import assert from 'node:assert/strict';
import { tmpdir } from 'node:os';
import { test } from 'node:test';
import { LeanSession } from './session.js';
import { WorkerError } from './worker.js';

const hasCode = (code: string) => (error: unknown) => error instanceof WorkerError && error.code === code;

function createSession(body = 'reply();', limits: { timeoutMs?: number; maxOutputBytes?: number; maxErrorBytes?: number } = {}) {
  const script = `
let count = 0;
require('node:readline').createInterface({input:process.stdin}).on('line', line => {
  const request = JSON.parse(line); count++;
  const result = {ok:true, requestId:request.requestId, source:request.source, pid:process.pid, count, diagnostics:[]};
  const reply = () => console.log(JSON.stringify(result));
  ${body}
});`;
  return new LeanSession({ executable: process.execPath, args: ['-e', script], cwd: tmpdir(), ...limits });
}

test('persistent transport reuses the process and matches distinct requests', async (t) => {
  const session = createSession();
  t.after(() => session.close());
  const first = await session.analyze('∀ (x : ℝ), x = x\n-- second source line');
  const second = await session.analyze('∃ (x : ℝ), x = 2');
  assert.equal(first.pid, second.pid);
  assert.equal(first.count, 1);
  assert.equal(second.count, 2);
  assert.notEqual(first.requestId, second.requestId);
  assert.equal(first.source, '∀ (x : ℝ), x = x\n-- second source line');
  assert.equal(second.source, '∃ (x : ℝ), x = 2');
});

test('persistent transport bounds concurrency without queuing sources', async (t) => {
  const session = createSession('setTimeout(reply, 30);');
  t.after(() => session.close());
  const first = session.analyze('first');
  await assert.rejects(session.analyze('second'), hasCode('WORKER_BUSY'));
  assert.equal((await first).count, 1);
  assert.equal((await session.analyze('third')).count, 2);
});

test('persistent transport preserves UTF-8 split across arbitrary stdout chunks', async (t) => {
  const session = createSession(`const bytes = Buffer.from(JSON.stringify(result) + '\\n');
    for (let offset = 0; offset < bytes.length; offset++) process.stdout.write(bytes.subarray(offset, offset + 1));`);
  t.after(() => session.close());
  const source = '∀ ε : ℝ, ε > 0';
  assert.equal((await session.analyze(source)).source, source);
});

test('timeout, abort, and unexpected exit recycle the process', async (t) => {
  const session = createSession(`
    if (request.source === 'hang') return;
    if (request.source === 'exit') process.exit(2);
    else reply();
  `, { timeoutMs: 200 });
  t.after(() => session.close());
  let previousPid = (await session.analyze('warm')).pid;
  await assert.rejects(session.analyze('hang'), hasCode('WORKER_TIMEOUT'));
  let recovered = await session.analyze('recover');
  assert.notEqual(recovered.pid, previousPid);
  previousPid = recovered.pid;
  const controller = new AbortController();
  const aborted = session.analyze('hang', controller.signal);
  controller.abort();
  await assert.rejects(aborted, hasCode('CANCELLED'));
  recovered = await session.analyze('recover');
  assert.notEqual(recovered.pid, previousPid);
  previousPid = recovered.pid;
  await assert.rejects(session.analyze('exit'), hasCode('WORKER_FAILED'));
  recovered = await session.analyze('recover');
  assert.notEqual(recovered.pid, previousPid);
});

test('invalid JSON, missing or incorrect IDs, and extra response lines are rejected and recycled', async (t) => {
  const session = createSession(`
    if (request.source === 'invalid') console.log('invalid-json');
    else if (request.source === 'missing') { delete result.requestId; reply(); }
    else if (request.source === 'mismatch') { result.requestId = 'old-request'; reply(); }
    else if (request.source === 'extra') process.stdout.write(JSON.stringify(result) + '\\n{}\\n');
    else reply();
  `);
  t.after(() => session.close());
  let lastPid = (await session.analyze('warm')).pid;
  for (const source of ['invalid', 'missing', 'mismatch', 'extra']) {
    await assert.rejects(session.analyze(source), hasCode('INVALID_WORKER_RESPONSE'));
    const recovered = await session.analyze('recover');
    assert.notEqual(recovered.pid, lastPid);
    lastPid = recovered.pid;
  }
});

test('a delayed previous response cannot satisfy the next pending request', async (t) => {
  const session = createSession(`
    if (request.source === 'late') { reply(); setTimeout(reply, 60); }
    else if (request.source === 'waiting') setTimeout(reply, 200);
    else reply();
  `);
  t.after(() => session.close());
  const first = await session.analyze('late');
  await assert.rejects(session.analyze('waiting'), hasCode('INVALID_WORKER_RESPONSE'));
  assert.notEqual((await session.analyze('recover')).pid, first.pid);
});

test('stdout and stderr bounds reset per request and recycle on excess', async (t) => {
  const session = createSession(`
    if (request.source === 'stdout') process.stdout.write('x'.repeat(2048));
    else if (request.source === 'stderr') { process.stderr.write('x'.repeat(2048)); }
    else reply();
  `, { maxOutputBytes: 1024, maxErrorBytes: 1024 });
  t.after(() => session.close());
  const first = await session.analyze('warm');
  for (let i = 0; i < 20; i++) assert.equal((await session.analyze('small')).pid, first.pid);
  for (const source of ['stdout', 'stderr']) {
    await assert.rejects(session.analyze(source), hasCode('WORKER_OUTPUT_LIMIT'));
    assert.equal((await session.analyze('recover')).count, 1);
  }
});

test('shutdown cancels pending work and prevents process resurrection', async () => {
  const session = createSession('setTimeout(reply, 1000);');
  const pending = session.analyze('pending');
  session.close();
  await assert.rejects(pending, hasCode('WORKER_CLOSED'));
  await assert.rejects(session.analyze('after shutdown'), hasCode('WORKER_CLOSED'));
});
