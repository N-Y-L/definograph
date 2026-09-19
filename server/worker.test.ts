import assert from 'node:assert/strict';
import { chmod, mkdtemp, mkdir, rm, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { ConfigError, loadWorkerConfig } from './config.js';
import { createWorkerBackend, runBoundedProcess, WorkerError } from './worker.js';

function hasCode(code: string) {
  return (error: unknown) => error instanceof WorkerError && error.code === code;
}

test('process runner transports source through stdin without shell evaluation', async () => {
  const source = '$(touch /tmp/statementlens-injection)\n`uname`\n∀ x, x = x';
  const output = await runBoundedProcess(process.execPath, {
    args: ['-e', "process.stdin.setEncoding('utf8'); process.stdin.on('data', s => process.stdout.write(s));"],
    input: `${JSON.stringify({ source })}\n`, cwd: tmpdir(),
  });
  assert.equal(JSON.parse(output).source, source);
});

test('process runner kills timed-out work and rejects oversized stdout and stderr', async () => {
  await assert.rejects(runBoundedProcess(process.execPath, {
    args: ['-e', 'setInterval(() => {}, 1000)'], cwd: tmpdir(), timeoutMs: 80,
  }), hasCode('WORKER_TIMEOUT'));
  await assert.rejects(runBoundedProcess(process.execPath, {
    args: ['-e', "process.stdout.write('x'.repeat(10000));"], cwd: tmpdir(), maxOutputBytes: 128,
  }), hasCode('WORKER_OUTPUT_LIMIT'));
  await assert.rejects(runBoundedProcess(process.execPath, {
    args: ['-e', "process.stderr.write('x'.repeat(10000));"], cwd: tmpdir(), maxErrorBytes: 128,
  }), hasCode('WORKER_OUTPUT_LIMIT'));
});

test('process runner handles cancellation, failed starts, and unsuccessful exits', async () => {
  const controller = new AbortController();
  const processResult = runBoundedProcess(process.execPath, {
    args: ['-e', 'setInterval(() => {}, 1000)'], cwd: tmpdir(), signal: controller.signal,
  });
  controller.abort();
  await assert.rejects(processResult, hasCode('CANCELLED'));
  await assert.rejects(runBoundedProcess(process.execPath, { cwd: tmpdir(), signal: controller.signal }), hasCode('CANCELLED'));
  await assert.rejects(runBoundedProcess('/not/a/real/statementlens-worker', { cwd: tmpdir() }), hasCode('WORKER_UNAVAILABLE'));
  await assert.rejects(runBoundedProcess(process.execPath, {
    args: ['-e', 'process.exit(2)'], cwd: tmpdir(),
  }), hasCode('WORKER_FAILED'));
});

async function fixture(workerBody: string, run: (root: string, configPath: string) => Promise<void>) {
  const root = await mkdtemp(path.join(tmpdir(), 'statementlens-worker-'));
  try {
    await mkdir(path.join(root, 'lib'));
    const leanExecutable = path.join(root, 'lean');
    const workerExecutable = path.join(root, 'worker');
    await writeFile(leanExecutable, `#!${process.execPath}\nconsole.log('Lean (version 4.28.0, test)');\n`);
    await writeFile(workerExecutable, `#!${process.execPath}\n${workerBody}\n`);
    await chmod(leanExecutable, 0o700);
    await chmod(workerExecutable, 0o700);
    const configPath = path.join(root, 'config.json');
    await writeFile(configPath, JSON.stringify({
      leanExecutable, workerExecutable, leanPath: [path.join(root, 'lib')], leanSysroot: root,
    }));
    await run(root, configPath);
  } finally {
    await rm(root, { recursive: true, force: true });
  }
}

test('backend uses configured executable and read paths, and reports executable version', async () => {
  await fixture(`
require('node:readline').createInterface({input: process.stdin}).on('line', line => {
  const input = JSON.parse(line);
  console.log(JSON.stringify({ok:true, requestId:input.requestId, source:input.source,
    paths:process.env.LEAN_PATH, sysroot:process.env.STATEMENTLENS_LEAN_SYSROOT, diagnostics:[]}));
});
`, async (root, configPath) => {
    const backend = createWorkerBackend({ rootDir: root, configPath });
    try {
      assert.deepEqual(await backend.health(), { ok: true, ready: true, leanVersion: 'Lean (version 4.28.0, test)', issue: null });
      const result = await backend.analyze('∀ n : Nat, n = n');
      assert.equal(result.source, '∀ n : Nat, n = n');
      const config = await loadWorkerConfig(configPath);
      assert.equal(result.paths, config.leanPath.join(path.delimiter));
      assert.equal(result.sysroot, config.leanSysroot);
    } finally {
      backend.close?.();
    }
  });
});

test('backend reloads a replaced executable and prevents work after shutdown', async () => {
  const script = (label: string) => `require('node:readline').createInterface({input:process.stdin}).on('line', line => {
    const input = JSON.parse(line); console.log(JSON.stringify({ok:true, requestId:input.requestId,
      label:${JSON.stringify(label)}, pid:process.pid, diagnostics:[]}));
  });`;
  await fixture(script('before'), async (root, configPath) => {
    const backend = createWorkerBackend({ rootDir: root, configPath });
    try {
      const first = await backend.analyze('True');
      assert.equal(first.label, 'before');
      const config = await loadWorkerConfig(configPath);
      await writeFile(config.workerExecutable, `#!${process.execPath}\n${script('after replacement')}\n`);
      const second = await backend.analyze('True');
      assert.equal(second.label, 'after replacement');
      assert.notEqual(first.pid, second.pid);
      backend.close?.();
      await assert.rejects(backend.analyze('True'), hasCode('WORKER_CLOSED'));
    } finally { backend.close?.(); }
  });
});

test('backend rejects malformed and incomplete worker responses', async () => {
  for (const body of ["console.log('not json')", "console.log('{}')", "console.log('{\"ok\":true}')", "console.log('[]')"]) {
    await fixture(body, async (root, configPath) => {
      await assert.rejects(createWorkerBackend({ rootDir: root, configPath }).analyze('True'), hasCode('INVALID_WORKER_RESPONSE'));
    });
  }
});

test('missing setup is a recoverable health state and explicit unavailable response', async () => {
  const root = await mkdtemp(path.join(tmpdir(), 'statementlens-unconfigured-'));
  try {
    const backend = createWorkerBackend({ rootDir: root });
    const health = await backend.health();
    assert.equal(health.ready, false);
    assert.equal(health.leanVersion, null);
    assert.match(health.issue!, /setup:lean/);
    await assert.rejects(backend.analyze('True'), hasCode('WORKER_UNAVAILABLE'));
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});

test('configuration requires absolute executable and library paths', async () => {
  await fixture("console.log('{}')", async (root, configPath) => {
    const valid = await loadWorkerConfig(configPath);
    for (const config of [
      { ...valid, leanExecutable: 'lean' },
      { ...valid, workerExecutable: root },
      { ...valid, leanPath: [] },
      { ...valid, leanPath: ['../mathlib'] },
      { ...valid, leanSysroot: '/nonexistent-statementlens-sysroot' },
      [],
    ]) {
      await writeFile(configPath, JSON.stringify(config));
      await assert.rejects(loadWorkerConfig(configPath), ConfigError);
    }
  });
});
