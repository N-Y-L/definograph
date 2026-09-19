import assert from 'node:assert/strict';
import { request as httpRequest, type Server } from 'node:http';
import { once } from 'node:events';
import { mkdtemp, mkdir, readFile, rm, symlink, writeFile } from 'node:fs/promises';
import { tmpdir } from 'node:os';
import path from 'node:path';
import { test } from 'node:test';
import { createLocalServer, resolveStaticFile } from './http.js';
import { WorkerError, type WorkerBackend } from './worker.js';

const healthy: WorkerBackend = {
  health: async () => ({ ok: true, ready: true, leanVersion: 'Lean (version 4.28.0, test)', issue: null }),
  analyze: async (source) => ({ ok: true, source, diagnostics: [], tree: {} }),
};

async function withServer(run: (url: string, server: Server) => Promise<void>, worker = healthy, distDir?: string) {
  const server = createLocalServer({ worker, port: 0, distDir });
  server.listen(0, '127.0.0.1');
  await once(server, 'listening');
  const address = server.address();
  assert.ok(address && typeof address !== 'string');
  try {
    await run(`http://127.0.0.1:${address.port}`, server);
  } finally {
    server.closeAllConnections();
    await new Promise<void>((resolve, reject) => server.close((error) => error ? reject(error) : resolve()));
  }
}

const post = (url: string, body: unknown, headers: Record<string, string> = {}) => fetch(`${url}/api/analyze`, {
  method: 'POST', headers: { 'Content-Type': 'application/json', ...headers }, body: JSON.stringify(body),
});

test('health reports the actual backend state; valid source is forwarded without rewriting', async () => {
  await withServer(async (url) => {
    const health = await fetch(`${url}/api/health`);
    assert.equal(health.status, 200);
    assert.equal((await health.json()).leanVersion, 'Lean (version 4.28.0, test)');
    const source = '∀ (x : ℝ), x < 2 → x < 3';
    const analyzed = await post(url, { source });
    assert.equal(analyzed.status, 200);
    assert.equal((await analyzed.json()).source, source);
  });
});

test('rejects remote, opaque, and suffix-confused origins and DNS rebinding hosts', async () => {
  let calls = 0;
  await withServer(async (url) => {
    for (const origin of ['https://example.org', 'null', 'http://localhost:5173.evil.test', 'http://localhost:51730']) {
      const result = await post(url, { source: 'True' }, { Origin: origin });
      assert.equal(result.status, 403, origin);
      assert.equal((await result.json()).code, 'FORBIDDEN_ORIGIN');
    }
    // Node's fetch sanitizes Host, so use the low-level client to exercise rebinding.
    const result = await new Promise<{ status: number; body: string }>((resolve, reject) => {
      const request = httpRequest(`${url}/api/analyze`, {
        method: 'POST', headers: { Host: 'attacker.test', 'Content-Type': 'application/json' },
      }, (response) => {
        let body = '';
        response.setEncoding('utf8');
        response.on('data', (part) => { body += part; });
        response.on('end', () => resolve({ status: response.statusCode!, body }));
      });
      request.on('error', reject);
      request.end(JSON.stringify({ source: 'True' }));
    });
    assert.equal(result.status, 403);
    assert.equal(JSON.parse(result.body).code, 'FORBIDDEN_HOST');
    const crossSite = await fetch(`${url}/api/health`, { headers: { 'Sec-Fetch-Site': 'cross-site' } });
    assert.equal(crossSite.status, 403);
  }, { ...healthy, analyze: async () => { calls++; return { ok: true, diagnostics: [] }; } });
  assert.equal(calls, 0);
});

test('permits the explicit local frontend origins and returns narrow preflight headers', async () => {
  await withServer(async (url) => {
    for (const origin of ['http://localhost:5173', 'http://127.0.0.1:5173', url]) {
      const result = await post(url, { source: 'True' }, { Origin: origin });
      assert.equal(result.status, 200);
      assert.equal(result.headers.get('access-control-allow-origin'), origin);
    }
    const preflight = await fetch(`${url}/api/analyze`, { method: 'OPTIONS', headers: { Origin: 'http://localhost:5173' } });
    assert.equal(preflight.status, 204);
    assert.equal(preflight.headers.get('access-control-allow-headers'), 'Content-Type');
    assert.equal(preflight.headers.get('access-control-allow-credentials'), null);
  });
});

test('validates request encoding, JSON, source type, emptiness, and size before analysis', async () => {
  let calls = 0;
  await withServer(async (url) => {
    for (const body of [null, [], {}, { source: 2 }, { source: '  ' }, { source: 'x'.repeat(32_769) }, { source: '∀'.repeat(22_000) }]) {
      assert.equal((await post(url, body)).status, 400);
    }
    const invalidJSON = await fetch(`${url}/api/analyze`, { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: '{' });
    assert.equal(invalidJSON.status, 400);
    const wrongContent = await fetch(`${url}/api/analyze`, { method: 'POST', body: 'True' });
    assert.equal(wrongContent.status, 415);
    const encoded = await post(url, { source: 'True' }, { 'Content-Encoding': 'gzip' });
    assert.equal(encoded.status, 415);
    const hugeBody = await post(url, { source: 'x'.repeat(300_000) });
    assert.equal(hugeBody.status, 413);
  }, { ...healthy, analyze: async () => { calls++; return { ok: true, diagnostics: [] }; } });
  assert.equal(calls, 0);
});

test('returns domain diagnostics unchanged and process errors as explicit service errors', async () => {
  const diagnostic = { ok: false, error: 'unknown identifier', diagnostics: [{ severity: 'error', message: 'unknown identifier' }] };
  await withServer(async (url) => {
    const response = await post(url, { source: 'missingName' });
    assert.equal(response.status, 200);
    assert.deepEqual(await response.json(), diagnostic);
  }, { ...healthy, analyze: async () => diagnostic });
  await withServer(async (url) => {
    const response = await post(url, { source: 'True' });
    assert.equal(response.status, 504);
    assert.equal((await response.json()).code, 'WORKER_TIMEOUT');
  }, { ...healthy, analyze: async () => { throw new WorkerError('WORKER_TIMEOUT', 'Timed out.', 504); } });
});

test('oversized chunked bodies receive a structured 413 without launching Lean', async () => {
  let calls = 0;
  await withServer(async (url) => {
    const response = await new Promise<{ status: number; body: string }>((resolve, reject) => {
      const request = httpRequest(`${url}/api/analyze`, {
        method: 'POST', headers: { 'Content-Type': 'application/json', 'Transfer-Encoding': 'chunked' },
      }, (response) => {
        let body = '';
        response.setEncoding('utf8');
        response.on('data', (part) => { body += part; });
        response.on('end', () => resolve({ status: response.statusCode!, body }));
      });
      request.on('error', reject);
      request.write('{"source":"');
      for (let i = 0; i < 5; i++) request.write('x'.repeat(65_536));
      request.end('"}');
    });
    assert.equal(response.status, 413);
    assert.equal(JSON.parse(response.body).code, 'BODY_TOO_LARGE');
  }, { ...healthy, analyze: async () => { calls++; return { ok: true, diagnostics: [] }; } });
  assert.equal(calls, 0);
});

test('bounds concurrent work and releases the slot after completion and failure', async () => {
  let release: (() => void) | undefined;
  let entered: (() => void) | undefined;
  const started = new Promise<void>((resolve) => { entered = resolve; });
  let calls = 0;
  await withServer(async (url) => {
    const first = post(url, { source: 'True' });
    await started;
    const second = await post(url, { source: 'True' });
    assert.equal(second.status, 429);
    assert.equal(second.headers.get('retry-after'), '1');
    assert.equal(calls, 1);
    release!();
    assert.equal((await first).status, 200);
    assert.equal((await post(url, { source: 'True' })).status, 502);
    assert.equal((await post(url, { source: 'True' })).status, 200);
  }, {
    ...healthy,
    analyze: async () => {
      calls++;
      if (calls === 1) { entered!(); await new Promise<void>((resolve) => { release = resolve; }); }
      if (calls === 2) throw new WorkerError('WORKER_FAILED', 'Failed.');
      return { ok: true, diagnostics: [] };
    },
  });
});

test('client disconnect aborts the in-flight worker', async () => {
  let started: (() => void) | undefined;
  const begin = new Promise<void>((resolve) => { started = resolve; });
  let observedAbort: (() => void) | undefined;
  const aborted = new Promise<void>((resolve) => { observedAbort = resolve; });
  await withServer(async (url) => {
    const request = httpRequest(`${url}/api/analyze`, { method: 'POST', headers: { 'Content-Type': 'application/json' } });
    request.on('error', () => undefined);
    request.end(JSON.stringify({ source: 'True' }));
    await begin;
    request.destroy();
    await aborted;
  }, {
    ...healthy,
    analyze: async (_source, signal) => {
      started!();
      return new Promise((_resolve, reject) => signal!.addEventListener('abort', () => {
        observedAbort!();
        reject(new WorkerError('CANCELLED', 'Cancelled.', 499));
      }, { once: true }));
    },
  });
});

test('static files stay within dist, including encoded traversal and symlinks', async () => {
  const root = await mkdtemp(path.join(tmpdir(), 'statementlens-static-'));
  const dist = path.join(root, 'dist');
  try {
    await mkdir(dist);
    await writeFile(path.join(dist, 'index.html'), '<h1>StatementLens</h1>');
    await writeFile(path.join(root, 'private.txt'), 'private');
    await symlink(path.join(root, 'private.txt'), path.join(dist, 'linked.txt'));
    for (const route of ['/../private.txt', '/%2e%2e/private.txt', '/%2e%2e%2fprivate.txt', '/linked.txt', '/bad%00.txt', '/%ZZ']) {
      assert.equal(await resolveStaticFile(dist, route), null, route);
    }
    const appFile = await resolveStaticFile(dist, '/statement/123');
    assert.ok(appFile);
    assert.equal(await readFile(appFile, 'utf8'), '<h1>StatementLens</h1>');
    await withServer(async (url) => {
      const response = await fetch(url);
      assert.equal(response.status, 200);
      assert.match(response.headers.get('content-security-policy')!, /frame-ancestors 'none'/);
      assert.equal(await response.text(), '<h1>StatementLens</h1>');
      assert.equal((await fetch(`${url}/linked.txt`)).status, 404);
      assert.equal((await fetch(`${url}/api/unknown`)).status, 404);
    }, healthy, dist);
  } finally {
    await rm(root, { recursive: true, force: true });
  }
});
