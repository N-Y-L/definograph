import { capabilities, type AnalysisRequest } from '../src/protocol.js';
import { createServer, type IncomingMessage, type ServerResponse } from 'node:http';
import { readFile, realpath, stat } from 'node:fs/promises';
import path from 'node:path';
import { MAX_SOURCE_BYTES, MAX_SOURCE_CHARACTERS, WorkerError, type WorkerBackend } from './worker.js';

const MIME: Record<string, string> = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8', '.json': 'application/json; charset=utf-8',
  '.svg': 'image/svg+xml', '.png': 'image/png', '.ico': 'image/x-icon', '.woff2': 'font/woff2', '.woff': 'font/woff', '.ttf': 'font/ttf',
};

function sendJSON(response: ServerResponse, status: number, data: unknown): void {
  if (response.destroyed || response.writableEnded) return;
  const body = JSON.stringify(data);
  response.writeHead(status, {
    'Content-Type': 'application/json; charset=utf-8',
    'Content-Length': Buffer.byteLength(body),
    'Cache-Control': 'no-store',
    'X-Content-Type-Options': 'nosniff',
  });
  response.end(body);
}

function sendError(response: ServerResponse, status: number, code: string, message: string): void {
  sendJSON(response, status, { ok: false, error: message, code, diagnostics: [{ severity: 'error', message }] });
}

async function readSource(request: IncomingMessage): Promise<AnalysisRequest> {
  if (request.headers['content-encoding'] && request.headers['content-encoding'] !== 'identity') {
    request.resume();
    throw new WorkerError('UNSUPPORTED_ENCODING', 'Compressed requests are not supported.', 415);
  }
  const contentType = request.headers['content-type']?.split(';', 1)[0]?.trim().toLowerCase();
  if (contentType !== 'application/json') {
    request.resume();
    throw new WorkerError('INVALID_CONTENT_TYPE', 'Use application/json.', 415);
  }
  const limit = 256 * 1024; // Allows JSON escaping while source itself has the tighter limit below.
  const declaredLength = Number(request.headers['content-length']);
  if (Number.isFinite(declaredLength) && declaredLength > limit) {
    request.resume();
    throw new WorkerError('BODY_TOO_LARGE', 'The request body is too large.', 413);
  }
  const data = await new Promise<Buffer>((resolve, reject) => {
    let size = 0;
    const chunks: Buffer[] = [];
    const cleanup = () => {
      request.off('data', onData);
      request.off('end', onEnd);
      request.off('aborted', onAborted);
    };
    const onError = (error: Error) => { cleanup(); reject(error); };
    const onAborted = () => onError(new WorkerError('CANCELLED', 'The request was interrupted.', 400));
    const onEnd = () => { cleanup(); resolve(Buffer.concat(chunks)); };
    const onData = (part: Buffer) => {
      size += part.length;
      if (size > limit) {
        cleanup();
        // Drain without retaining an oversized chunked body so a structured 413 can still be sent.
        request.resume();
        reject(new WorkerError('BODY_TOO_LARGE', 'The request body is too large.', 413));
      } else chunks.push(part);
    };
    request.on('data', onData);
    request.once('end', onEnd);
    request.once('error', onError);
    request.once('aborted', onAborted);
  });
  let body: unknown;
  try {
    body = JSON.parse(data.toString('utf8'));
  } catch {
    throw new WorkerError('INVALID_JSON', 'The request body must be valid JSON.', 400);
  }
  if (!body || typeof body !== 'object' || Array.isArray(body) || typeof (body as { source?: unknown }).source !== 'string') {
    throw new WorkerError('INVALID_SOURCE', 'Provide a JSON object with a source string.', 400);
  }
  const source = (body as { source: string }).source;
  if (!source.trim() || source.length > MAX_SOURCE_CHARACTERS || Buffer.byteLength(source) > MAX_SOURCE_BYTES) {
    throw new WorkerError('INVALID_SOURCE', 'Provide a nonempty Lean statement of at most 32,768 characters and 65,536 bytes.', 400);
  }
  const input = body as Record<string, unknown>;
  if (Object.keys(input).some(key => !['source', 'inputMode', 'expansion', 'previewDefinitions'].includes(key))) {
    throw new WorkerError('INVALID_OPTIONS', 'Unknown analysis option.', 400);
  }
  const result: AnalysisRequest = { source };
  if (input.inputMode !== undefined) {
    if (input.inputMode !== 'term' && input.inputMode !== 'declaration') throw new WorkerError('INVALID_OPTIONS', 'inputMode must be term or declaration.', 400);
    result.inputMode = input.inputMode;
  }
  if (input.previewDefinitions !== undefined) {
    if (typeof input.previewDefinitions !== 'boolean') throw new WorkerError('INVALID_OPTIONS', 'previewDefinitions must be boolean.', 400);
    result.previewDefinitions = input.previewDefinitions;
  }
  if (input.expansion !== undefined) {
    const expansion = input.expansion as Record<string, unknown>;
    if (!expansion || typeof expansion !== 'object' || Array.isArray(expansion) ||
        Object.keys(expansion).some(key => !['constants', 'maxDepth'].includes(key)) ||
        !Array.isArray(expansion.constants) || expansion.constants.length > 12 ||
        !expansion.constants.every(name => typeof name === 'string' && name.length > 0 && name.length <= 512 && !/[\r\n\0]/.test(name)) ||
        !Number.isInteger(expansion.maxDepth) || Number(expansion.maxDepth) < 1 || Number(expansion.maxDepth) > 3) {
      throw new WorkerError('INVALID_OPTIONS', 'Expansion needs up to 12 constant names and maxDepth from 1 to 3.', 400);
    }
    result.expansion = { constants: [...new Set(expansion.constants as string[])], maxDepth: Number(expansion.maxDepth) };
  }
  return result;
}

/** Resolve within dist, including symlinks. No local project files can be served. */
export async function resolveStaticFile(distDir: string, urlPath: string): Promise<string | null> {
  let decoded: string;
  try { decoded = decodeURIComponent(urlPath); } catch { return null; }
  if (decoded.includes('\0') || decoded.includes('\\') || decoded.split('/').includes('..')) return null;
  const requested = path.resolve(distDir, `.${decoded.startsWith('/') ? decoded : `/${decoded}`}`);
  const within = (root: string, candidate: string) => candidate === root || candidate.startsWith(`${root}${path.sep}`);
  if (!within(path.resolve(distDir), requested)) return null;
  try {
    const root = await realpath(distDir);
    let candidate = requested;
    try {
      if ((await stat(candidate)).isDirectory()) candidate = path.join(candidate, 'index.html');
    } catch {
      if (path.extname(decoded)) return null;
      candidate = path.join(distDir, 'index.html');
    }
    const resolved = await realpath(candidate);
    if (!within(root, resolved) || !(await stat(resolved)).isFile()) return null;
    return resolved;
  } catch {
    return null;
  }
}

export function createLocalServer(options: { worker: WorkerBackend; port?: number; distDir?: string }) {
  const port = options.port ?? 4317;
  let analyzing = false;
  const server = createServer((request, response) => {
    void handle(request, response).catch((error: unknown) => {
      if (error instanceof WorkerError) sendError(response, error.status, error.code, error.message);
      else sendError(response, 500, 'INTERNAL_ERROR', 'The local server could not complete this request.');
    });
  });
  // Bound slow or incomplete requests even though this is a loopback service.
  server.requestTimeout = 15_000;
  server.headersTimeout = 10_000;
  server.keepAliveTimeout = 5_000;
  const handle = async (request: IncomingMessage, response: ServerResponse): Promise<void> => {
    const address = server.address();
    const actualPort = address && typeof address !== 'string' ? address.port : port;
    const hosts = new Set([`127.0.0.1:${actualPort}`, `localhost:${actualPort}`]);
    if (!hosts.has(request.headers.host ?? '')) {
      request.resume();
      sendError(response, 403, 'FORBIDDEN_HOST', 'Only the local StatementLens address is allowed.');
      return;
    }
    const origins = new Set([
      `http://127.0.0.1:${actualPort}`, `http://localhost:${actualPort}`,
      'http://127.0.0.1:5173', 'http://localhost:5173',
    ]);
    const origin = request.headers.origin;
    if ((origin && !origins.has(origin)) || (!origin && request.headers['sec-fetch-site'] === 'cross-site')) {
      request.resume();
      sendError(response, 403, 'FORBIDDEN_ORIGIN', 'Only the local StatementLens app may use this service.');
      return;
    }
    if (origin) {
      response.setHeader('Access-Control-Allow-Origin', origin);
      response.setHeader('Vary', 'Origin');
    }
    response.setHeader('X-Frame-Options', 'DENY');
    response.setHeader('Referrer-Policy', 'no-referrer');
    const url = new URL(request.url ?? '/', `http://127.0.0.1:${actualPort}`);
    if (request.method === 'OPTIONS' && url.pathname.startsWith('/api/')) {
      response.writeHead(204, {
        'Access-Control-Allow-Methods': 'GET, POST, OPTIONS',
        'Access-Control-Allow-Headers': 'Content-Type',
        'Access-Control-Max-Age': '600',
      });
      response.end();
      return;
    }
    if (url.pathname === '/api/capabilities' && request.method === 'GET') {
      sendJSON(response, 200, capabilities);
      return;
    }
    if (url.pathname === '/api/health' && request.method === 'GET') {
      sendJSON(response, 200, await options.worker.health());
      return;
    }
    if (url.pathname === '/api/analyze' && request.method === 'POST') {
      if (analyzing) {
        request.resume();
        response.setHeader('Retry-After', '1');
        sendError(response, 429, 'WORKER_BUSY', 'Lean is analyzing another statement. Try again when it finishes.');
        return;
      }
      analyzing = true;
      const controller = new AbortController();
      const cancel = () => { if (!response.writableEnded) controller.abort(); };
      response.once('close', cancel);
      try {
        const { source, ...analysisOptions } = await readSource(request);
        sendJSON(response, 200, await options.worker.analyze(source, controller.signal, analysisOptions));
      } finally {
        analyzing = false;
        response.off('close', cancel);
      }
      return;
    }
    if (url.pathname.startsWith('/api/')) {
      sendError(response, 404, 'NOT_FOUND', 'The requested API route does not exist.');
      return;
    }
    if ((request.method === 'GET' || request.method === 'HEAD') && options.distDir) {
      const file = await resolveStaticFile(options.distDir, url.pathname);
      if (file) {
        const contents = await readFile(file);
        response.writeHead(200, {
          'Content-Type': MIME[path.extname(file)] ?? 'application/octet-stream',
          'Content-Length': contents.length,
          'Cache-Control': path.basename(file) === 'index.html' ? 'no-cache' : 'public, max-age=3600',
          'X-Content-Type-Options': 'nosniff',
          'Content-Security-Policy': "default-src 'self'; script-src 'self'; style-src 'self' 'unsafe-inline'; img-src 'self' data:; connect-src 'self'; font-src 'self'; object-src 'none'; base-uri 'self'; frame-ancestors 'none'",
        });
        response.end(request.method === 'HEAD' ? undefined : contents);
        return;
      }
    }
    sendError(response, 404, 'NOT_FOUND', 'Start the frontend with npm run dev, or build it with npm run build.');
  };
  return server;
}
