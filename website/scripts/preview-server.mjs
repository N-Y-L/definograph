// Local preview of dist/ that follows the hosting rules the site relies on:
// auto-trailing-slash HTML handling, the 404 page with status 404 for anything
// missing (no single-page fallback), and the response headers in dist/_headers.
// It is a stand-in for local review, not a production server.
import http from 'node:http';
import { readFile, readdir, stat } from 'node:fs/promises';
import path from 'node:path';
import { headersFor, parseHeaders, parseRedirects } from './headers.mjs';

const TYPES = new Map([
  ['.html', 'text/html; charset=utf-8'],
  ['.css', 'text/css; charset=utf-8'],
  ['.svg', 'image/svg+xml'],
  ['.png', 'image/png'],
  ['.txt', 'text/plain; charset=utf-8'],
  ['.md', 'text/markdown; charset=utf-8'],
  ['.xml', 'application/xml'],
]);
const DEFAULT_CACHE = 'public, max-age=0, must-revalidate';

// The host matches asset paths case-sensitively. On a case-insensitive disk, stat() alone
// would also find /Learn/ or /FAVICON.SVG, so every segment's exact spelling is confirmed.
async function isFile(distDir, file) {
  try {
    if (!(await stat(file)).isFile()) return false;
    let dir = distDir;
    for (const segment of path.relative(distDir, file).split(path.sep)) {
      if (!(await readdir(dir)).includes(segment)) return false;
      dir = path.join(dir, segment);
    }
    return true;
  } catch {
    return false;
  }
}

// Maps a decoded URL path to { status, file } or { status, location }.
export async function resolveRequest(distDir, pathname) {
  const notFound = { status: 404, file: path.join(distDir, '404.html') };
  const segments = pathname.split('/');
  if (
    !pathname.startsWith('/') ||
    pathname.includes('\0') ||
    pathname.includes('\\') ||
    segments.some((segment) => segment.startsWith('.')) ||
    pathname === '/_headers' ||
    pathname === '/_redirects'
  ) {
    return notFound;
  }
  // Redirect rules come first, as on the host; they only name retired paths.
  const redirects = await readFile(path.join(distDir, '_redirects'), 'utf8').then(parseRedirects, () => []);
  const rule = redirects.find((candidate) => candidate.from === pathname);
  if (rule) return { status: rule.status, location: rule.to };
  const fileFor = (p) => path.join(distDir, ...p.split('/').filter(Boolean));

  if (pathname.endsWith('/index.html')) {
    return (await isFile(distDir, fileFor(pathname))) ? { status: 307, location: pathname.slice(0, -'index.html'.length) } : notFound;
  }
  if (pathname.endsWith('.html')) {
    return (await isFile(distDir, fileFor(pathname))) ? { status: 307, location: pathname.slice(0, -'.html'.length) } : notFound;
  }
  if (pathname.endsWith('/')) {
    if (await isFile(distDir, fileFor(`${pathname}index.html`))) return { status: 200, file: fileFor(`${pathname}index.html`) };
    if (pathname !== '/' && (await isFile(distDir, fileFor(`${pathname.slice(0, -1)}.html`)))) {
      return { status: 307, location: pathname.slice(0, -1) };
    }
    return notFound;
  }
  if (await isFile(distDir, fileFor(pathname))) return { status: 200, file: fileFor(pathname) };
  if (await isFile(distDir, fileFor(`${pathname}/index.html`))) return { status: 307, location: `${pathname}/` };
  if (await isFile(distDir, fileFor(`${pathname}.html`))) return { status: 200, file: fileFor(`${pathname}.html`) };
  return notFound;
}

async function serve(distDir, req, res) {
  if (req.method !== 'GET' && req.method !== 'HEAD') {
    res.writeHead(405, { Allow: 'GET, HEAD', 'Content-Type': 'text/plain; charset=utf-8' });
    res.end('Method not allowed\n');
    return 405;
  }
  const url = new URL(req.url ?? '/', 'http://127.0.0.1');
  let pathname = null;
  try {
    pathname = decodeURIComponent(url.pathname);
  } catch {
    // Malformed percent-encoding: treat as missing.
  }
  const result = pathname === null
    ? { status: 404, file: path.join(distDir, '404.html') }
    : await resolveRequest(distDir, pathname);

  res.setHeader('Cache-Control', DEFAULT_CACHE);
  if (result.location) {
    res.setHeader('Location', `${result.location}${url.search}`);
    res.writeHead(result.status);
    res.end();
    return result.status;
  }

  const body = await readFile(result.file);
  res.setHeader('Content-Type', TYPES.get(path.extname(result.file)) ?? 'application/octet-stream');
  res.setHeader('Content-Length', body.length);
  const rules = parseHeaders(await readFile(path.join(distDir, '_headers'), 'utf8'));
  for (const { name, value } of headersFor(rules, url.pathname).values()) res.setHeader(name, value);
  res.writeHead(result.status);
  res.end(req.method === 'HEAD' ? undefined : body);
  return result.status;
}

export function createPreviewServer(distDir, { log } = {}) {
  return http.createServer((req, res) => {
    serve(distDir, req, res)
      .then((status) => log?.(`${status} ${req.method} ${req.url}`))
      .catch((error) => {
        if (!res.headersSent) res.writeHead(500, { 'Content-Type': 'text/plain; charset=utf-8' });
        res.end('Preview server error\n');
        log?.(`500 ${req.method} ${req.url}: ${error.message}`);
      });
  });
}
