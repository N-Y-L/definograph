// npm run dev: build, serve dist/ at http://127.0.0.1:4173/ and rebuild when inputs change.
// npm run preview: the same with a preview build in dist-preview/, where recorded figures that
// are not available yet appear as visible placeholders (never for release).
// Serves only on the loopback interface and never opens a browser.
import { watch } from 'node:fs';
import path from 'node:path';
import { PREVIEW_DIST, build } from './build.mjs';
import { createPreviewServer } from './preview-server.mjs';
import { DIST, ROOT } from './site.mjs';

const preview = process.argv.includes('--preview');
const OUT = preview ? PREVIEW_DIST : DIST;

const HOST = '127.0.0.1';
const PORT = 4173;
const WATCHED = ['content', 'templates', 'source-assets', 'tutorial'];

try {
  await build({ preview });
} catch (error) {
  console.error(`Build failed: ${error.message}`);
  process.exit(1);
}

const server = createPreviewServer(OUT, { log: (line) => console.log(line) });
server.on('error', (error) => {
  console.error(error.code === 'EADDRINUSE' ? `Port ${PORT} on ${HOST} is already in use.` : error.message);
  process.exit(1);
});
server.listen(PORT, HOST, () => {
  console.log(`${preview ? 'Preview build (placeholders, not for release)' : 'Preview'}: http://${HOST}:${PORT}/ (Ctrl+C to stop)`);
  console.log(`Rebuilding when ${WATCHED.join(', ')} change. Restart after editing scripts/.`);
});

let timer = null;
let building = false;
let pending = false;

async function rebuild() {
  if (building) {
    pending = true;
    return;
  }
  building = true;
  try {
    const { files } = await build({ preview });
    console.log(`Rebuilt ${files.length} files.`);
  } catch (error) {
    console.error(`Build failed, keeping the previous dist/: ${error.message}`);
  } finally {
    building = false;
    if (pending) {
      pending = false;
      schedule();
    }
  }
}

function schedule() {
  clearTimeout(timer);
  timer = setTimeout(rebuild, 150);
}

const watchers = WATCHED.map((dir) => watch(path.join(ROOT, dir), { recursive: true }, schedule));

function stop() {
  for (const watcher of watchers) watcher.close();
  clearTimeout(timer);
  server.close(() => process.exit(0));
  server.closeAllConnections?.();
  setTimeout(() => process.exit(0), 500).unref();
}
process.on('SIGINT', stop);
process.on('SIGTERM', stop);
