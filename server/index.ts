import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createLocalServer } from './http.js';
import { createWorkerBackend } from './worker.js';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const port = Number(process.env.STATEMENTLENS_PORT ?? '4317');
if (!Number.isInteger(port) || port < 1 || port > 65535) {
  throw new Error('STATEMENTLENS_PORT must be an integer between 1 and 65535.');
}
const worker = createWorkerBackend({ rootDir, configPath: process.env.STATEMENTLENS_CONFIG });
const server = createLocalServer({ worker, port, distDir: path.join(rootDir, 'dist') });
server.on('error', (error: NodeJS.ErrnoException) => {
  console.error(error.code === 'EADDRINUSE'
    ? `Definograph port ${port} is already in use.`
    : `Definograph server failed: ${error.message}`);
  process.exitCode = 1;
});
server.listen(port, '127.0.0.1', () => {
  console.log(`Definograph local API: http://127.0.0.1:${port}`);
});

function shutdown() {
  worker.close?.();
  server.close();
  server.closeAllConnections();
}
process.once('SIGINT', shutdown);
process.once('SIGTERM', shutdown);
