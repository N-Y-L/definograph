import { createHash } from 'node:crypto';
import { createReadStream } from 'node:fs';
import { stat } from 'node:fs/promises';
import { WorkerError } from './protocol.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';

const sha = (v: unknown): v is string => typeof v === 'string' && /^[a-f0-9]{64}$/.test(v);
function canonical(v: unknown): string {
  if (Array.isArray(v)) return '[' + v.map(canonical).join(',') + ']';
  if (v !== null && typeof v === 'object') return '{' + Object.entries(v).sort(([a], [b]) => a < b ? -1 : a > b ? 1 : 0).map(([k, x]) => JSON.stringify(k) + ':' + canonical(x)).join(',') + '}';
  return JSON.stringify(v);
}
export async function hashContextExecutable(file: string): Promise<string> {
  const info = await stat(file);
  if (!info.isFile() || info.size > 512 * 1024 * 1024) throw new WorkerError('EDITOR_CONFIG', 'The context executable is unavailable or exceeds the build limit.');
  const hash = createHash('sha256');
  for await (const bytes of createReadStream(file)) hash.update(bytes);
  return hash.digest('hex');
}

/** Verify the installed native build record, without loading its build libraries
 * into the user's elaboration environment. This is consistency, not attestation. */
export function sourceCaptureEngine(config: Record<string, unknown>, contextSha256: string): SourceSnapshotOrigin['engine'] | undefined {
  if (config.sourceCapture === undefined) return undefined; // Compatible legacy engine.
  const v = config.sourceCapture;
  if (!v || typeof v !== 'object' || Array.isArray(v)) throw new WorkerError('EDITOR_CONFIG', 'Invalid source capture build record. Rebuild the Lean engine.');
  const pins = v as Record<string, unknown>;
  const { buildFingerprint, libraryPath: _libraryPath, ...fields } = pins;
  if (!sha(buildFingerprint) || !sha(pins.contextSha256) || !sha(pins.packageSha256) || !sha(pins.leanSha256)
      || pins.adapter === null || !pins.adapter || pins.contextSha256 !== contextSha256
      || createHash('sha256').update(canonical(fields)).digest('hex') !== buildFingerprint) {
    throw new WorkerError('EDITOR_CONFIG', 'The source capture build fingerprint does not match the context engine. Rebuild the Lean engine.');
  }
  return { contextSha256, buildFingerprint, packageSha256: pins.packageSha256, leanSha256: pins.leanSha256 };
}
