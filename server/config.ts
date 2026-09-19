import { access, readFile, realpath, stat } from 'node:fs/promises';
import { constants } from 'node:fs';
import path from 'node:path';

export interface WorkerConfig {
  leanExecutable: string;
  workerExecutable: string;
  leanPath: string[];
  leanSysroot: string;
}

export class ConfigError extends Error {
  constructor(message: string) {
    super(message);
    this.name = 'ConfigError';
  }
}

async function checkedPath(value: unknown, label: string, executable = false): Promise<string> {
  if (typeof value !== 'string' || !path.isAbsolute(value) || value.includes('\0')) {
    throw new ConfigError(`${label} must be an absolute path.`);
  }
  try {
    const resolved = await realpath(value);
    const info = await stat(resolved);
    if (executable ? !info.isFile() : !info.isDirectory()) {
      throw new ConfigError(`${label} must point to ${executable ? 'an executable file' : 'a directory'}.`);
    }
    await access(resolved, executable ? constants.R_OK | constants.X_OK : constants.R_OK);
    return resolved;
  } catch (error) {
    if (error instanceof ConfigError) throw error;
    throw new ConfigError(`${label} is not available. Run npm run setup:lean.`);
  }
}

/** Read only the dedicated configuration; never consult or edit another Lean project. */
export async function loadWorkerConfig(configPath: string): Promise<WorkerConfig> {
  let value: unknown;
  try {
    const info = await stat(configPath);
    if (!info.isFile() || info.size > 32_768) throw new ConfigError('The local worker configuration is invalid.');
    value = JSON.parse(await readFile(configPath, 'utf8'));
  } catch (error) {
    if (error instanceof ConfigError) throw error;
    throw new ConfigError('Lean is not configured. Run npm run setup:lean.');
  }
  if (!value || typeof value !== 'object' || Array.isArray(value)) {
    throw new ConfigError('The local worker configuration must be a JSON object.');
  }
  const config = value as Record<string, unknown>;
  if (!Array.isArray(config.leanPath) || config.leanPath.length === 0 || config.leanPath.length > 32) {
    throw new ConfigError('leanPath must contain the isolated Lean library directories.');
  }
  const [leanExecutable, workerExecutable, leanSysroot, ...leanPath] = await Promise.all([
    checkedPath(config.leanExecutable, 'leanExecutable', true),
    checkedPath(config.workerExecutable, 'workerExecutable', true),
    checkedPath(config.leanSysroot, 'leanSysroot'),
    ...config.leanPath.map((entry, index) => checkedPath(entry, `leanPath[${index}]`)),
  ]);
  return { leanExecutable: leanExecutable!, workerExecutable: workerExecutable!, leanSysroot: leanSysroot!, leanPath };
}
