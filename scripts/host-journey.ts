/** RC5 launcher: build the extension, create a private Lean project
 * pointing at this engine, run the real VS Code (Electron) as an Extension
 * Development Host with extension/test/host-journey.cjs, then validate every
 * message the extension posted with the frontend's own parsers and write a
 * report with build, engine and Lean identity. Nothing in the user's VS Code
 * profile is touched: an isolated user-data directory is used, and the
 * installed extensions directory is only read so the Lean 4 language exists. */
import assert from 'node:assert/strict';
import { execFile, spawn } from 'node:child_process';
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import { createServer } from 'node:net';
import path from 'node:path';
import { promisify } from 'node:util';
import { fileURLToPath } from 'node:url';
import { parseEditorMessage } from '../src/editor/host.js';
import { hashContextExecutable } from '../server/source-capture-origin.js';

const run = promisify(execFile);
const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const extension = path.join(engine, 'extension');
import { readdirSync } from 'node:fs';
const macos = '/Applications/Visual Studio Code.app/Contents/MacOS';
const electron = process.env.DEFINOGRAPH_VSCODE_ELECTRON ?? path.join(macos, readdirSync(macos)[0]);
const extensionsDir = process.env.DEFINOGRAPH_VSCODE_EXTENSIONS ?? path.join(os.homedir(), '.vscode/extensions');
const out = process.env.DEFINOGRAPH_JOURNEY_EVIDENCE_OUT;
assert.ok(out, 'Set DEFINOGRAPH_JOURNEY_EVIDENCE_OUT to a directory outside the repository.');
await mkdir(out); // Refuse accidental reuse of cited evidence.
const sha = (buffer: Buffer | string) => createHash('sha256').update(buffer).digest('hex');
const config = JSON.parse(await readFile(path.join(engine, '.local/config.json'), 'utf8')) as { leanExecutable: string };

await run(process.execPath, ['build.mjs'], { cwd: extension });
const bundle = await readFile(path.join(extension, 'dist/extension.cjs'));
const reuseProject = process.env.DEFINOGRAPH_JOURNEY_REUSE_PROJECT;
const reuseProfile = process.env.DEFINOGRAPH_JOURNEY_REUSE_PROFILE;
assert.equal(Boolean(reuseProject), Boolean(reuseProfile), 'Reuse requires both paths from a previous failed report.');
const project = await realpath(reuseProject ?? await mkdtemp(path.join(os.tmpdir(), 'definograph-journey-')));
const userData = reuseProfile ? await realpath(reuseProfile) : await mkdtemp(path.join(os.tmpdir(), 'definograph-vscode-'));
await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
await mkdir(path.join(project, '.vscode'), { recursive: true });
await mkdir(path.join(userData, 'User'), { recursive: true });
const previousFixtureSource = `structure Rotor where
  Carrier : Type
  turn : Carrier → Carrier
  fixed : ∀ x, turn x = x
example (owner : Rotor) (unused : Nat) : Rotor := owner
`;
const source = previousFixtureSource + `def journeySeed (n : Nat) : Nat := n
example : Nat := journeySeed 0
`;
if (reuseProject) {
  assert.equal(await readFile(path.join(project, '.definograph-journey-fixture'), 'utf8'), engine, 'Only reuse this harness\'s own fixture.');
  const existingSource = await readFile(path.join(project, 'Main.lean'), 'utf8');
  assert.ok(existingSource === source || existingSource === previousFixtureSource, 'Do not overwrite an edited fixture; only the exact previous harness template may be upgraded.');
} else await writeFile(path.join(project, '.definograph-journey-fixture'), engine);
await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
await writeFile(path.join(project, 'Main.lean'), source);
await writeFile(path.join(project, 'Helper.lean'), '-- Private RC5 dirty-buffer control.\n');
await writeFile(path.join(project, '.vscode/settings.json'), JSON.stringify({ 'statementLens.engineDirectory': engine }, null, 2));
await writeFile(path.join(userData, 'User/settings.json'), JSON.stringify({ 'update.mode': 'none', 'telemetry.telemetryLevel': 'off', 'extensions.autoUpdate': false, 'extensions.autoCheckUpdates': false, 'workbench.startupEditor': 'none' }, null, 2));
const journalPath = path.join(project, 'journey.json');
// Reserve an unused loopback port, then release it immediately before spawning
// Electron, which must acquire that same port. Workspace Trust remains normal.
const reservation = createServer();
await new Promise<void>((resolve, reject) => { reservation.once('error', reject); reservation.listen({ host: '127.0.0.1', port: 0, exclusive: true }, resolve); });
const address = reservation.address();
assert.ok(address && typeof address !== 'string');
const debuggerPort = address.port;
const args = ['--new-window', '--disable-gpu', '--remote-debugging-address=127.0.0.1', `--remote-debugging-port=${debuggerPort}`, `--user-data-dir=${userData}`, `--extensions-dir=${extensionsDir}`,
  `--extensionDevelopmentPath=${extension}`, `--extensionTestsPath=${path.join(extension, 'test/host-journey.cjs')}`, project];
const started = Date.now();
console.log(JSON.stringify({ stage: 'launching isolated Extension Development Host', project, userData, debuggerPort, workspaceTrust: 'normal VS Code policy; no trust override' }));
await new Promise<void>((resolve, reject) => reservation.close(error => error ? reject(error) : resolve()));
const child = spawn(electron, args, { env: { ...process.env, DEFINOGRAPH_JOURNEY_CDP_PORT: String(debuggerPort), DEFINOGRAPH_JOURNEY_OUT: journalPath, DEFINOGRAPH_JOURNEY_SELECT: 'owner', DEFINOGRAPH_JOURNEY_ENGINE_EXECUTABLE: path.join(engine, '.local/statementlens-context'), ELECTRON_RUN_AS_NODE: '' }, stdio: ['ignore', 'pipe', 'pipe'] });
let log = '';
child.stdout.on('data', chunk => { log += String(chunk); }); child.stderr.on('data', chunk => { log += String(chunk); });
const code = await new Promise<number | null>(resolve => { const timer = setTimeout(() => { child.kill('SIGTERM'); resolve(-1); }, 15 * 60 * 1000); child.on('exit', code => { clearTimeout(timer); resolve(code); }); });
let journal: any = null;
try { journal = JSON.parse(await readFile(journalPath, 'utf8')); } catch { journal = null; }
const leanVersion = (await run(config.leanExecutable, ['--version'])).stdout.trim();
const validation: { index: number; type: string; requestId?: string; parsed: boolean }[] = [];
if (journal) for (const [index, item] of (journal.outgoing as { message: any }[]).entries()) {
  const parsed = parseEditorMessage(item.message);
  validation.push({ index, type: item.message.type, requestId: item.message.requestId, parsed: parsed !== undefined });
}
const passed = journal?.ok === true && code === 0 && validation.length > 0 && validation.every(item => item.parsed);
await mkdir(out, { recursive: true });
const report = {
  status: passed ? 'RC5 Extension Development Host journey completed in a real VS Code extension host with the real engine and Lean processes' : 'RC5 journey did not complete; see blockers, error and log',
  finishedAt: new Date().toISOString(), durationMs: Date.now() - started, electronExitCode: code,
  identity: { vscode: journal?.vscode ?? null, extensionBundleSha256: sha(bundle), distIndexSha256: sha(await readFile(path.join(engine, 'dist/index.html'))), engineExecutableSha256: await hashContextExecutable(path.join(engine, '.local/statementlens-context')), lean: leanVersion, extensionsDirUsed: extensionsDir },
  project: { source, selection: 'owner' },
  blockers: journal?.blockers ?? ['no journal was written'], error: journal?.error ?? null,
  retryPaths: passed ? null : { project, userData },
  steps: journal?.steps ?? [], actualWebviewMessages: journal?.incoming ?? [], nativeProcesses: journal?.nativeProcesses ?? [], messagesPosted: journal?.outgoing?.length ?? 0, allPostedMessagesParse: validation.length > 0 && validation.every(item => item.parsed), validation,
  notClaimed: ['manual mouse/keyboard interaction', 'DOM clicks for setup, refusal, race and refresh controls (those retain handler injection)', 'Windows or Linux hosts', 'a published VSIX'],
};
await writeFile(path.join(out, 'report.json'), JSON.stringify(report, null, 2) + '\n');
if (journal) await writeFile(path.join(out, 'journey.json'), JSON.stringify(journal, null, 2) + '\n');
await writeFile(path.join(out, 'host.log'), log);
if (passed) {
  await rm(userData, { recursive: true, force: true }).catch(() => undefined);
  await rm(project, { recursive: true, force: true }).catch(() => undefined);
}
console.log(JSON.stringify({ status: report.status, exit: code, steps: report.steps.length, posted: report.messagesPosted, parse: report.allPostedMessagesParse, blockers: report.blockers, error: report.error ? String(report.error).slice(0, 200) : null }));
if (!passed) process.exitCode = 1;
