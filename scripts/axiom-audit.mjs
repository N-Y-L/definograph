/** Axiom policy for the proved core, checked against the compiled modules of the native build.
 *
 *   node scripts/axiom-audit.mjs              policy, negative control and kernel replay
 *   node scripts/axiom-audit.mjs --no-replay  skip the replay (saves about a minute)
 *   node scripts/axiom-audit.mjs --fresh      replay the whole import closure from an empty environment
 */
import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { copyFile, mkdtemp, readFile, rm } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { parseArgs } from 'node:util';
import { fileSha256, loadSourceCaptureDependency } from './source-capture-dependency.mjs';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const { values: options } = parseArgs({ options: { 'no-replay': { type: 'boolean' }, fresh: { type: 'boolean' } } });
const auditScript = path.join(root, 'scripts/axiom-audit.lean');
const policyFile = path.join(root, 'scripts/axiom-policy.json');
const fixtureDirectory = path.join(root, 'scripts/fixtures/axiom-audit');
const fixtureModule = 'AxiomAuditFixture';

/** What the audit must report for the fixture: one line per planted declaration. */
const expectedFixtureViolations = [
  'declared-axiom AxiomAuditFixture.plantedAxiom',
  'forbidden-axiom AxiomAuditFixture.plantedSorry [sorryAx]',
  'forbidden-axiom AxiomAuditFixture.dependsOnPlantedSorry [sorryAx]',
  'forbidden-axiom AxiomAuditFixture.plantedSorryDefinition [sorryAx]',
  'forbidden-axiom AxiomAuditFixture.plantedNativeDecide [Lean.ofReduceBool, Lean.trustCompiler]',
  'forbidden-axiom AxiomAuditFixture.plantedNativeDecide._proof_1_1 [Lean.ofReduceBool, Lean.trustCompiler]',
  'forbidden-axiom AxiomAuditFixture.dependsOnPlantedAxiom [AxiomAuditFixture.plantedAxiom]',
  'unlisted-ratcheted-axiom AxiomAuditFixture.plantedChoice',
  'exception-kind AxiomAuditFixture.plantedChoiceListedAsStatement',
  'stale-exception AxiomAuditFixture.clean',
  'certificate-axioms AxiomAuditFixture.regressedCertificate',
  'certificate-axioms AxiomAuditFixture.clean',
  'certificate-policy AxiomAuditFixture.clean',
  'certificate-missing AxiomAuditFixture.missingCertificate',
  'theorem-count theorem constants',
];

const config = JSON.parse(await readFile(path.join(root, '.local/config.json'), 'utf8').catch(() => {
  throw new Error('No native build found. Run npm run setup:lean first.');
}));
const pins = config.sourceCapture;
if (!pins?.libraryPath) throw new Error('The native build has no source-capture library. Run npm run setup:lean.');
const lean = config.leanExecutable;
const toolchainBin = path.dirname(lean);

function run(command, args, { leanPath, timeout, cwd = root }) {
  const result = spawnSync(command, args, {
    cwd, encoding: 'utf8', timeout, maxBuffer: 32 * 1024 * 1024,
    // leanchecker locates its library by running `lean` from PATH.
    env: { ...process.env, LEAN_PATH: leanPath, PATH: toolchainBin + path.delimiter + (process.env.PATH ?? '') },
  });
  if (result.error) throw result.error;
  return result;
}

/** The build names its output directory at random; the configuration records where it is.
 *  Tie the files about to be audited to the vendored sources they were compiled from. */
async function verifiedModules() {
  const snapshot = await loadSourceCaptureDependency(path.join(root, 'vendor/DefinographCapture'));
  assert.equal(pins.sourceCommit, snapshot.manifest.sourceCommit, 'Rebuild: the vendored revision changed.');
  assert.equal(pins.packageSha256, snapshot.digest, 'Rebuild: the vendored manifest changed.');
  assert.deepEqual(pins.artifacts.map(({ module, sourceSha256 }) => ({ module, sha256: sourceSha256 })),
    snapshot.sources.map(({ module, sha256 }) => ({ module, sha256 })), 'Rebuild: the vendored sources changed.');
  assert.equal(await fileSha256(lean), pins.leanSha256, 'Rebuild: the Lean executable changed.');
  for (const artifact of pins.artifacts) {
    const olean = path.join(pins.libraryPath, artifact.module.replaceAll('.', '/') + '.olean');
    assert.equal(await fileSha256(olean), artifact.oleanSha256, `Rebuild: compiled module differs from the build record: ${olean}`);
  }
  return { modules: snapshot.sources.map(source => source.module), entry: snapshot.manifest.entryModule };
}

function audit(policy, importRoot, modules, leanPath) {
  const result = run(lean, ['--run', auditScript, policy, importRoot, modules.join(',')], { leanPath, timeout: 180_000 });
  if (result.status !== 0 && result.status !== 1) throw new Error(`The audit could not run:\n${result.stderr || result.stdout}`);
  const report = JSON.parse(result.stdout);
  assert.equal(report.ok, result.status === 0, 'The audit exit status disagrees with its report.');
  return report;
}

const describe = ({ rule, name, detail }) => rule === 'forbidden-axiom' ? `${rule} ${name} [${detail}]` : `${rule} ${name}`;
const checks = [];
const check = async (name, body) => {
  const started = Date.now();
  try { checks.push({ name, ok: true, note: await body() }); }
  catch (error) { checks.push({ name, ok: false, note: error.message }); }
  const last = checks.at(-1);
  console.log(`${last.ok ? 'PASS' : 'FAIL'} ${name} (${((Date.now() - started) / 1000).toFixed(1)} s)${last.note ? `\n  ${String(last.note).replaceAll('\n', '\n  ')}` : ''}`);
};

const { modules, entry } = await verifiedModules();

await check('the proved core satisfies the axiom policy', async () => {
  const report = audit(policyFile, entry, modules, pins.libraryPath);
  if (!report.ok) throw new Error(report.violations.map(describe).join('\n'));
  const counts = report.counts;
  const inProof = report.ratchetedAxiomUsers.filter(user => user.kind === 'proof').length;
  return `${counts.theoremConstants} theorem constants in ${modules.length} modules; axioms reached: ${report.reachableAxioms.join(', ')}; `
    + `${counts.byAxiomSet.none ?? 0} use none; ${counts.ratchetedAxiomUsers} listed exceptions use Classical.choice `
    + `(${inProof} through the proof, ${counts.ratchetedAxiomUsers - inProof} already in the statement); ${report.certificates.length} certificates match their recorded axioms`;
});

await check('the audit rejects a planted sorry, native_decide, axiom and unlisted Classical.choice', async () => {
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'definograph-axiom-audit-'));
  try {
    const source = path.join(temporary, fixtureModule + '.lean');
    await copyFile(path.join(fixtureDirectory, fixtureModule + '.lean'), source);
    const compiled = run(lean, ['-o', path.join(temporary, fixtureModule + '.olean'), source], { leanPath: '', timeout: 120_000, cwd: temporary });
    assert.equal(compiled.status, 0, `The fixture did not compile:\n${compiled.stderr || compiled.stdout}`);
    const report = audit(path.join(fixtureDirectory, 'policy.json'), fixtureModule, [fixtureModule], temporary);
    assert.equal(report.ok, false, 'The audit accepted the fixture.');
    assert.deepEqual(report.violations.map(describe).sort(), [...expectedFixtureViolations].sort());
    return `${report.violations.length} violations, each the expected one`;
  } finally { await rm(temporary, { recursive: true, force: true }); }
});

if (!options['no-replay']) {
  await check(options.fresh ? 'the kernel re-checks the whole import closure from an empty environment'
    : 'the kernel re-checks every declaration of the compiled modules', async () => {
    const args = options.fresh ? ['--fresh', entry] : modules;
    const result = run(path.join(toolchainBin, 'leanchecker'), args, { leanPath: pins.libraryPath, timeout: 900_000 });
    if (result.status !== 0) throw new Error(result.stderr || result.stdout || `leanchecker exited with ${result.status}`);
    return `leanchecker ${options.fresh ? `--fresh ${entry}` : `over ${modules.length} modules`} exited with 0`;
  });
}

const failed = checks.filter(result => !result.ok).length;
console.log(`${checks.length - failed}/${checks.length} axiom checks passed.`);
process.exitCode = failed ? 1 : 0;
