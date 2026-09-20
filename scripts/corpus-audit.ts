/** Read-only corpus audit: native binaries and dependencies must already be built.
 * Only a private temporary fixture is compiled; reports go under ignored .local. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdir, mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { corpusCases, type CorpusCase } from '../corpus/cases.ts';
import { analyzeEditorContext, type EditorRange } from '../server/editor-context.ts';
import { createWorkerBackend, runBoundedProcess } from '../server/worker.ts';
import type { Analysis, Expr, StatementNode } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import { compileInterpretationReport, type InterpretationReport } from '../src/semantic/coverage.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
import { compileReading, compileReadingCues } from '../src/reading/index.ts';
import { compileTypedConstruction } from '../src/constructions/model.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const selectedIds = process.argv.slice(2);
if (selectedIds.some(id => !corpusCases.some(c => c.id === id))) throw new Error('Arguments must be corpus case IDs. With no arguments the full corpus runs.');
const selected = corpusCases.filter(c => !selectedIds.length || selectedIds.includes(c.id));
// Keep the baseline in a focused renaming run; do not silently skip the comparison.
const requiredIds = new Set(selected.flatMap(c => c.expected.compareRenameWith ? [c.id, c.expected.compareRenameWith] : [c.id]));
const cases = corpusCases.filter(c => requiredIds.has(c.id));
const config = JSON.parse(await readFile(path.join(rootDir, '.local/config.json'), 'utf8')) as { leanExecutable: string; leanPath: string[]; workerExecutable: string; leanSysroot: string };
const digest = (value: string | Uint8Array) => createHash('sha256').update(value).digest('hex');
const executableHashes = async () => ({ workerSha256: digest(await readFile(config.workerExecutable)), contextSha256: digest(await readFile(path.join(rootDir, '.local/statementlens-context'))) });
const originalExecutables = await executableHashes();
const fixture = await mkdtemp(path.join(os.tmpdir(), 'statementlens-corpus-'));
const backend = createWorkerBackend({ rootDir });
const nodes = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(nodes)];
const rawHead = (expr: Expr): { name: string; canonical?: boolean } => {
  if (expr.kind === 'app') return rawHead(expr.fn);
  if (expr.kind === 'const') return { name: expr.name, canonical: expr.canonical };
  if (expr.kind === 'var') return { name: `(variable) ${expr.name}` };
  return { name: expr.kind === 'opaque' ? '(opaque expression)' : `(${expr.kind})` };
};
const counts = (values: readonly string[]) => Object.fromEntries([...new Set(values)].sort().map(value => [value, values.filter(item => item === value).length]));
const position = (source: string, offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
function selection(source: string, term: string): EditorRange {
  const start = source.lastIndexOf(term);
  assert.ok(start >= 0, 'Editor selection must occur verbatim in its fixture');
  return { start: position(source, start), end: position(source, start + term.length) };
}

/** Ignore labels, keep constructor identity, ordered ports and scoped binder identity. */
function fingerprint(document: SemanticDocument): unknown {
  const binderIds = new Map(document.choices.map((choice, index) => [choice.binderId, `binder:${index}`]));
  const key = (expr: Expr, local = binderIds, depth = 0): unknown => {
    if (depth > 128) throw new Error('Fingerprint depth exhausted');
    switch (expr.kind) {
      case 'var': return ['var', local.get(expr.id) ?? expr.id];
      case 'const': return ['const', expr.name, expr.canonical];
      case 'literal': return ['literal', expr.value];
      case 'sort': return ['sort', expr.name];
      case 'opaque': return ['opaque', expr.text];
      case 'app': return ['app', key(expr.fn, local, depth + 1), expr.args.filter((_, i) => !expr.argumentKinds || expr.argumentKinds[i] === 'value').map(arg => key(arg, local, depth + 1))];
      case 'lambda': case 'forall': { const inner = new Map(local); inner.set(expr.binder.id, `local:${depth}`); return [expr.kind, key(expr.body, inner, depth + 1)]; }
    }
  };
  const objects = new Map(document.objects.map(o => [o.id, o]));
  return { relations: document.relations.map(relation => JSON.stringify([relation.kind, relation.fidelity, relation.pluginId, relation.ports.map(port => [port.role, key(objects.get(port.objectId)!.expression)])])).sort(), choices: document.choices.map(choice => [choice.role, choice.dependsOn]) };
}

function invariantChecks(document: SemanticDocument): void {
  const allNodes = nodes(document.tree), nodeIds = new Set(allNodes.map(node => node.id));
  const scopeIds = new Set(document.scopes.map(scope => scope.id)), objectIds = new Set(document.objects.map(object => object.id));
  assert.deepEqual(document.coverage.map(fragment => fragment.nodeId).sort(), allNodes.filter(node => !node.children.length).map(node => node.id).sort(), 'Every atomic statement needs coverage');
  assert.deepEqual(document.diagnostics, [], 'The bounded corpus must not exhaust traversal');
  assert.equal(scopeIds.size, document.scopes.length);
  assert.equal(objectIds.size, document.objects.length);
  for (const relation of document.relations) {
    assert.ok(nodeIds.has(relation.nodeId) && scopeIds.has(relation.scopeId));
    relation.ports.forEach(port => assert.ok(objectIds.has(port.objectId), 'Every relation port needs its original object'));
  }
  for (const choice of document.choices) choice.dependsOn.forEach(id => assert.ok(choice.availableObjectIds.includes(id), 'No dependence on an unavailable later/sibling choice'));
  for (const implication of allNodes.filter(node => node.kind === 'implies' && node.children.length === 2)) {
    const premise = implication.children[0]!, conclusion = implication.children[1]!;
    const premiseScope = document.scopes.find(scope => scope.id === `scope:${premise.id}`)!;
    const conclusionScope = document.scopes.find(scope => scope.id === `scope:${conclusion.id}`)!;
    assert.ok(!premiseScope.assumptionNodeIds.includes(premise.id), 'A premise cannot assume itself');
    assert.ok(conclusionScope.assumptionNodeIds.includes(premise.id), 'Its conclusion must retain the premise');
  }
  const reading = compileReading(document), cues = compileReadingCues(reading, document, { maxCues: 1000 });
  assert.equal(cues.truncated, false);
  for (const cue of cues.cues) {
    const scope = document.scopes.find(scope => scope.id === cue.scopeId)!;
    assert.ok(scope, 'Every cue needs its semantic scope');
    assert.deepEqual(cue.assumptionNodeIds, scope.assumptionNodeIds, 'Guidance must retain local assumptions');
    assert.deepEqual(cue.branchPath, reading.sequence.find(step => step.nodeId === cue.nodeId)!.branchPath);
  }
}

function expectations(test: CorpusCase, document: SemanticDocument, prior: Map<string, SemanticDocument>): void {
  invariantChecks(document);
  const expected = test.expected, kinds = document.relations.map(relation => relation.kind as string);
  const missingHeads = document.opaqueRegions.map(region => rawHead(region.expression).name);
  for (const kind of expected.relationKinds ?? []) assert.ok(kinds.includes(kind), `Missing interpreted relation kind: ${kind}`);
  for (const kind of expected.absentKinds ?? []) assert.ok(!kinds.includes(kind), `Unexpected interpretation of unaudited constructor: ${kind}`);
  for (const head of expected.opaqueHeads ?? []) assert.ok(missingHeads.includes(head), `Expected missing vocabulary was not retained: ${head}; observed ${missingHeads.join(', ')}`);
  if (expected.noOpaque) assert.equal(document.opaqueRegions.length, 0, `Unexpected missing vocabulary: ${missingHeads.join(', ')}`);
  if (expected.noNumericalScenes) assert.equal(document.scenes.length, 0, 'No numerical coordinates should be assigned to this fixture');
  if (expected.binderRoles) assert.deepEqual(document.choices.map(choice => choice.role), expected.binderRoles);
  if (expected.witnessDependencyCount !== undefined) {
    const witnesses = document.choices.filter(choice => choice.role === 'existential');
    assert.equal(witnesses.length, 1);
    assert.equal(witnesses[0]!.dependsOn.length, expected.witnessDependencyCount, 'Changing quantifier order must change the permitted dependence');
  }
  const interpreted = document.relations.filter(relation => relation.fidelity !== 'structural');
  if (test.category === 'supported') assert.equal(document.opaqueRegions.length, 0, 'Supported means no opaque predicate applications in this chosen statement');
  if (test.category === 'partially-supported') { assert.ok(document.opaqueRegions.length > 0); assert.ok(interpreted.length > 0); }
  if (test.category === 'currently-unsupported') { assert.ok(document.opaqueRegions.length > 0); assert.equal(interpreted.length, 0, 'This fixture should have only structural predicate support'); }
  if (expected.rootOpaque) {
    const reading = compileReading(document);
    const target = reading.panels.find(panel => panel.opaqueRegionIds.length && panel.relationIds.some(id => interpreted.some(relation => relation.id === id)));
    assert.ok(target, 'Known child and unknown parent must remain within one atomic panel');
    assert.ok(target.rootRelationIds.length > 0 && target.rootRelationIds.every(id => document.relations.find(relation => relation.id === id)?.fidelity === 'structural'), 'A recognized child must not replace its unknown parent');
    assert.ok(compileReadingCues(reading, document).cues.some(cue => cue.stage.kind === 'contained' && cue.detail.includes('not a separate assertion')), 'Contained mathematics must be labelled as expression structure');
  }
  if (expected.branchRoles) {
    const reading = compileReading(document);
    const matches = reading.sequence.filter(step => expected.branchRoles!.every(role => step.branchPath.some(branch => branch.edge.role === role)));
    assert.ok(matches.length >= 2, 'Both alternatives must retain the enclosing roles');
    matches.forEach(step => assert.ok(document.scopes.find(scope => scope.nodeId === step.nodeId)!.assumptionNodeIds.length > 0, 'The conditional premise must remain in scope'));
  }
  if (expected.dependentSignature) {
    const reading = compileReading(document);
    assert.ok(reading.quantifierGroups.some(group => compileTypedConstruction(document, group.binders).signatures.some(signature => signature.kind === 'dependent-map' && signature.resultDependsOn.length > 0)), 'A section must preserve its indexed codomain');
  }
  if (expected.compareRenameWith) { const original = prior.get(expected.compareRenameWith); assert.ok(original, 'Rename baseline did not compile'); assert.deepEqual(fingerprint(document), fingerprint(original), 'Binder renaming changed interpreted topology'); }
}

interface CaseResult {
  id: string; title: string; mode: string; category: string; passed: boolean; failure?: string;
  sourceSha256: string; interpretation: string; knownLimitations: readonly string[];
  validation?: string; provenance?: Analysis['provenance']; diagnostics?: unknown; interpretationReport?: InterpretationReport; coverage?: Record<string, number>; interpretedVocabulary?: Record<string, number>;
  uninterpretedHeads?: { name: string; canonical?: boolean; occurrences: number }[];
  logicalNodes?: number; typedObjects?: number; scopedChoices?: number;
}
const results: CaseResult[] = [], prior = new Map<string, SemanticDocument>();
const sourceSnapshots = new Map<string, string>();
try {
  await mkdir(path.join(fixture, '.lake/build/lib/lean'), { recursive: true });
  const dependency = await readFile(path.join(rootDir, 'corpus/ProjectDependency.lean'), 'utf8');
  const projectFiles: Record<string, string> = {
    'lean-toolchain': 'leanprover/lean4:v4.28.0\n',
    'lakefile.toml': 'name = "statementlens_corpus"\n[[lean_lib]]\nname = "ProjectDependency"\n',
    'lake-manifest.json': JSON.stringify({ version: '1.1.0', packagesDir: '.lake/packages', packages: [] }),
    'ProjectDependency.lean': dependency,
  };
  for (const [name, source] of Object.entries(projectFiles)) { await writeFile(path.join(fixture, name), source); sourceSnapshots.set(name, source); }
  if (cases.some(test => test.mode === 'editor')) await runBoundedProcess(config.leanExecutable, { args: ['-o', '.lake/build/lib/lean/ProjectDependency.olean', 'ProjectDependency.lean'], cwd: fixture, env: { ...process.env, LEAN_PATH: '' }, timeoutMs: 10_000 });
  for (const test of cases) {
    const entry: CaseResult = { id: test.id, title: test.title, mode: test.mode, category: test.category, passed: false, sourceSha256: digest(test.source), interpretation: test.interpretation, knownLimitations: test.missing };
    try {
      let output;
      if (test.mode === 'editor') {
        // A saved private file exists, but the submitted buffer is deliberately distinct.
        const name = `${test.id.replaceAll('-', '_')}.lean`, saved = '-- Private corpus fixture; the unsaved buffer is analyzed.\n';
        await writeFile(path.join(fixture, name), saved); sourceSnapshots.set(name, saved);
        output = await analyzeEditorContext({ engineDirectory: rootDir, fileName: path.join(fixture, name), source: test.source, selection: selection(test.source, test.selection!), workspaceTrusted: true, libraryPaths: config.leanPath.filter(entry => !entry.includes('/leantex/')) });
      } else output = await backend.analyze(test.source);
      assert.equal(output.ok, true, JSON.stringify(output));
      const analysis = output as unknown as Analysis;
      const document = compileSemanticDocument(analysis);
      entry.validation = analysis.validation; entry.provenance = analysis.provenance; entry.diagnostics = analysis.diagnostics;
      const interpretationReport = compileInterpretationReport(document, analysis.definitions);
      entry.interpretationReport = interpretationReport;
      assert.equal(interpretationReport.clauses.total, document.coverage.length);
      assert.equal(interpretationReport.clauses.interpreted + interpretationReport.clauses.partial + interpretationReport.clauses.structural, document.coverage.length);
      assert.equal(interpretationReport.gaps.reduce((total, gap) => total + gap.occurrences, 0), document.opaqueRegions.length);
      for (const gap of interpretationReport.gaps) {
        assert.ok(gap.nodeIds.every(id => document.opaqueRegions.some(region => region.nodeId === id)));
        assert.ok(gap.scopeIds.every(id => document.scopes.some(scope => scope.id === id)));
        if (gap.canExpand) assert.ok(analysis.definitions?.some(definition => definition.name === gap.constant && definition.canExpand));
      }
      for (const fragment of document.coverage) {
        const local = compileInterpretationReport(document, analysis.definitions, fragment.nodeId);
        assert.equal(local.clauses.total, 1, 'Selected-fragment report must not include sibling clauses');
        assert.ok(local.gaps.every(gap => gap.nodeIds.every(id => id === fragment.nodeId)));
      }
      entry.coverage = counts(document.coverage.map(fragment => fragment.status));
      entry.interpretedVocabulary = counts(document.relations.filter(relation => relation.fidelity !== 'structural').map(relation => relation.kind));
      const heads = document.opaqueRegions.map(region => rawHead(region.expression));
      entry.uninterpretedHeads = [...new Set(heads.map(head => JSON.stringify(head)))].sort().map(key => ({ ...JSON.parse(key), occurrences: heads.filter(head => JSON.stringify(head) === key).length }));
      entry.logicalNodes = nodes(document.tree).length; entry.typedObjects = document.objects.length; entry.scopedChoices = document.choices.length;
      assert.ok(!analysis.diagnostics.some(diagnostic => diagnostic !== null && typeof diagnostic === 'object' && 'severity' in diagnostic && diagnostic.severity === 'error'), 'Corpus source must elaborate without file errors');
      expectations(test, document, prior);
      prior.set(test.id, document); entry.passed = true;
    } catch (error) { entry.failure = error instanceof Error ? error.message : String(error); }
    results.push(entry);
    console.log(`${entry.passed ? 'PASS' : 'FAIL'} ${test.id}${entry.failure ? `: ${entry.failure}` : ''}`);
  }
  for (const [name, source] of sourceSnapshots) assert.equal(await readFile(path.join(fixture, name), 'utf8'), source, `Private fixture source/config changed: ${name}`);
  const missing = new Map<string, { name: string; canonical?: boolean; cases: string[]; occurrences: number }>();
  for (const entry of results) for (const head of entry.uninterpretedHeads ?? []) {
    const key = JSON.stringify([head.name, head.canonical]), previous = missing.get(key) ?? { name: head.name, canonical: head.canonical, cases: [], occurrences: 0 };
    previous.cases.push(entry.id); previous.occurrences += head.occurrences; missing.set(key, previous);
  }
  const missingVocabulary = [...missing.values()].sort((a, b) => b.cases.length - a.cases.length || a.name.localeCompare(b.name));
  const finalExecutables = await executableHashes();
  const stableExecutables = JSON.stringify(originalExecutables) === JSON.stringify(finalExecutables);
  const report = { schemaVersion: 1, generatedAt: new Date().toISOString(), corpus: 'statement-lens-semantic-vocabulary', completeCorpus: cases.length === corpusCases.length,
    purpose: 'A selected vocabulary regression corpus, not a percentage of arbitrary mathematics, proof correctness, or visual comprehension.',
    environment: { node: process.version, ...originalExecutables, dependencySha256: digest(dependency), stableExecutables, ...(stableExecutables ? {} : { finalExecutables }) },
    total: results.length, passed: results.filter(result => result.passed).length, failed: results.filter(result => !result.passed).length,
    categories: counts(results.map(result => result.category)), projectSourceAndConfigUnchanged: true, results, missingVocabulary };
  const cell = (value: string) => value.replaceAll('|', '\\|').replaceAll('\n', ' ');
  const markdown = [
    '# Semantic vocabulary corpus', '', report.purpose, '',
    `${report.passed}/${report.total} case expectations passed. ${report.completeCorpus ? 'Full corpus.' : 'Focused subset only.'} Private fixture source/config remained unchanged.`, '', ...(stableExecutables ? [] : ['INVALID RUN: a native executable changed during the audit. Rerun after builds complete.', '']),
    '| Case | Input | Expected category | Result | Interpreted relation kinds | Uninterpreted heads |',
    '|---|---|---|---|---|---|',
    ...results.map(result => `| ${cell(result.title)} | ${result.mode} | ${result.category} | ${result.passed ? 'PASS' : 'FAIL'} | ${Object.keys(result.interpretedVocabulary ?? {}).join(', ') || '—'} | ${cell(result.uninterpretedHeads?.map(head => `${head.name}${head.canonical === false ? ' (not audited)' : ''}`).join(', ') || result.failure || '—')} |`),
    '', '## Missing vocabulary observed in this corpus', '',
    ...missingVocabulary.map(head => `- ${head.name}${head.canonical === false ? ' (not audited for built-in interpretation)' : ''}: ${head.cases.length} case(s), ${head.occurrences} expression occurrence(s). Cases: ${head.cases.join(', ')}.`),
    '', '## Interpretation limits', '', ...results.filter(result => result.knownLimitations.length).map(result => `- ${result.id}: ${result.knownLimitations.join(' ')}`),
    '', ...results.filter(result => result.failure).map(result => `- FAILURE ${result.id}: ${cell(result.failure!)}`), '',
    'The inventory includes coercion/projection wrappers. Frequency is a corpus-specific engineering signal, not a ranking of mathematical importance.', '',
  ].join('\n');
  await mkdir(path.join(rootDir, '.local'), { recursive: true });
  const suffix = report.completeCorpus ? '' : '-focused';
  await writeFile(path.join(rootDir, `.local/corpus-audit${suffix}.json`), JSON.stringify(report, null, 2) + '\n');
  await writeFile(path.join(rootDir, `.local/corpus-audit${suffix}.md`), markdown);
  console.log(`${report.passed}/${report.total} semantic corpus expectations passed; reports: .local/corpus-audit${suffix}.{json,md}`);
  if (!stableExecutables) console.error('INVALID RUN: native executables changed during the audit. Rerun after builds complete.');
  process.exitCode = report.failed || !stableExecutables ? 1 : 0;
} finally { backend.close?.(); await rm(fixture, { recursive: true, force: true }); }
