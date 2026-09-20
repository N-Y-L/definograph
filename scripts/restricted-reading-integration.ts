/** Actual editor contexts → audited semantics → the production guided reader.
 * Uses already-built native binaries; writes only a private temporary project. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createElement, type ComponentType } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { createServer } from 'vite';
import { analyzeEditorContext, type EditorRange } from '../server/editor-context.ts';
import type { Analysis, Expr } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import type { SemanticDocument, SemanticRelation } from '../src/semantic/types.ts';
import { compileReading, compileReadingCues, type ReadingDocument, type ReadingCuePlan } from '../src/reading/index.ts';
import { compileRestrictedMap } from '../src/restricted/model.ts';
import type { StatementReadingViewProps } from '../src/visual/StatementReadingView.tsx';
import { activeReadingGuide as guide } from './ssr-reading.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(rootDir, '.local/config.json'), 'utf8')) as { leanPath: string[]; contextExecutable: string; workerExecutable: string };
const hash = async (file: string) => createHash('sha256').update(await readFile(file)).digest('hex');
const hashes = async () => Promise.all([hash(config.contextExecutable), hash(config.workerExecutable)]);
const originalHashes = await hashes();
const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-restricted-reading-'));
const snapshots = new Map<string, string>();
const ssr = await createServer({ configFile: false, root: rootDir, appType: 'custom', server: { middlewareMode: true, watch: null, hmr: false, ws: false } });
let StatementReadingView: ComponentType<StatementReadingViewProps>;

interface Compiled { analysis: Analysis; document: SemanticDocument; reading: ReadingDocument; cues: ReadingCuePlan; html: string }
interface Case { name: string; term: string; header?: string; source?: string; opaque?: boolean; check: (result: Compiled) => void }
const restricted = (document: SemanticDocument, kind?: string) => document.relations.filter(relation => kind ? relation.kind === kind : relation.pluginId === 'restricted-maps');
const port = (relation: SemanticRelation, role: string) => {
  const matches = relation.ports.filter(port => port.role === role);
  assert.equal(matches.length, 1, `Expected one ${role} port`);
  return matches[0]!.objectId;
};
const head = (expression: Expr): string => expression.kind === 'app' ? head(expression.fn) : expression.kind === 'const' ? expression.name : expression.kind;
const position = (source: string, offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
function selection(source: string, term: string): EditorRange {
  const offset = source.lastIndexOf(term);
  assert.ok(offset >= 0, 'The exact selected fragment must occur in the submitted unsaved buffer');
  return { start: position(source, offset), end: position(source, offset + term.length) };
}
function render(document: SemanticDocument, selectedNodeId?: string): string {
  const warnings: string[] = [], originalError = console.error;
  console.error = (...items: unknown[]) => { warnings.push(items.map(String).join(' ')); };
  try {
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading: compileReading(document, { selectedNodeId }), onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
    assert.deepEqual(warnings, [], 'The production reader must render without React errors');
    return html;
  } finally { console.error = originalError; }
}
function figure(html: string, relation: SemanticRelation): string {
  const marker = html.indexOf(`data-restricted-relation="${relation.id}"`);
  assert.ok(marker >= 0, `A required restricted-map figure is absent: ${relation.id}`);
  const start = html.lastIndexOf('<figure', marker), end = html.indexOf('</figure>', marker);
  assert.ok(start >= 0 && end > marker);
  return html.slice(start, end + '</figure>'.length);
}
function assertIntroduction(result: Compiled, relation: SemanticRelation): void {
  assert.equal(relation.provenance.expressionPath, 'binder.type');
  const node = result.reading.nodes.find(node => node.id === relation.nodeId)!;
  assert.equal(node.binder!.objectId, port(relation, 'map'));
  assert.equal(node.scopeId, relation.scopeId);
  const cue = result.cues.cues.find(cue => cue.focusRelationIds.includes(relation.id))!;
  assert.ok(cue && cue.intent === 'introduce');
  const displayed = figure(guide(render(result.document, relation.nodeId)), relation);
  assert.ok(displayed.includes(`data-restricted-scope="${relation.scopeId}"`));
  assert.ok(displayed.includes('data-restricted-law="source"') && displayed.includes('data-restricted-law="target"'));
  assert.ok(displayed.includes('For every element in the source region') && displayed.includes('For every element in the target region'));
  assert.ok(displayed.includes('possibly empty') && !displayed.includes('<circle'));
  for (const branch of cue.branchPath.filter(branch => !['body', 'result'].includes(branch.edge.role))) {
    assert.ok(guide(render(result.document, relation.nodeId)).includes(`data-logic-role="${branch.edge.role}"`));
  }
}
function assertRoundTrip(result: Compiled, expectedDirection: 'forward' | 'inverse', assumed: boolean): void {
  const applications = restricted(result.document, 'restricted-application');
  const panel = result.reading.panels.find(panel => applications.filter(relation => relation.nodeId === panel.nodeId).length === 2)!;
  assert.ok(panel, 'Both halves of the round trip must belong to one clause');
  const stages = result.cues.cues.filter(cue => cue.panelId === panel.id);
  assert.deepEqual(stages.map(cue => cue.stage.relationKind), ['restricted-application', 'restricted-application', 'equality']);
  assert.deepEqual(stages.map(cue => cue.stage.kind), ['construction', 'construction', 'clause']);
  const first = result.document.relations.find(relation => relation.id === stages[0]!.stage.relationId)!;
  const second = result.document.relations.find(relation => relation.id === stages[1]!.stage.relationId)!;
  assert.equal(first.restrictedDirection, expectedDirection);
  assert.equal(second.restrictedDirection, expectedDirection === 'forward' ? 'inverse' : 'forward');
  assert.equal(port(first, 'output'), port(second, 'input'), 'The intermediate point must keep its exact semantic identity');
  assert.equal(port(first, 'map'), port(second, 'map'), 'symm must preserve the original bundled map identity');
  assert.equal(port(first, 'source carrier'), port(second, 'source carrier'));
  assert.equal(port(first, 'target carrier'), port(second, 'target carrier'));
  const equality = result.document.relations.find(relation => relation.id === panel.rootRelationIds[0])!;
  assert.equal(equality.kind, 'equality');
  assert.ok(equality.ports.some(argument => argument.objectId === port(second, 'output')));
  assert.ok(equality.ports.some(argument => argument.objectId === port(first, 'input')));
  assert.ok(panel.groups[0]!.connections.some(connection => connection.fromRelationId === first.id && connection.toRelationId === second.id && connection.kind === 'feeds'));
  const scope = result.document.scopes.find(scope => scope.id === first.scopeId)!;
  assert.equal(scope.assumptionNodeIds.length > 0, assumed);
  const active = guide(render(result.document, panel.nodeId));
  const displayed = figure(active, first);
  assert.ok(displayed.includes('data-restricted-application'));
  assert.ok(!displayed.includes('<circle'), 'A function application must not fabricate geometric point locations');
  assert.ok(compileRestrictedMap(result.document, first)!.explanation.includes('does not establish membership'));
}

const partial = 'import Mathlib.Logic.Equiv.PartialEquiv';
const topological = 'import Mathlib.Topology.OpenPartialHomeomorph.Defs';
const leftInverse = '∀ (A B : Type) (e : PartialEquiv A B) (x : A), x ∈ e.source → e.symm (e x) = x';
const localTerm = 'e.symm (e x) = x';
const cases: Case[] = [
  { name: 'source-restricted inverse law retains its assumption and intermediate point', term: leftInverse, check: result => {
    assertIntroduction(result, restricted(result.document, 'restricted-equivalence')[0]!);
    assertRoundTrip(result, 'forward', true);
    const region = restricted(result.document, 'restricted-region')[0]!;
    assert.equal(region.restrictedRegion, 'source');
    const membership = result.document.relations.find(relation => relation.kind === 'membership')!;
    assert.ok(membership.ports.some(argument => argument.objectId === port(region, 'region')));
  } },
  { name: 'an open partial homeomorphism preserves target-restricted inverse orientation', header: topological, term: '∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (e : OpenPartialHomeomorph A B) (y : B), y ∈ e.target → e (e.symm y) = y', check: result => {
    assertRoundTrip(result, 'inverse', true);
    const relation = restricted(result.document, 'restricted-equivalence')[0]!;
    assertIntroduction(result, relation);
    assert.ok(restricted(result.document).every(relation => relation.restrictedMapKind === 'open-partial-homeomorphism'));
    assert.match(compileRestrictedMap(result.document, relation)!.explanation, /open subsets.*continuous on their respective regions/);
  } },
  { name: 'double symm normalizes direction while retaining exact projected expression identity', header: topological, term: '∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (e : OpenPartialHomeomorph A B) (y : B), y ∈ e.symm.source → e.symm.symm (e.symm y) = y', check: result => {
    assertRoundTrip(result, 'inverse', true);
    const region = restricted(result.document, 'restricted-region')[0]!;
    assert.equal(region.restrictedRegion, 'target');
    assert.ok(result.document.objects.find(object => object.id === port(region, 'region'))!.expression.kind === 'app');
    assert.equal(compileRestrictedMap(result.document, region)!.target.object!.id, port(region, 'region'));
  } },
  { name: 'toPartialEquiv retains the original open-map object through a round trip', header: topological, term: '∀ (A B : Type) [TopologicalSpace A] [TopologicalSpace B] (e : OpenPartialHomeomorph A B) (x : A), x ∈ e.toPartialEquiv.source → e.toPartialEquiv.symm (e.toPartialEquiv x) = x', check: result => {
    assertRoundTrip(result, 'forward', true);
    const map = port(restricted(result.document, 'restricted-equivalence')[0]!, 'map');
    assert.ok(restricted(result.document).every(relation => port(relation, 'map') === map));
  } },
  { name: 'selected local theorem fragment retains the actual map and source hypothesis', term: localTerm, source: `${partial}\nexample (A B : Type) (e : PartialEquiv A B) (x : A) (hx : x ∈ e.source) : ${localTerm} := e.left_inv hx\n`, check: result => {
    assert.equal(result.analysis.validation, 'kernel-type-checked-context-fragment');
    assertRoundTrip(result, 'forward', true);
    assert.ok(result.document.choices.some(choice => choice.role === 'parameter'));
    assert.ok(result.reading.nodes.some(node => node.binder?.name === 'hx' && node.binder.role === 'assumption'));
  } },
  { name: 'existential maps remain inside their separate negated alternatives', term: '∀ (A B : Type), ¬ ((∃ e : PartialEquiv A B, True) ∨ (∃ f : PartialEquiv A B, True))', check: result => {
    const maps = restricted(result.document, 'restricted-equivalence');
    assert.equal(maps.length, 2);
    for (const relation of maps) {
      assertIntroduction(result, relation);
      const cue = result.cues.cues.find(cue => cue.focusRelationIds.includes(relation.id))!;
      assert.deepEqual(cue.roles, ['negated', 'alternative', 'witness']);
      const other = maps.find(candidate => candidate.id !== relation.id)!;
      assert.ok(!result.document.scopes.find(scope => scope.id === relation.scopeId)!.objectIds.includes(port(other, 'map')));
    }
  } },
  { name: 'unknown wrappers keep nested local-map applications as contained expressions', header: `${partial}\ndef ReadingUnknown {A : Type} (x : A) : Prop := x = x`, opaque: true, term: '∀ (A B : Type) (e : PartialEquiv A B) (x : A), ReadingUnknown (e.symm (e x))', check: result => {
    const applications = restricted(result.document, 'restricted-application');
    assert.equal(applications.length, 2);
    const panel = result.reading.panels.find(panel => panel.nodeId === applications[0]!.nodeId)!;
    assert.ok(panel.rootRelationIds.every(id => result.document.relations.find(relation => relation.id === id)!.fidelity === 'structural'));
    const stages = result.cues.cues.filter(cue => cue.panelId === panel.id);
    assert.equal(stages[0]!.stage.kind, 'clause');
    for (const application of applications) {
      const cue = stages.find(cue => cue.stage.relationId === application.id)!;
      assert.equal(cue.stage.kind, 'contained');
      assert.ok(cue.detail.includes('not a separate assertion'));
    }
    const active = guide(render(result.document, panel.nodeId));
    assert.ok(active.includes('Inside this expression') && active.includes('not separate assertions'));
  } },
  { name: 'an abstract predicate remains the parent of its constructed argument', term: '∀ (A B : Type) (e : PartialEquiv A B) (x : A) (F : A → Prop), F (e.symm (e x))', check: result => {
    const applications = restricted(result.document, 'restricted-application');
    const panel = result.reading.panels.find(panel => panel.nodeId === applications[0]!.nodeId)!;
    assert.equal(panel.rootRelationIds.length, 1);
    const parent = result.document.relations.find(relation => relation.id === panel.rootRelationIds[0])!;
    assert.equal(parent.kind, 'predicate'); assert.equal(parent.label, 'F');
    assert.ok(parent.conditions.some(condition => condition.includes('no additional properties')));
    const stages = result.cues.cues.filter(cue => cue.panelId === panel.id);
    assert.equal(stages[0]!.stage.kind, 'clause');
    for (const application of applications) assert.equal(stages.find(cue => cue.stage.relationId === application.id)!.stage.kind, 'contained');
  } },
  { name: 'an unaudited coercion cannot acquire restricted-application laws', opaque: true, term: '∀ (A B : Type) (inst : CoeFun (PartialEquiv A B) (fun _ => A → B)) (e : PartialEquiv A B) (x : A), (@CoeFun.coe (PartialEquiv A B) (fun _ => A → B) inst e x) = (@CoeFun.coe (PartialEquiv A B) (fun _ => A → B) inst e x)', check: result => {
    assert.equal(restricted(result.document, 'restricted-equivalence').length, 1, 'The supplied bundled map still has its actual type');
    assert.equal(restricted(result.document, 'restricted-application').length, 0, 'A separate CoeFun parameter has no contract connecting it to the bundled function');
    assert.ok(result.document.opaqueRegions.some(region => head(region.expression) === 'CoeFun.coe'));
  } },
  { name: 'same-spelled project projections remain uninterpreted', header: 'namespace PartialEquiv\ndef source (n : Nat) : Nat := n\nend PartialEquiv', opaque: true, term: '∀ n : Nat, PartialEquiv.source n = n', check: result => {
    assert.equal(restricted(result.document).length, 0);
    assert.ok(result.document.opaqueRegions.some(region => head(region.expression) === 'PartialEquiv.source'));
    assert.ok(result.document.relations.some(relation => relation.kind === 'equality'));
    assert.ok(!result.html.includes('data-restricted-relation='));
  } },
  { name: 'same-spelled project bundle types expose only their actual ordinary function field', header: 'structure PartialEquiv (A B : Type) where\n  toFun : A → B', term: '∀ (A B : Type) (e : PartialEquiv A B) (x : A), e.toFun x = e.toFun x', check: result => {
    assert.equal(restricted(result.document).length, 0);
    assert.equal(result.document.relations.filter(relation => relation.kind === 'application' && relation.pluginId === 'structure-fields').length, 1);
    const owner = result.document.objects.find(object => object.binder?.structure?.name === 'PartialEquiv')!;
    assert.deepEqual(owner.binder!.structure!.fields.map(field => [field.name, field.kind]), [['toFun', 'data']]);
    assert.ok(!result.html.includes('data-restricted-law='));
  } },
  { name: 'an unguarded global equality receives no invented region hypothesis', term: '∀ (A B : Type) (e : PartialEquiv A B) (x : A), e.symm (e x) = x', check: result => {
    assertRoundTrip(result, 'forward', false);
    assert.equal(result.document.relations.filter(relation => relation.kind === 'membership').length, 0);
    assert.equal(restricted(result.document, 'restricted-region').length, 0);
    const model = compileRestrictedMap(result.document, restricted(result.document, 'restricted-equivalence')[0]!)!;
    assert.equal(model.source.object, undefined);
    assert.equal(model.target.object, undefined);
  } },
  { name: 'equal carrier types do not collapse the source and target region roles', term: '∀ (A : Type) (e : PartialEquiv A A) (x : A), x ∈ e.source → e.symm (e x) = x', check: result => {
    assertRoundTrip(result, 'forward', true);
    const model = compileRestrictedMap(result.document, restricted(result.document, 'restricted-equivalence')[0]!)!;
    assert.equal(model.sameCarrier, true);
    assert.equal(model.source.role, 'source');
    assert.equal(model.target.role, 'target');
    assert.notEqual(model.source.label, model.target.label);
  } },
  { name: 'a checked user type alias shares the same grammar while retaining its declared name', header: `${partial}\nabbrev RegionCorrespondence (A B : Type) := PartialEquiv A B`, term: '∀ (A B : Type) (e : RegionCorrespondence A B) (x : A), x ∈ e.source → e.symm (e x) = x', check: result => {
    assertRoundTrip(result, 'forward', true);
    const relation = restricted(result.document, 'restricted-equivalence')[0]!;
    assertIntroduction(result, relation);
    const object = result.document.objects.find(object => object.id === port(relation, 'map'))!;
    assert.match(object.binder!.type, /^RegionCorrespondence /);
    assert.equal(object.binder!.typeExpansion!.definitionalEquality, true);
    assert.deepEqual(object.binder!.typeExpansion!.constants, ['RegionCorrespondence']);
    assert.ok(relation.conditions.some(condition => condition.includes('Lean checked the declared type RegionCorrespondence')));
  } },
  { name: 'a family-selected map composes generic application with the restricted-map grammar', term: '∀ (I A B : Type) (family : I → PartialEquiv A B) (i : I) (x : A), x ∈ (family i).source → (family i).symm ((family i) x) = x', check: result => {
    const applications = restricted(result.document, 'restricted-application');
    assert.equal(applications.length, 2);
    const panel = result.reading.panels.find(panel => panel.nodeId === applications[0]!.nodeId)!;
    const stages = result.cues.cues.filter(cue => cue.panelId === panel.id);
    assert.deepEqual(stages.map(cue => cue.stage.relationKind), ['application', 'restricted-application', 'restricted-application', 'equality']);
    const producedMap = result.document.relations.find(relation => relation.id === stages[0]!.stage.relationId)!;
    const first = result.document.relations.find(relation => relation.id === stages[1]!.stage.relationId)!;
    const second = result.document.relations.find(relation => relation.id === stages[2]!.stage.relationId)!;
    assert.equal(port(producedMap, 'output'), port(first, 'map'));
    assert.equal(port(first, 'map'), port(second, 'map'));
    assert.equal(port(first, 'output'), port(second, 'input'));
    assert.ok(panel.groups[0]!.connections.some(connection => connection.fromRelationId === producedMap.id && connection.toRelationId === first.id && connection.kind === 'feeds'));
  } },
];

let passed = 0, failed = 0;
try {
  const toolchain = path.join(temporary, 'lean-toolchain');
  await writeFile(toolchain, 'leanprover/lean4:v4.28.0\n'); snapshots.set(toolchain, 'leanprover/lean4:v4.28.0\n');
  ({ StatementReadingView } = await ssr.ssrLoadModule('/src/visual/StatementReadingView.tsx'));
  for (const [index, test] of cases.entries()) {
    try {
      const source = test.source ?? `${test.header ?? partial}\n#check ${test.term}\n`;
      const fileName = path.join(temporary, `Case${index}.lean`), saved = '-- The unsaved buffer is intentionally different.\n';
      await writeFile(fileName, saved); snapshots.set(fileName, saved);
      const response = await analyzeEditorContext({ engineDirectory: rootDir, fileName, source, selection: selection(source, test.term), workspaceTrusted: true, libraryPaths: config.leanPath.filter(entry => !entry.includes('/leantex/')) });
      assert.equal(response.ok, true, JSON.stringify(response));
      const analysis = response as unknown as Analysis;
      assert.ok(!analysis.diagnostics.some(diagnostic => diagnostic && typeof diagnostic === 'object' && 'severity' in diagnostic && diagnostic.severity === 'error'));
      const document = compileSemanticDocument(analysis), reading = compileReading(document), cues = compileReadingCues(reading, document);
      assert.deepEqual(document.diagnostics, []);
      assert.equal(document.scenes.length, 0, 'Abstract restricted maps must not acquire numerical coordinates');
      assert.equal(cues.truncated, false);
      if (!test.opaque) assert.deepEqual(document.opaqueRegions.map(region => head(region.expression)), [], 'Audited projections and applications should not remain opaque');
      for (const relation of restricted(document)) assert.ok(compileRestrictedMap(document, relation), 'Every audited relation must have a valid scope-preserving model');
      for (const cue of cues.cues) assert.deepEqual(cue.assumptionNodeIds, document.scopes.find(scope => scope.id === cue.scopeId)!.assumptionNodeIds);
      const html = render(document);
      for (const panel of reading.panels) assert.ok(html.includes(`data-reading-node="${panel.nodeId}"`), 'The full statement must retain every clause');
      test.check({ analysis, document, reading, cues, html });
      passed++; console.log(`PASS ${test.name}`);
    } catch (error) { failed++; console.error(`FAIL ${test.name}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  for (const [file, source] of snapshots) assert.equal(await readFile(file, 'utf8'), source, 'A private source or toolchain file changed during analysis');
  assert.deepEqual(await hashes(), originalHashes, 'A native executable changed during this audit; rerun after builds finish');
  console.log(`${passed}/${cases.length} actual-editor restricted-map → guided reader SSR checks passed. Private source/configuration remained unchanged.`);
  process.exitCode = failed ? 1 : 0;
} finally { await ssr.close(); await rm(temporary, { recursive: true, force: true }); }
