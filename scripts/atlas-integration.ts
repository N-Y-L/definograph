import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createElement, type ComponentType } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { createServer } from 'vite';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis, StatementNode } from '../src/core/types.ts';
import type { AnalysisOptions } from '../src/protocol.ts';
import { compileSemanticDocument, expressionKey } from '../src/semantic/index.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
import { compileReading } from '../src/reading/index.ts';
import { planReadingPresentation, visibleReadingNodes, type ReadingRegion } from '../src/reading/presentation.ts';
import { compileTypedConstruction } from '../src/constructions/model.ts';
import type { ReadingDocument } from '../src/reading/types.ts';
import type { StatementReadingViewProps } from '../src/visual/StatementReadingView.tsx';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
// Vite handles the renderer's TSX and local CSS in-process. No browser or listener is needed.
const ssr = await createServer({ configFile: false, root: rootDir, appType: 'custom',
  server: { middlewareMode: true, watch: null, hmr: false, ws: false } });
interface Compiled { analysis: Analysis; document: SemanticDocument; reading: ReadingDocument; html: string }
interface Case { name: string; source: string; options?: AnalysisOptions; body?: boolean; check?: (result: Compiled) => void }
const flatten = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(flatten)];
const objectName = (document: SemanticDocument, id: string) => document.objects.find(o => o.id === id)?.label;
const orderedChoices = (reading: ReadingDocument) => reading.quantifierGroups.flatMap(group => group.binders.map(binder => [group.kind, binder.name]));
let StatementReadingView: ComponentType<StatementReadingViewProps>;

function htmlFor(document: SemanticDocument, reading: ReadingDocument): string {
  return renderToStaticMarkup(createElement(StatementReadingView, { document, reading,
    onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
}
function regionChildren(region: ReadingRegion): readonly ReadingRegion[] {
  if (region.kind === 'binders') return region.body ? [region.body] : [];
  if (region.kind === 'implication') return [...region.assumptions, region.conclusion];
  if (region.kind === 'negation') return [region.body];
  return 'children' in region ? region.children : [];
}
function allRegions(region: ReadingRegion): ReadingRegion[] { return [region, ...regionChildren(region).flatMap(allRegions)]; }
function assertPresentation(reading: ReadingDocument): void {
  const presentation = planReadingPresentation(reading);
  const regions = allRegions(presentation.root);
  const sourceIds = regions.flatMap(region => [...region.sourceNodeIds]);
  assert.deepEqual([...sourceIds].sort(), reading.nodes.map(n => n.id).sort(), 'Every source node must survive atlas grouping exactly once');
  assert.equal(new Set(sourceIds).size, sourceIds.length);
  for (const region of regions) {
    for (const id of region.sourceNodeIds) assert.equal(presentation.nodeToRegionId[id], region.id);
    if (region.kind === 'binders') {
      assert.ok(region.binders.every(binder => binder.kind === region.node.kind));
      for (let i = 1; i < region.binders.length; i++) assert.equal(region.binders[i - 1]!.children[0]!.id, region.binders[i]!.id);
    }
    if (region.kind === 'implication') {
      let source = region.node;
      region.assumptions.forEach((premise, index) => {
        assert.equal(source.kind, 'implies');
        assert.equal(source.children[0]!.id, premise.node.id, 'An antecedent must stay an intact logical region');
        assert.equal(region.sourceNodeIds[index], source.id);
        source = source.children[1]!;
      });
      assert.equal(source.id, region.conclusion.node.id, 'A grouped chain must stop at its next binder or connective');
    }
  }
}
async function compile(test: Pick<Case, 'source' | 'options' | 'body'>): Promise<Compiled> {
  const result = await backend.analyze(test.source, undefined, test.options);
  assert.equal(result.ok, true, String(result.error ?? 'Native Lean rejected the fixture'));
  const original = result as unknown as Analysis;
  const analysis = test.body && original.definitionTree
    ? { ...original, tree: original.definitionTree, expression: original.definitionTree.expression } : original;
  const document = compileSemanticDocument(analysis), reading = compileReading(document);
  const html = htmlFor(document, reading);
  assertPresentation(reading);
  for (const region of allRegions(planReadingPresentation(reading).root)) {
    assert.ok(html.includes(`data-source-nodes="${region.sourceNodeIds.join(' ')}"`), `The atlas omitted or reassigned a logical region: ${region.id}`);
  }
  assert.deepEqual(document.diagnostics, []);
  assert.deepEqual(reading.nodes.map(node => node.id), flatten(analysis.tree).map(node => node.id));
  for (const group of reading.quantifierGroups) {
    const construction = compileTypedConstruction(document, group.binders);
    assert.equal(construction.status, 'ready', construction.diagnostics.join('; '));
    assert.deepEqual(construction.objects.map(o => o.objectId), group.binders.map(b => b.objectId));
    const available = new Set(document.scopes.find(scope => scope.id === group.binders.at(-1)!.scopeId)!.objectIds);
    for (const type of construction.types) if (type.objectId) assert.ok(available.has(type.objectId), 'Carrier diagrams cannot link to a later or sibling binder');
    for (const map of construction.maps) {
      assert.ok(construction.types.some(type => type.id === map.domainId));
      assert.ok(construction.types.some(type => type.id === map.codomainId));
    }
    for (const signature of construction.signatures) {
      signature.inputs.forEach((input, index) => assert.ok(input.dependsOn.every(dependency => dependency < index)));
      assert.ok(signature.resultDependsOn.every(index => index < signature.inputs.length));
    }
  }
  assert.ok(!html.includes('type="range"') && !html.includes('type="number"'), 'The atlas must not require numerical choices');
  for (const panel of reading.panels) {
    assert.ok(html.includes(`data-reading-node="${panel.nodeId}"`), `The atlas omitted atomic clause ${panel.nodeId}`);
    const selected = compileReading(document, { selectedNodeId: panel.nodeId });
    assert.deepEqual(selected.sequence, reading.sequence, 'Selection must not reorder or remove logical regions');
    const selectedHtml = htmlFor(document, selected);
    for (const other of reading.panels) assert.ok(selectedHtml.includes(`data-reading-node="${other.nodeId}"`));
    for (const group of panel.groups) for (const connection of group.connections) {
      assert.ok(group.relationIds.includes(connection.fromRelationId) && group.relationIds.includes(connection.toRelationId));
      assert.equal(document.relations.find(r => r.id === connection.fromRelationId)?.scopeId, group.scopeId);
      assert.equal(document.relations.find(r => r.id === connection.toRelationId)?.scopeId, group.scopeId);
    }
  }
  return { analysis, document, reading, html };
}

const cases: Case[] = [
  { name: 'universe instantiations keep identically printed carriers distinct', source: '∀ (f : (@ULift Nat : Type 1) → (@ULift Nat : Type 2)), True', check: ({ document, reading }) => {
    const construction = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
    assert.equal(construction.maps.length, 1);
    assert.equal(construction.types.length, 2);
    assert.notEqual(construction.maps[0]!.domainId, construction.maps[0]!.codomainId);
    assert.notEqual(expressionKey(construction.types[0]!.expression), expressionKey(construction.types[1]!.expression));
  } },
  { name: 'a witness remains after its arbitrary input', source: '∀ c : ℝ, ∃ p : ℝ, p ∈ Metric.ball c 1', check: ({ document, reading }) => {
    assert.deepEqual(orderedChoices(reading), [['forall', 'c'], ['exists', 'p']]);
    assert.deepEqual(reading.quantifierGroups[1]!.binders[0]!.dependsOn.map(id => objectName(document, id)), ['c']);
  } },
  { name: 'a fixed witness does not acquire dependence on a later input', source: '∃ p : ℝ, ∀ c : ℝ, p ∈ Metric.ball c 1', check: ({ reading }) => {
    assert.deepEqual(orderedChoices(reading), [['exists', 'p'], ['forall', 'c']]);
    assert.deepEqual(reading.quantifierGroups[0]!.binders[0]!.dependsOn, []);
  } },
  { name: 'direct implication chains retain the scope of each premise', source: '∀ (P Q R : Prop), P → Q → R', check: ({ reading }) => {
    const implications = reading.nodes.filter(n => n.kind === 'implies');
    assert.equal(implications.length, 2);
    const [p, q, r] = reading.panels.map(panel => reading.nodes.find(n => n.id === panel.nodeId)!);
    assert.deepEqual(p.assumptionNodeIds, []);
    assert.deepEqual(q.assumptionNodeIds, [p.id]);
    assert.deepEqual(r.assumptionNodeIds, [p.id, q.id]);
  } },
  { name: 'a nested implication premise never turns into two global assumptions', source: '∀ (P Q R S : Prop), (P → Q) → (R ∨ ¬S)', check: ({ reading }) => {
    const outer = reading.nodes.find(n => n.kind === 'implies')!;
    assert.equal(outer.children[0]!.kind, 'implies');
    assert.equal(outer.children[1]!.kind, 'or');
    for (const leaf of reading.nodes.filter(n => !n.children.length && n.context.some(c => c.includes('disjunction')))) {
      assert.deepEqual(leaf.assumptionNodeIds, [outer.children[0]!.id]);
    }
    const negative = reading.nodes.find(n => n.kind === 'not')!;
    assert.equal(negative.children[0]!.edgeFromParent?.role, 'negated');
  } },
  { name: 'an intervening universal and witness remain inside the implication', source: '∀ (X : Type) (P : Prop) (Q : X → Prop), P → ∀ x : X, Q x → ∃ y : X, Q y', check: ({ reading }) => {
    const implication = reading.nodes.find(n => n.kind === 'implies')!;
    assert.equal(implication.children[1]!.kind, 'forall');
    const exists = reading.nodes.find(n => n.kind === 'exists')!;
    assert.equal(exists.assumptionNodeIds.length, 2);
    assert.equal(reading.quantifierGroups.at(-1)!.branchPath.filter(p => p.edge.role === 'conclusion').length, 2);
  } },
  { name: 'iff directions and disjunction alternatives retain separate envelopes', source: '∀ (P Q R : Prop), (P ∨ Q) ↔ ¬(P ∧ R)', check: ({ reading }) => {
    const iff = reading.nodes.find(n => n.kind === 'iff')!;
    assert.deepEqual(iff.directions?.map(d => [d.assumptionNodeId, d.conclusionNodeId]), [[iff.children[0]!.id, iff.children[1]!.id], [iff.children[1]!.id, iff.children[0]!.id]]);
    assert.equal(iff.children[0]!.kind, 'or');
    assert.equal(iff.children[1]!.kind, 'not');
    assert.ok(reading.nodes.every(n => !n.assumptionNodeIds.length));
  } },
  { name: 'an unknown wrapper stays the claim around recognized geometry', source: '∀ (F : Prop → Prop) (x : ℝ), F (x ∈ Metric.ball 0 1)', check: ({ document, reading, html }) => {
    const panel = reading.panels[0]!;
    const root = document.relations.find(r => r.id === panel.rootRelationIds[0])!;
    assert.equal(root.kind, 'predicate');
    assert.equal(root.label, 'F');
    assert.equal(panel.rootRelationIds.length, 1);
    assert.ok(panel.relationIds.some(id => document.relations.find(r => r.id === id)?.kind === 'membership'));
    assert.ok(html.includes('Inside this expression'));
    assert.ok(html.includes('not separate assertions'));
    assert.ok(html.indexOf('Inside this expression') < html.indexOf('Membership condition · the named element belongs'), 'Membership must appear inside the subordinate detail, not replace F');
  } },
  { name: 'quantified proposition arguments keep their inner relation scope', source: '∀ (F : Prop → Prop), F (∀ x : ℝ, x ∈ Metric.ball 0 1)', check: ({ document, reading }) => {
    const panel = reading.panels[0]!;
    const root = document.relations.find(r => r.id === panel.rootRelationIds[0])!;
    assert.equal(root.label, 'F');
    const membership = document.relations.find(r => r.kind === 'membership')!;
    assert.ok(membership);
    assert.notEqual(membership.scopeId, root.scopeId);
    assert.ok(panel.groups.some(group => group.role === 'local-expression' && group.relationIds.includes(membership.id)));
  } },
  { name: 'implicit ordinary type arguments do not become map inputs', source: '∀ (F : ∀ {A : Type}, A → Prop) (x : ℝ), F x', check: ({ document, reading }) => {
    const root = document.relations.find(r => r.id === reading.panels[0]!.rootRelationIds[0])!;
    assert.equal(root.label, 'F');
    assert.deepEqual(root.ports.map(p => objectName(document, p.objectId)), ['F', 'x']);
  } },
  { name: 'abstract map composition shares carriers and keeps map order', source: '∀ (A B C : Type) (f : A → B) (g : B → C) (h : A → C) (x : A), g (f x) = h x', check: ({ document, reading }) => {
    const equality = document.relations.find(r => r.kind === 'equality')!;
    const output = equality.ports.find(p => p.role === 'left')!.objectId;
    const g = document.relations.find(r => r.kind === 'application' && r.ports.some(p => p.role === 'output' && p.objectId === output))!;
    assert.equal(objectName(document, g.ports.find(p => p.role === 'function')!.objectId), 'g');
    const input = g.ports.find(p => p.role === 'input 1')!.objectId;
    const f = document.relations.find(r => r.kind === 'application' && r.ports.some(p => p.role === 'output' && p.objectId === input))!;
    assert.equal(objectName(document, f.ports.find(p => p.role === 'function')!.objectId), 'f');
    const construction = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
    assert.equal(construction.types.length, 3);
    const mapF = construction.maps.find(map => map.name === 'f')!, mapG = construction.maps.find(map => map.name === 'g')!, mapH = construction.maps.find(map => map.name === 'h')!;
    assert.equal(mapF.codomainId, mapG.domainId);
    assert.equal(mapF.domainId, mapH.domainId);
    assert.equal(mapG.codomainId, mapH.codomainId);
    assert.equal(construction.members.find(member => member.name === 'x')!.typeId, mapF.domainId);
  } },
  { name: 'dependent outputs retain their type family and bound input', source: '∀ (A : Type) (B : A → Type) (f : (a : A) → B a) (x : A), f x = f x', check: ({ document, reading }) => {
    const construction = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
    assert.equal(construction.signatures.find(s => s.name === 'B')?.kind, 'family');
    const f = construction.signatures.find(s => s.name === 'f')!;
    assert.equal(f.kind, 'dependent-map');
    assert.deepEqual(f.resultDependsOn, [0]);
    assert.ok(!construction.maps.some(map => map.name === 'f'));
  } },
  { name: 'relations and multi-input maps keep ordered typed arguments', source: '∀ (X Y Z : Type) (R : X → Y → Prop) (f : X → Y → Z) (x : X) (y : Y), R x y → f x y = f x y', check: ({ document, reading }) => {
    const construction = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
    const relation = construction.signatures.find(s => s.name === 'R')!, fn = construction.signatures.find(s => s.name === 'f')!;
    assert.equal(relation.kind, 'relation'); assert.deepEqual(relation.inputs.map(input => input.type), ['X', 'Y']);
    assert.equal(fn.kind, 'multi-input-map'); assert.deepEqual(fn.inputs.map(input => input.type), ['X', 'Y']);
    assert.equal(fn.result, 'Z');
  } },
  { name: 'identically named binders in sibling branches keep distinct identities', source: '∀ X : Type, (∀ x : X, x = x) ∧ (∀ x : X, x = x)', check: ({ document, reading }) => {
    const xs = document.objects.filter(o => o.binder?.name === 'x');
    assert.equal(xs.length, 2);
    assert.notEqual(xs[0]!.id, xs[1]!.id);
    const xGroups = reading.quantifierGroups.filter(g => g.binders.some(b => b.name === 'x'));
    assert.equal(xGroups.length, 2);
    assert.notEqual(xGroups[0]!.branchPath.at(-1)!.edge.index, xGroups[1]!.branchPath.at(-1)!.edge.index);
    assert.equal(compileTypedConstruction(document, xGroups.flatMap(g => [...g.binders])).status, 'invalid-scope');
  } },
  { name: 'locally bound expressions remain separate from their enclosing predicate', source: '∀ (P : (ℝ → Prop) → Prop), P (fun x : ℝ => x = 0)', check: ({ reading }) => {
    assert.ok(reading.panels[0]!.groups.some(group => group.role === 'local-expression'));
    assert.ok(reading.panels[0]!.groups.some(group => group.role === 'clause'));
  } },
  { name: 'a partial metric constructor is not presented as a set', source: '∀ (P : (ℝ → Set ℝ) → Prop), P (Metric.ball (0 : ℝ))', check: ({ document }) => {
    assert.equal(document.relations.filter(r => r.kind === 'metric-region').length, 0);
    assert.equal(document.scenes.filter(s => s.kind === 'ball').length, 0);
  } },
  { name: 'definition signatures retain parameters rather than universal claims', source: 'Function.Injective', options: { inputMode: 'declaration' }, check: ({ reading }) => {
    assert.equal(reading.root.kind, 'parameter');
    assert.ok(reading.quantifierGroups.every(g => g.kind === 'parameter'));
  } },
  { name: 'definition bodies keep parameter construction outside their quantified condition', source: 'Function.Injective', options: { inputMode: 'declaration' }, body: true, check: ({ reading }) => {
    assert.deepEqual(reading.quantifierGroups.map(g => g.kind), ['parameter', 'forall']);
    assert.ok(reading.nodes.some(n => n.kind === 'implies'));
  } },
];

let passed = 0, failed = 0;
try {
  ({ StatementReadingView } = await ssr.ssrLoadModule('/src/visual/StatementReadingView.tsx'));
  for (const test of cases) {
    try {
      const result = await compile(test);
      test.check?.(result);
      passed += 1; console.log(`PASS ${test.name}`);
    } catch (error) {
      failed += 1; console.error(`FAIL ${test.name}: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  for (const [name, check] of [
    ['dependent arrow and forall function types have identical elaborated meaning', async () => {
      const arrow = await compile({ source: '∀ (A : Type) (B : A → Type) (f : (a : A) → B a) (x : A), f x = f x' });
      const quantified = await compile({ source: '∀ (A : Type) (B : A → Type) (f : ∀ a : A, B a) (x : A), f x = f x' });
      assert.equal(expressionKey(arrow.analysis.expression), expressionKey(quantified.analysis.expression));
      assert.deepEqual(compileTypedConstruction(arrow.document, arrow.reading.quantifierGroups[0]!.binders), compileTypedConstruction(quantified.document, quantified.reading.quantifierGroups[0]!.binders));
    }],
    ['renaming binders changes labels without changing construction or relation identity', async () => {
      const first = await compile({ source: '∀ (A B : Type) (f : A → B) (x : A), f x = f x' });
      const renamed = await compile({ source: '∀ (U V : Type) (map : U → V) (input : U), map input = map input' });
      assert.equal(expressionKey(first.analysis.expression), expressionKey(renamed.analysis.expression));
      assert.deepEqual(first.document.relations.map(r => [r.id, r.kind, r.ports]), renamed.document.relations.map(r => [r.id, r.kind, r.ports]));
      const topology = ({ document, reading }: Compiled) => {
        const construction = compileTypedConstruction(document, reading.quantifierGroups[0]!.binders);
        return { types: construction.types.map(t => [t.id, t.objectId]), maps: construction.maps.map(m => [m.objectId, m.domainId, m.codomainId]), members: construction.members.map(m => [m.objectId, m.typeId]) };
      };
      assert.deepEqual(topology(first), topology(renamed));
    }],
    ['a selected deep clause retains every ancestor beyond the normal display budget', async () => {
      let tree: StatementNode = { id: 'deep-leaf', kind: 'predicate', label: 'True', lean: 'True', expression: { kind: 'const', name: 'True' }, children: [] };
      for (let i = 0; i < 120; i++) tree = { id: `negation-${i}`, kind: 'not', label: 'Not', lean: '¬ …', expression: { kind: 'const', name: 'True' }, children: [tree] };
      const document = compileSemanticDocument({ source: 'trusted depth fixture', tree, expression: tree.expression });
      const reading = compileReading(document, { selectedNodeId: 'deep-leaf' });
      const visible = visibleReadingNodes(reading, 100);
      assert.equal(visible.size, 121);
      assert.ok(reading.selection.ancestorNodeIds.every(id => visible.has(id)));
      assert.ok(htmlFor(document, reading).includes('data-reading-node="deep-leaf"'));
    }],
  ] as const) {
    try { await check(); passed += 1; console.log(`PASS ${name}`); }
    catch (error) { failed += 1; console.error(`FAIL ${name}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  console.log(`${passed}/${passed + failed} native Lean → atlas model → server-rendered reader checks passed.`);
  process.exitCode = failed ? 1 : 0;
} finally {
  backend.close?.();
  await ssr.close();
}
