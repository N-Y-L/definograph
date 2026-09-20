import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createElement, type ComponentType, type ReactNode } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { createServer } from 'vite';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis } from '../src/core/types.ts';
import type { AnalysisOptions } from '../src/protocol.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
import { compileReading, compileReadingCues, type ReadingCue, type ReadingCuePlan, type ReadingDocument } from '../src/reading/index.ts';
import type { StatementReadingViewProps } from '../src/visual/StatementReadingView.tsx';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
const ssr = await createServer({ configFile: false, root: rootDir, appType: 'custom', server: { middlewareMode: true, watch: null, hmr: false, ws: false } });
interface Compiled { analysis: Analysis; document: SemanticDocument; reading: ReadingDocument; plan: ReadingCuePlan }
interface Case { name: string; source: string; options?: AnalysisOptions; body?: boolean; check: (result: Compiled) => void }
interface GuideProps { plan: ReadingCuePlan; cue: ReadingCue; reading: ReadingDocument; document: SemanticDocument; onChoose: (cue: ReadingCue) => void; children: ReactNode }
let GuidedReading: ComponentType<GuideProps>, StatementReadingView: ComponentType<StatementReadingViewProps>;
const introductions = (plan: ReadingCuePlan) => plan.cues.filter(cue => cue.intent === 'introduce');
const relationKinds = (plan: ReadingCuePlan) => plan.cues.filter(cue => cue.stage.relationKind).map(cue => cue.stage.relationKind);
const relation = (result: Compiled, cue: ReadingCue) => result.document.relations.find(relation => relation.id === cue.stage.relationId)!;
const objectName = (document: SemanticDocument, id: string) => document.objects.find(object => object.id === id)?.label;

function assertPlan(result: Compiled): void {
  const { document, reading, plan } = result;
  assert.equal(plan.truncated, false);
  assert.equal(plan.totalCueCount, plan.cues.length);
  assert.equal(new Set(plan.cues.map(cue => cue.id)).size, plan.cues.length);
  const coveredSources = new Set(plan.cues.flatMap(cue => [...cue.sourceNodeIds]));
  assert.ok(reading.nodes.every(node => coveredSources.has(node.id)), 'Every source node needs a cue or grouped introduction');
  for (const [index, cue] of plan.cues.entries()) {
    assert.equal(cue.ordinal, index + 1);
    const step = reading.sequence.find(step => step.nodeId === cue.nodeId)!;
    const scope = document.scopes.find(scope => scope.id === cue.scopeId)!;
    assert.ok(scope && scope.nodeId === cue.nodeId);
    assert.deepEqual(cue.ancestorNodeIds, step.ancestorNodeIds);
    assert.deepEqual(cue.branchPath, step.branchPath);
    assert.deepEqual(cue.assumptionNodeIds, scope.assumptionNodeIds);
    assert.deepEqual(cue.contextObjectIds, scope.objectIds);
    assert.equal(cue.scopePath.at(-1), cue.scopeId);
    assert.ok(cue.focusObjectIds.every(id => document.objects.some(object => object.id === id)));
    for (const id of cue.focusRelationIds) {
      const relation = document.relations.find(relation => relation.id === id)!;
      assert.equal(relation.nodeId, cue.nodeId); assert.equal(relation.scopeId, cue.scopeId);
    }
    const group = reading.panels.find(panel => panel.id === cue.panelId)?.groups.find(group => group.scopeId === cue.scopeId);
    const available = new Set([...cue.contextObjectIds, ...cue.focusObjectIds, ...group?.objectIds ?? []]);
    assert.ok(cue.retainedObjectIds.every(id => available.has(id)), 'Object continuity cannot escape the current scope');
    if (cue.stage.kind === 'contained') assert.ok(cue.detail.includes('not a separate assertion'));
    const html = renderToStaticMarkup(createElement(GuidedReading, { plan, cue, reading, document, onChoose: () => undefined, children: createElement('div', { 'data-fixture-stage': cue.id }) }));
    assert.ok(html.includes(`data-cue-scope="${cue.scopeId}"`));
    for (const part of cue.branchPath.filter(part => !['body', 'result'].includes(part.edge.role))) {
      assert.ok(html.includes(`data-logic-role="${part.edge.role}"`), `The staged view detached its ${part.edge.role} envelope`);
    }
    if (scope.context.some(context => context === 'Within a function body' || context === 'Within a quantified expression')) {
      assert.ok(cue.contextLabels.some(context => context === 'Within a function body' || context === 'Within a quantified expression'));
    }
  }
  for (const panel of reading.panels) {
    assert.ok(plan.cues.some(cue => cue.panelId === panel.id));
    assert.deepEqual(compileReadingCues(compileReading(document, { selectedNodeId: panel.nodeId }), document), plan, 'Source selection cannot reorder cue logic');
  }
}

async function compile(source: string, options?: AnalysisOptions, body = false): Promise<Compiled> {
  const response = await backend.analyze(source, undefined, options);
  assert.equal(response.ok, true, String(response.error ?? 'Native Lean rejected fixture'));
  const original = response as unknown as Analysis;
  const analysis = body && original.definitionTree ? { ...original, tree: original.definitionTree, expression: original.definitionTree.expression } : original;
  const document = compileSemanticDocument(analysis), reading = compileReading(document), plan = compileReadingCues(reading, document, { maxCues: 1000 });
  return { analysis, document, reading, plan };
}

const cases: Case[] = [
  { name: 'forall-exists introductions preserve permitted dependence', source: '∀ c : ℝ, ∃ p : ℝ, p ∈ Metric.ball c 1', check: ({ plan }) => {
    const intro = introductions(plan);
    assert.deepEqual(intro.map(cue => cue.role), ['arbitrary', 'witness']);
    assert.deepEqual(intro[1]!.binders[0]!.dependsOn, intro[0]!.focusObjectIds);
    assert.deepEqual(relationKinds(plan), ['metric-region', 'membership']);
  } },
  { name: 'exists-forall introduces a fixed witness before later choices', source: '∃ p : ℝ, ∀ c : ℝ, p ∈ Metric.ball c 1', check: ({ plan }) => {
    const intro = introductions(plan);
    assert.deepEqual(intro.map(cue => cue.role), ['witness', 'arbitrary']);
    assert.deepEqual(intro[0]!.binders[0]!.dependsOn, []);
  } },
  { name: 'nested negation and alternatives stay visible around staged geometry', source: '∀ (P : Prop) (x : ℝ), P → ¬(x ∈ Metric.ball 0 1 ∨ x ∈ Metric.ball 1 2)', check: result => {
    const geometry = result.plan.cues.filter(cue => cue.stage.relationKind === 'metric-region');
    assert.equal(geometry.length, 2);
    geometry.forEach((cue, index) => {
      assert.deepEqual(cue.roles, ['conclusion', 'negated', 'alternative']);
      assert.equal(cue.branchPath.at(-1)!.edge.index, index);
      assert.equal(cue.assumptionNodeIds.length, 1);
      const reading = compileReading(result.document, { selectedNodeId: cue.nodeId });
      const html = renderToStaticMarkup(createElement(StatementReadingView, { reading, document: result.document }));
      assert.ok(html.includes('data-logic-role="negated"') && html.includes('data-logic-role="alternative"') && html.includes('data-logic-role="conclusion"'));
    });
  } },
  { name: 'iff sides and nested antecedents do not become global assumptions', source: '∀ (P Q R S : Prop), ((P → Q) → R) ↔ ¬S', check: ({ plan, reading }) => {
    const iff = reading.nodes.find(node => node.kind === 'iff')!;
    assert.ok(plan.cues.some(cue => cue.nodeId === iff.id && cue.title === 'Read both directions'));
    const negative = plan.cues.find(cue => cue.roles.includes('equivalence-right') && cue.roles.includes('negated'))!;
    assert.deepEqual(negative.assumptionNodeIds, []);
    const nestedPremise = plan.cues.find(cue => cue.roles.filter(role => role === 'assumption').length === 2)!;
    assert.ok(nestedPremise);
    assert.deepEqual(nestedPremise.assumptionNodeIds, []);
  } },
  { name: 'map composition follows both ordered paths before their comparison', source: '∀ (A B C : Type) (f : A → B) (g : B → C) (h : A → C) (x : A), g (f x) = h x', check: result => {
    const applications = result.plan.cues.filter(cue => cue.stage.relationKind === 'application');
    assert.deepEqual(applications.map(cue => objectName(result.document, relation(result, cue).ports.find(port => port.role === 'function')!.objectId)), ['f', 'g', 'h']);
    assert.equal(result.plan.cues.at(-1)!.stage.relationKind, 'equality');
    assert.equal(introductions(result.plan)[0]!.binders.length, 7);
  } },
  { name: 'nested set construction follows audited operations and operand order', source: '∀ (X : Type) (A B C : Set X) (x : X), x ∈ A \\ (B ∩ C)', check: result => {
    const stages = result.plan.cues.filter(cue => cue.stage.relationKind);
    assert.deepEqual(stages.map(cue => cue.stage.relationKind), ['set-construction', 'set-construction', 'membership']);
    assert.deepEqual(stages.slice(0, 2).map(cue => relation(result, cue).setOperation), ['intersection', 'difference']);
    assert.deepEqual(stages.slice(0, 2).map(cue => cue.title), ['Form the intersection', 'Form the difference']);
    assert.ok(stages[1]!.detail.includes('outside'));
  } },
  { name: 'an abstract proposition wrapper stays above contained geometry', source: '∀ (F : Prop → Prop) (x : ℝ), F (x ∈ Metric.ball 0 1)', check: ({ plan, reading }) => {
    const stages = plan.cues.filter(cue => cue.panelId);
    assert.equal(stages[0]!.title, 'Read the complete clause');
    assert.deepEqual(stages[0]!.focusRelationIds, reading.panels[0]!.rootRelationIds);
    assert.deepEqual(stages.slice(1).map(cue => cue.stage.relationKind), ['metric-region', 'membership']);
    assert.ok(stages.slice(1).every(cue => cue.stage.kind === 'contained'));
  } },
  { name: 'a quantified proposition argument retains its local binder and wrapper', source: '∀ (F : Prop → Prop), F (∀ x : ℝ, x ∈ Metric.ball 0 1)', check: ({ plan, document }) => {
    const contained = plan.cues.filter(cue => cue.stage.kind === 'contained');
    assert.ok(contained.length >= 2);
    const local = document.objects.find(object => object.binder?.name === 'x')!;
    assert.ok(contained.every(cue => cue.contextObjectIds.includes(local.id)));
    assert.ok(contained.every(cue => cue.contextLabels.includes('Within a quantified expression')));
    assert.equal(introductions(plan).length, 1, 'Local expression quantification must not become an outer statement binder');
  } },
  { name: 'lambda body variables never leak into a following branch', source: '∀ (P : (ℝ → Prop) → Prop), P (fun x : ℝ => x = 0) ∧ True', check: ({ plan, document }) => {
    const local = document.objects.find(object => object.binder?.name === 'x')!;
    const inner = plan.cues.find(cue => cue.stage.relationKind === 'equality')!;
    assert.equal(inner.stage.kind, 'contained');
    assert.ok(inner.contextLabels.includes('Within a function body'));
    assert.ok(inner.contextObjectIds.includes(local.id));
    assert.ok(!plan.cues.at(-1)!.contextObjectIds.includes(local.id));
    assert.ok(!plan.cues.at(-1)!.retainedObjectIds.includes(local.id));
  } },
  { name: 'dependent family witnesses retain exact typed identities', source: '∀ (A : Type) (B : A → Type) (f : (a : A) → B a) (x : A), ∃ y : B x, f x = y', check: ({ plan }) => {
    const intro = introductions(plan);
    assert.deepEqual(intro.map(cue => cue.role), ['arbitrary', 'witness']);
    assert.deepEqual(intro[0]!.binders.map(binder => binder.name), ['A', 'B', 'f', 'x']);
    assert.equal(intro[1]!.binders[0]!.type, 'B x');
    assert.ok(intro[1]!.binders[0]!.dependsOn.includes(intro[0]!.binders.find(binder => binder.name === 'x')!.objectId!));
  } },
  { name: 'same-spelled branch-local binders remain separate choices', source: '∀ X : Type, (∀ x : X, x = x) ∨ (∀ x : X, x = x)', check: ({ plan }) => {
    const locals = introductions(plan).filter(cue => cue.binders.some(binder => binder.name === 'x'));
    assert.equal(locals.length, 2);
    assert.notEqual(locals[0]!.focusObjectIds[0], locals[1]!.focusObjectIds[0]);
    assert.ok(!locals[1]!.retainedObjectIds.includes(locals[0]!.focusObjectIds[0]!));
  } },
  { name: 'declaration signatures introduce context parameters', source: 'Function.Injective', options: { inputMode: 'declaration' }, check: ({ plan }) => {
    assert.ok(introductions(plan).every(cue => cue.role === 'parameter'));
    assert.ok(introductions(plan).every(cue => cue.detail.includes('parameters of this context')));
  } },
  { name: 'definition bodies preserve parameters outside their quantified condition', source: 'Function.Injective', options: { inputMode: 'declaration' }, body: true, check: ({ plan }) => {
    assert.deepEqual(introductions(plan).map(cue => cue.role), ['parameter', 'arbitrary']);
    assert.ok(plan.cues.some(cue => cue.roles.includes('assumption')));
    assert.ok(plan.cues.some(cue => cue.roles.includes('conclusion')));
  } },
];

let passed = 0, failed = 0;
const run = async (name: string, check: () => void | Promise<void>) => {
  try { await check(); passed++; console.log(`PASS ${name}`); }
  catch (error) { failed++; console.error(`FAIL ${name}: ${error instanceof Error ? error.message : String(error)}`); }
};
try {
  ({ GuidedReading } = await ssr.ssrLoadModule('/src/visual/GuidedReading.tsx'));
  ({ StatementReadingView } = await ssr.ssrLoadModule('/src/visual/StatementReadingView.tsx'));
  for (const test of cases) await run(test.name, async () => { const result = await compile(test.source, test.options, test.body); assertPlan(result); test.check(result); });
  await run('renaming binders preserves the guided construction topology', async () => {
    const first = await compile('∀ (X : Type) (f : X → X) (x : X), f x = x');
    const second = await compile('∀ (Carrier : Type) (transform : Carrier → Carrier) (point : Carrier), transform point = point');
    const topology = ({ plan }: Compiled) => plan.cues.map(cue => [cue.id, cue.intent, cue.role, cue.scopeId, cue.focusObjectIds, cue.focusRelationIds, cue.branchPath, cue.stage]);
    assert.deepEqual(topology(first), topology(second));
  });
  await run('the bounded guide keeps a source-ordered prefix of a large accepted statement', async () => {
    const conjunction = (count: number): string => count === 1 ? 'P' : `(${conjunction(Math.floor(count / 2))} ∧ ${conjunction(Math.ceil(count / 2))})`;
    const result = await compile(`∀ P : Prop, ${conjunction(130)}`);
    const bounded = compileReadingCues(result.reading, result.document);
    assert.ok(result.plan.totalCueCount > 250);
    assert.equal(bounded.cues.length, 250);
    assert.deepEqual(bounded.cues, result.plan.cues.slice(0, 250));
    assert.equal(bounded.omittedCueCount, result.plan.totalCueCount - 250);
    assert.ok(bounded.truncated && bounded.omittedNodeIds.length > 0);
    assert.ok(result.reading.nodes.every(node => bounded.cues.some(cue => cue.sourceNodeIds.includes(node.id)) || bounded.omittedNodeIds.includes(node.id)));
    assert.ok(result.reading.nodes.length > bounded.cues.length);
  });
  console.log(`${passed}/${passed + failed} native Lean → guided cues → context renderer checks passed.`);
  process.exitCode = failed ? 1 : 0;
} finally { backend.close?.(); await ssr.close(); }
