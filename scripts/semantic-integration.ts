import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import { initialScenario, sliceGeometry } from '../src/core/index.ts';
import type { Analysis, Expr, StatementNode } from '../src/core/types.ts';
import type { AnalysisOptions } from '../src/protocol.ts';
import { compileSemanticDocument, planViews, selectedNodeIds } from '../src/semantic/index.ts';
import type { SemanticDocument, SemanticObject, SemanticRelation, ViewPlan } from '../src/semantic/types.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
interface Compiled { analysis: Analysis; document: SemanticDocument; plan: ViewPlan }
interface Case { name: string; source: string; options?: AnalysisOptions; check: (result: Compiled) => void }

const nodes = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(nodes)];
const relations = (document: SemanticDocument, kind: SemanticRelation['kind']) => document.relations.filter(r => r.kind === kind);
const objectFor = (document: SemanticDocument, id: string): SemanticObject => {
  const object = document.objects.find(o => o.id === id);
  assert.ok(object, `Missing referenced object ${id}`);
  return object;
};
const binderObject = (document: SemanticDocument, name: string): SemanticObject => {
  const object = document.objects.find(o => o.binder?.name === name);
  assert.ok(object, `Missing binder ${name}`);
  return object;
};

/** Mathematical relationships must not depend on printed binder names or source-node paths.
 * Retain all value arguments and their order; omit audited implementation arguments only. */
function relationshipFingerprint(document: SemanticDocument): string[] {
  const binderIds = new Map(document.choices.map((choice, i) => [choice.binderId, `binder:${i}`]));
  const key = (expr: Expr, local = binderIds, depth = 0): unknown => {
    switch (expr.kind) {
      case 'var': return ['var', local.get(expr.id) ?? expr.id];
      case 'const': return ['const', expr.name];
      case 'literal': return ['literal', expr.value];
      case 'sort': return ['sort', expr.name];
      case 'opaque': return ['opaque', expr.text];
      case 'app': return ['app', key(expr.fn, local, depth + 1), expr.args.filter((_, i) => !expr.argumentKinds || expr.argumentKinds[i] === 'value').map(arg => key(arg, local, depth + 1)), expr.metric ?? null, expr.dimension ?? null];
      case 'lambda': case 'forall': {
        const inner = new Map(local); inner.set(expr.binder.id, `local:${depth}`);
        return [expr.kind, key(expr.body, inner, depth + 1)];
      }
    }
  };
  return document.relations.map(relation => JSON.stringify([
    relation.kind, relation.fidelity, relation.pluginId,
    relation.ports.map(port => [port.role, key(objectFor(document, port.objectId).expression)]),
  ])).sort();
}

function assertDocumentInvariants({ analysis, document, plan }: Compiled): void {
  const allNodes = nodes(analysis.tree), nodeIds = new Set(allNodes.map(n => n.id));
  const leaves = allNodes.filter(n => !n.children.length);
  const objectIds = new Set(document.objects.map(o => o.id));
  const scopeIds = new Set(document.scopes.map(s => s.id));
  const relationIds = new Set(document.relations.map(r => r.id));
  const sceneIds = new Set(document.scenes.map(s => s.id));
  assert.equal(analysis.schemaVersion, 2);
  assert.equal(document.objects.length, objectIds.size, 'Object identities must be unique');
  assert.equal(document.relations.length, relationIds.size, 'Relation identities must be unique');
  assert.equal(document.scopes.length, scopeIds.size, 'Scope identities must be unique');
  assert.deepEqual(document.coverage.map(c => c.nodeId).sort(), leaves.map(n => n.id).sort(), 'Every logical leaf needs exactly one coverage record');
  assert.deepEqual(document.diagnostics, [], 'These bounded examples should not exhaust semantic traversal');
  for (const relation of document.relations) {
    assert.ok(nodeIds.has(relation.nodeId));
    assert.ok(scopeIds.has(relation.scopeId));
    assert.equal(relation.provenance.nodeId, relation.nodeId);
    assert.equal(relation.provenance.origin, 'elaborated-expression');
    relation.ports.forEach(port => assert.ok(objectIds.has(port.objectId)));
  }
  for (const scope of document.scopes) {
    assert.ok(nodeIds.has(scope.nodeId));
    if (scope.parentId) assert.ok(scopeIds.has(scope.parentId));
    scope.objectIds.forEach(id => assert.ok(objectIds.has(id)));
    scope.assumptionNodeIds.forEach(id => assert.ok(nodeIds.has(id)));
  }
  for (const choice of document.choices) {
    assert.ok(objectIds.has(choice.objectId));
    assert.ok(scopeIds.has(choice.scopeId));
    assert.ok(!choice.dependsOn.includes(choice.objectId));
    choice.dependsOn.forEach(id => assert.ok(choice.availableObjectIds.includes(id), 'Witness dependency escaped its lexical scope'));
  }
  for (const fragment of document.coverage) {
    fragment.relationIds.forEach(id => assert.ok(relationIds.has(id)));
    fragment.sceneIds.forEach(id => assert.ok(sceneIds.has(id)));
    fragment.objectIds.forEach(id => assert.ok(objectIds.has(id)));
  }
  assert.ok(plan.views.length > 0);
  assert.equal(plan.primaryViewId, plan.views[0]!.id);
  assert.equal(plan.views[0]!.score, Math.max(...plan.views.map(v => v.score)));
  assert.ok(plan.views.some(view => view.kind === 'semantic-map'), 'Every plan must retain the complete structural view');
  assert.equal(plan.coverage.fragments, leaves.length);
  assert.equal(plan.coverage.interpreted + plan.coverage.partial + plan.coverage.structural, leaves.length);
  assert.deepEqual(planViews(document), plan, 'Automatic view selection must be deterministic');
  for (const fragment of document.coverage) {
    const selected = planViews(document, { selectedNodeId: fragment.nodeId });
    assert.equal(selected.coverage.fragments, 1);
    assert.ok(selected.views.some(v => v.kind === 'semantic-map'));
    selected.views.filter(v => v.kind !== 'quantifier-flow').forEach(view => view.nodeIds.forEach(id => assert.ok(selectedNodeIds(analysis.tree, fragment.nodeId).has(id))));
  }
}

async function compile(source: string, options?: AnalysisOptions): Promise<Compiled> {
  const output = await backend.analyze(source, undefined, options);
  assert.equal(output.ok, true, String(output.error ?? 'Native Lean elaboration failed'));
  const analysis = output as unknown as Analysis;
  const document = compileSemanticDocument(analysis), plan = planViews(document);
  const result = { analysis, document, plan };
  assertDocumentInvariants(result);
  return result;
}

const cases: Case[] = [
  {
    name: 'abstract sets share typed objects across subset and membership conditions',
    source: '∀ (X : Type) (s t : Set X) (x : X), s ⊆ t → x ∈ s → x ∈ t',
    check: ({ document, plan }) => {
      assert.equal(relations(document, 'subset').length, 1);
      assert.equal(relations(document, 'membership').length, 2);
      assert.equal(binderObject(document, 's').kind, 'set');
      const x = binderObject(document, 'x').id;
      assert.ok(relations(document, 'membership').every(r => r.ports.some(p => p.role === 'element' && p.objectId === x)));
      assert.ok(plan.sharedObjectIds.includes(x));
      assert.equal(document.opaqueRegions.length, 0);
    },
  },
  {
    name: 'images and preimages compose through an abstract function',
    source: '∀ (X Y : Type) (f : X → Y) (s : Set X) (t : Set Y), Set.image f s ⊆ t ∧ s ⊆ Set.preimage f t',
    check: ({ document, plan }) => {
      assert.equal(relations(document, 'image').length, 1);
      assert.equal(relations(document, 'preimage').length, 1);
      assert.equal(relations(document, 'subset').length, 2);
      assert.equal(binderObject(document, 'f').kind, 'function');
      const f = binderObject(document, 'f').id;
      for (const relation of [...relations(document, 'image'), ...relations(document, 'preimage')]) assert.ok(relation.ports.some(p => p.role === 'function' && p.objectId === f));
      assert.ok(plan.sharedObjectIds.includes(f));
      assert.equal(plan.views[0]!.kind, 'relation-map');
      assert.ok(document.coverage.every(c => c.status === 'interpreted'));
    },
  },
  {
    name: 'composition retains explicit applications and any uninterpreted operator',
    source: '∀ (X Y Z : Type) (f : X → Y) (g : Y → Z) (x : X), g (f x) = (g ∘ f) x',
    check: ({ document }) => {
      assert.equal(relations(document, 'equality').length, 1);
      assert.ok(relations(document, 'application').length >= 2);
      assert.ok(document.objects.some(o => o.expression.kind === 'const' && o.expression.name === 'Function.comp'));
      assert.ok(document.coverage.every(c => c.status !== 'structural'));
    },
  },
  {
    name: 'arbitrary curried relations preserve their argument order',
    source: '∀ (X : Type) (R : X → X → Prop) (x y : X), R x y ∨ R y x',
    check: ({ document }) => {
      const predicates = relations(document, 'predicate').filter(r => r.fidelity === 'symbolic');
      assert.equal(predicates.length, 2);
      assert.deepEqual(predicates.map(r => r.ports.map(p => p.role)), [['relation', 'argument 1', 'argument 2'], ['relation', 'argument 1', 'argument 2']]);
      assert.equal(predicates[0]!.ports[1]!.objectId, predicates[1]!.ports[2]!.objectId);
      assert.equal(predicates[0]!.ports[2]!.objectId, predicates[1]!.ports[1]!.objectId);
      assert.equal(document.scenes.length, 0);
    },
  },
  {
    name: 'partially applied equality is a function rather than a complete relation',
    source: '∀ (X : Type) (x : X), Function.Injective (@Eq X x)',
    check: ({ document }) => {
      assert.equal(relations(document, 'function-property').length, 1);
      assert.equal(relations(document, 'equality').length, 0);
    },
  },
  {
    name: 'partially applied image retains its function type without inventing a set argument',
    source: '∀ (X Y : Type) (f : X → Y), Function.Injective (Set.image f)',
    check: ({ document }) => {
      assert.equal(relations(document, 'function-property').length, 1);
      assert.equal(relations(document, 'image').length, 0);
    },
  },
  {
    name: 'a partially applied ball constructor cannot authorize a metric region or plot',
    source: '∀ (P : (ℝ → Set ℝ) → Prop), P (Metric.ball (0 : ℝ))',
    check: ({ document, plan }) => {
      assert.equal(relations(document, 'metric-region').length, 0, 'A radius is required before the constructor denotes a metric region');
      assert.equal(document.scenes.filter(s => s.kind === 'ball').length, 0, 'No audited complete metric region should receive a numerical scene here');
      assert.equal(plan.views.filter(v => v.kind === 'ball').length, 0);
    },
  },
  {
    name: 'unknown topology remains typed and covered without numerical invention',
    source: '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y), Continuous f',
    check: ({ document, plan }) => {
      assert.equal(binderObject(document, 'f').kind, 'function');
      assert.ok(document.opaqueRegions.length > 0);
      assert.equal(plan.coverage.structural, 1);
      assert.equal(document.scenes.length, 0);
      assert.equal(plan.views[0]!.kind, 'semantic-map');
    },
  },
  {
    name: 'recognized geometry survives under an uninterpreted parent definition',
    source: 'Set.Nonempty (Metric.ball (0 : ℝ) 1)',
    check: ({ document }) => {
      const region = relations(document, 'metric-region')[0];
      assert.ok(region);
      assert.equal(document.coverage[0]!.status, 'partial');
      assert.ok(document.opaqueRegions.some(o => o.supportedRelationIds.includes(region.id)));
      assert.ok(document.scenes.some(s => s.kind === 'ball'));
    },
  },
  {
    name: 'a replacement set membership instance receives only structural interpretation',
    source: '∀ (X : Type) (m : Membership X (Set X)) (x : X) (s : Set X), @Membership.mem X (Set X) m s x',
    check: ({ document, plan }) => {
      assert.equal(relations(document, 'membership').length, 0);
      assert.equal(plan.coverage.structural, 1);
      assert.ok(document.opaqueRegions.length > 0);
    },
  },
  {
    name: 'a custom metric keeps symbolic regions but cannot authorize a plot',
    source: '∀ (m : PseudoMetricSpace (ℝ × ℝ)) (p c : ℝ × ℝ), p ∈ @Metric.ball (ℝ × ℝ) m c 1',
    check: ({ document, plan }) => {
      assert.equal(relations(document, 'membership').length, 1);
      assert.equal(relations(document, 'metric-region').length, 1);
      assert.ok(relations(document, 'metric-region')[0]!.conditions.some(c => c.includes('no audited numerical')));
      assert.equal(document.scenes.filter(s => s.kind === 'ball').length, 0, 'No audited complete metric region should receive a numerical scene here');
      assert.equal(plan.views.filter(v => v.kind === 'ball').length, 0);
    },
  },
  {
    name: 'a 21-dimensional sphere retains metric geometry and an explicit slice contract',
    source: '∀ p : EuclideanSpace ℝ (Fin 21), p ∈ Metric.sphere 0 2',
    check: ({ analysis, document, plan }) => {
      const ball = document.scenes.find(s => s.kind === 'ball');
      assert.ok(ball?.kind === 'ball');
      assert.equal(ball.dimension, 21);
      assert.equal(ball.metric, 'euclideanN');
      const slice = sliceGeometry(ball, initialScenario(analysis.tree), { axes: [2, 17] });
      assert.equal(slice.status, 'geometry');
      if (slice.status === 'geometry') {
        assert.equal(slice.ambientDimension, 21);
        assert.equal(slice.intrinsicDimension, 20);
        assert.equal(slice.isSlice, true);
      }
      assert.equal(plan.views[0]!.kind, 'ball');
      assert.ok(plan.views[0]!.conditions.some(c => c.includes('21-dimensional') && c.includes('not projected')));
    },
  },
  {
    name: 'implication assumptions and witness dependencies stay within their branch',
    source: '∀ (X : Type) (R : X → X → Prop), ((∀ x : X, R x x) → ∀ x : X, ∃ y : X, R x y) ∨ (∃ z : X, R z z)',
    check: ({ analysis, document }) => {
      const implication = nodes(analysis.tree).find(n => n.kind === 'implies');
      assert.ok(implication);
      const premiseIds = selectedNodeIds(analysis.tree, implication.children[0]!.id);
      const conclusionIds = selectedNodeIds(analysis.tree, implication.children[1]!.id);
      const proofChoice = document.choices.find(c => c.nodeId === implication.id && c.role === 'assumption');
      assert.ok(proofChoice);
      for (const scope of document.scopes.filter(s => premiseIds.has(s.nodeId))) assert.ok(!scope.objectIds.includes(proofChoice.objectId));
      for (const scope of document.scopes.filter(s => conclusionIds.has(s.nodeId))) {
        assert.ok(scope.objectIds.includes(proofChoice.objectId));
        assert.ok(scope.assumptionNodeIds.includes(implication.children[0]!.id));
      }
      const z = binderObject(document, 'z');
      const zChoice = document.choices.find(c => c.objectId === z.id)!;
      assert.ok(!zChoice.availableObjectIds.includes(proofChoice.objectId));
      const branchBinders = document.choices.filter(c => conclusionIds.has(c.nodeId));
      assert.ok(branchBinders.every(c => !zChoice.availableObjectIds.includes(c.objectId)));
      const zScope = document.scopes.find(s => s.id === zChoice.scopeId)!;
      assert.deepEqual(zScope.assumptionNodeIds, []);
      assert.ok(zScope.context.includes('Alternative 2 of a disjunction'));
    },
  },
  {
    name: 'lambda body relations have their own typed input scope',
    source: '∀ (F : (ℝ → ℝ) → ℝ) (x : ℝ), F (fun t : ℝ => t * t + x) = x',
    check: ({ document }) => {
      const input = document.choices.find(c => c.role === 'lambda');
      assert.ok(input);
      const scope = document.scopes.find(s => s.id === input.scopeId)!;
      assert.ok(scope.context.includes('Within a function body'));
      assert.ok(scope.objectIds.includes(input.objectId));
      assert.ok(input.availableObjectIds.includes(binderObject(document, 'x').id));
    },
  },
  {
    name: 'declaration lookup preserves theorem statements and imported provenance',
    source: 'Metric.mem_ball', options: { inputMode: 'declaration' },
    check: ({ analysis, document }) => {
      assert.equal(analysis.provenance?.inspected, 'statement');
      assert.equal(analysis.provenance?.declaration?.kind, 'theorem');
      assert.equal(analysis.provenance?.declaration?.module, 'Mathlib.Topology.MetricSpace.Pseudo.Defs');
      assert.equal(relations(document, 'membership').length, 1);
      assert.equal(relations(document, 'metric-region').length, 1);
      assert.ok(document.scopes.some(s => s.kind === 'iff'));
    },
  },
  {
    name: 'definition signatures remain parameters and expose a separate lambda body',
    source: 'Function.comp', options: { inputMode: 'declaration' },
    check: ({ analysis, document, plan }) => {
      assert.equal(analysis.provenance?.inspected, 'signature');
      assert.ok(document.choices.length > 0);
      assert.ok(document.choices.every(c => c.role === 'parameter'));
      assert.ok(document.choices.every(c => !c.explanation.startsWith('An arbitrary')));
      assert.equal(analysis.definitionExpression?.kind, 'lambda');
      assert.ok(plan.views.some(v => v.kind === 'quantifier-flow'));
      assert.equal(document.scenes.length, 0);
    },
  },
  {
    name: 'definition bodies reveal their parameterized logic without asserting the signature',
    source: 'Function.Injective', options: { inputMode: 'declaration' },
    check: ({ analysis }) => {
      assert.ok(analysis.definitionTree && analysis.definitionExpression);
      const bodyAnalysis: Analysis = { ...analysis, tree: analysis.definitionTree, expression: analysis.definitionExpression };
      const document = compileSemanticDocument(bodyAnalysis), plan = planViews(document);
      assertDocumentInvariants({ analysis: bodyAnalysis, document, plan });
      assert.equal(document.tree.kind, 'parameter');
      assert.equal(document.tree.id, 'definition');
      assert.equal(document.choices.filter(c => c.role === 'parameter').length, 3);
      assert.equal(document.choices.filter(c => c.role === 'universal').length, 2);
      assert.equal(binderObject(document, 'f').binder?.role, 'parameter');
      assert.equal(relations(document, 'equality').length, 2);
      assert.ok(document.scopes.some(s => s.kind === 'implies'));
      assert.equal(analysis.tree.kind, 'parameter', 'Viewing the body must not mutate the original signature');
      assert.equal(analysis.provenance?.inspected, 'signature');
    },
  },
  {
    name: 'selected definition expansion creates scopes without claiming a proof',
    source: '∀ (X Y : Type) (f : X → Y), Function.Injective f',
    options: { expansion: { constants: ['Function.Injective'], maxDepth: 2 } },
    check: ({ analysis, document }) => {
      assert.ok(nodes(analysis.tree).some(n => n.expansion?.constant === 'Function.Injective'));
      assert.equal(relations(document, 'function-property').length, 0);
      assert.equal(relations(document, 'equality').length, 2);
      assert.ok(document.scopes.some(s => s.kind === 'implies'));
      assert.equal(analysis.validation, 'kernel-type-checked-statement');
      assert.ok(document.choices.filter(c => c.role === 'universal').length >= 5);
    },
  },
];

let passed = 0, failed = 0;
async function check(name: string, action: () => Promise<void>): Promise<void> {
  try { await action(); passed += 1; console.log(`PASS ${name}`); }
  catch (error) { failed += 1; console.error(`FAIL ${name}: ${error instanceof Error ? error.message : String(error)}`); }
}
try {
  for (const test of cases) await check(test.name, async () => test.check(await compile(test.source, test.options)));
  await check('renaming types, sets, maps, and points preserves the recognized relationships', async () => {
    const left = await compile('∀ (X Y : Type) (f : X → Y) (s : Set X) (t : Set Y) (x : X), x ∈ s ∧ Set.image f s ⊆ t ∧ f x ∈ t');
    const right = await compile('∀ (A B : Type) (h : A → B) (u : Set A) (v : Set B) (p : A), p ∈ u ∧ Set.image h u ⊆ v ∧ h p ∈ v');
    assert.deepEqual(relationshipFingerprint(left.document), relationshipFingerprint(right.document));
    assert.deepEqual(left.document.choices.map(c => [c.role, c.dependsOn]), right.document.choices.map(c => [c.role, c.dependsOn]));
    assert.equal(left.plan.views[0]!.kind, right.plan.views[0]!.kind);
  });
  await check('conjunction regrouping preserves mathematical objects and relationships', async () => {
    const prefix = '∀ (X : Type) (s t : Set X) (x : X), ';
    const left = await compile(prefix + '(x ∈ s ∧ s ⊆ t) ∧ x ∈ t');
    const right = await compile(prefix + 'x ∈ s ∧ (s ⊆ t ∧ x ∈ t)');
    assert.deepEqual(relationshipFingerprint(left.document), relationshipFingerprint(right.document));
    assert.deepEqual(left.document.objects.filter(o => o.binder).map(o => [o.id, o.kind]), right.document.objects.filter(o => o.binder).map(o => [o.id, o.kind]));
    assert.deepEqual([...left.plan.sharedObjectIds].sort(), [...right.plan.sharedObjectIds].sort());
    assert.deepEqual(left.plan.coverage, right.plan.coverage);
  });
  await check('expansion settings do not leak to later requests in the persistent worker', async () => {
    const fresh = await compile('∀ (X Y : Type) (f : X → Y), Function.Injective f');
    assert.equal(relations(fresh.document, 'function-property').length, 1);
    assert.equal(nodes(fresh.analysis.tree).filter(n => n.expansion).length, 0);
  });
  console.log(`${passed}/${passed + failed} native Lean → semantic document → automatic view checks passed.`);
  process.exitCode = failed ? 1 : 0;
} finally {
  backend.close?.();
}
