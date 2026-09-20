import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis, StatementNode } from '../src/core/types.ts';
import type { AnalysisOptions } from '../src/protocol.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
import { compileReading } from '../src/reading/index.ts';
import type { ReadingDocument, ReadingEdgeRole, ReadingNode } from '../src/reading/types.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
interface Compiled { analysis: Analysis; semantic: SemanticDocument; reading: ReadingDocument }
interface Case { name: string; source: string; options?: AnalysisOptions; definitionBody?: boolean; check: (result: Compiled) => void }
const flatten = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(flatten)];
const flattenReading = (node: ReadingNode): ReadingNode[] => [node, ...node.children.flatMap(flattenReading)];
const expectedEdge = (kind: StatementNode['kind'], index: number): ReadingEdgeRole => {
  switch (kind) {
    case 'forall': case 'exists': return 'body';
    case 'parameter': return 'result';
    case 'implies': return index === 0 ? 'assumption' : 'conclusion';
    case 'and': return 'conjunct';
    case 'or': return 'alternative';
    case 'iff': return index === 0 ? 'equivalence-left' : 'equivalence-right';
    case 'not': return 'negated';
    default: throw new Error(`Atomic node ${kind} must not have children`);
  }
};
const readingNode = (reading: ReadingDocument, id: string): ReadingNode => {
  const node = reading.nodes.find(n => n.id === id); assert.ok(node, `Reading omitted node ${id}`); return node;
};
const objectName = (semantic: SemanticDocument, id: string): string | undefined => semantic.objects.find(o => o.id === id)?.binder?.name;
const atomicRelations = ({ semantic, reading }: Compiled) => reading.panels.flatMap(panel => panel.rootRelationIds.map(id => semantic.relations.find(r => r.id === id)!));

function assertReadingInvariants({ analysis, semantic, reading }: Compiled): void {
  const sourceNodes = flatten(analysis.tree), sourceIds = sourceNodes.map(n => n.id);
  const leaves = sourceNodes.filter(n => !n.children.length);
  const semanticNodes = new Map(semantic.scopes.map(s => [s.id, s]));
  const relations = new Map(semantic.relations.map(r => [r.id, r]));
  const objectIds = new Set(semantic.objects.map(o => o.id));
  const sceneIds = new Set(semantic.scenes.map(s => s.id));
  const parents = new Map<string, string>();
  for (const node of sourceNodes) for (const child of node.children) parents.set(child.id, node.id);
  assert.equal(analysis.schemaVersion, 2);
  assert.equal(reading.root.id, analysis.tree.id);
  assert.equal(reading.root.kind, analysis.tree.kind, 'The reading root must be the statement, not a selected picture');
  assert.deepEqual(reading.nodes.map(n => n.id), sourceIds, 'Every source node must appear once in preorder');
  assert.deepEqual(flattenReading(reading.root).map(n => n.id), sourceIds, 'The nested composition must preserve the full source tree');
  assert.equal(new Set(reading.nodes.map(n => n.id)).size, reading.nodes.length);
  assert.deepEqual(reading.sequence.map(step => step.nodeId), sourceIds, 'The visual sequence must follow statement order rather than representation scores');
  assert.equal(new Set(reading.sequence.map(step => step.id)).size, reading.sequence.length);
  reading.sequence.forEach((step, index) => {
    const node = readingNode(reading, step.nodeId);
    assert.equal(step.ordinal, index + 1);
    assert.equal(step.kind, ['forall', 'exists', 'parameter'].includes(node.kind) ? 'binder' : node.children.length ? 'connective' : 'clause');
    assert.equal(step.panelId, node.panelId);
    const ancestors: string[] = [];
    let parent = parents.get(node.id);
    while (parent) { ancestors.push(parent); parent = parents.get(parent); }
    ancestors.reverse();
    assert.deepEqual(step.ancestorNodeIds, ancestors);
    assert.deepEqual(step.branchPath.map(position => position.nodeId), ancestors);
    step.branchPath.forEach((position, positionIndex) => {
      const parentNode = readingNode(reading, position.nodeId);
      const childId = ancestors[positionIndex + 1] ?? node.id;
      const childIndex = parentNode.children.findIndex(child => child.id === childId);
      assert.ok(childIndex >= 0);
      assert.equal(position.edge.role, expectedEdge(parentNode.kind, childIndex));
      assert.equal(position.edge.index, childIndex);
    });
  });
  assert.deepEqual(reading.panels.map(p => p.nodeId).sort(), leaves.map(n => n.id).sort(), 'Every atomic clause needs a panel');
  assert.deepEqual(reading.diagnostics, []);
  for (const source of sourceNodes) {
    const node = readingNode(reading, source.id);
    assert.equal(node.kind, source.kind);
    assert.equal(node.lean, source.lean);
    assert.equal(node.parentId, parents.get(node.id));
    assert.ok(node.phrase.trim());
    assert.deepEqual(node.children.map(c => c.id), source.children.map(c => c.id));
    assert.ok(semanticNodes.has(node.scopeId));
    node.children.forEach((child, index) => {
      assert.equal(child.edgeFromParent?.role, expectedEdge(source.kind, index));
      assert.equal(child.edgeFromParent?.index, index);
      assert.ok(child.edgeFromParent?.label.trim());
    });
    if (source.binder) {
      assert.equal(node.binder?.binderId, source.binder.id);
      assert.equal(node.binder?.role, source.binder.role);
      assert.equal(node.binder?.name, source.binder.name);
      const choice = semantic.choices.find(c => c.binderId === source.binder!.id);
      assert.ok(choice);
      assert.deepEqual(node.binder?.dependsOn, choice.dependsOn);
    }
    if (!source.children.length) assert.equal(reading.panels.find(p => p.id === node.panelId)?.nodeId, node.id);
    if (source.kind === 'iff') {
      assert.equal(node.directions?.length, 2);
      assert.deepEqual(node.directions?.map(d => [d.assumptionNodeId, d.conclusionNodeId]), [
        [source.children[0]!.id, source.children[1]!.id],
        [source.children[1]!.id, source.children[0]!.id],
      ]);
    }
  }
  for (const panel of reading.panels) {
    assert.equal(readingNode(reading, panel.nodeId).children.length, 0);
    panel.relationIds.forEach(id => assert.equal(relations.get(id)?.nodeId, panel.nodeId));
    panel.rootRelationIds.forEach(id => assert.ok(panel.relationIds.includes(id)));
    panel.objectIds.forEach(id => assert.ok(objectIds.has(id)));
    panel.sceneIds.forEach(id => assert.ok(sceneIds.has(id)));
    for (const group of panel.groups) {
      assert.ok(semanticNodes.has(group.scopeId));
      group.relationIds.forEach(id => assert.equal(relations.get(id)?.scopeId, group.scopeId, 'Relations cannot migrate between clause and lambda scopes'));
      group.rootRelationIds.forEach(id => assert.ok(group.relationIds.includes(id)));
      for (const connection of group.connections) {
        assert.ok(group.relationIds.includes(connection.fromRelationId));
        assert.ok(group.relationIds.includes(connection.toRelationId));
        assert.ok(objectIds.has(connection.objectId));
      }
    }
  }
  const groupedNodes: string[] = [];
  for (const group of reading.quantifierGroups) {
    assert.equal(group.nodeIds.length, group.binders.length);
    group.nodeIds.forEach((id, index) => {
      const node = readingNode(reading, id);
      assert.equal(node.kind, group.kind);
      assert.equal(node.binder?.binderId, group.binders[index]!.binderId);
      if (index) assert.equal(readingNode(reading, group.nodeIds[index - 1]!).children[0]?.id, id, 'Grouped binders must be adjacent in the same branch');
      groupedNodes.push(id);
    });
  }
  assert.deepEqual(groupedNodes.sort(), sourceNodes.filter(n => ['forall', 'exists', 'parameter'].includes(n.kind)).map(n => n.id).sort(), 'Every quantifier or parameter belongs to exactly one group');
  for (const selected of sourceNodes) {
    const focus = compileReading(semantic, { selectedNodeId: selected.id });
    assert.deepEqual(focus.nodes.map(n => n.id), sourceIds, 'Selection must not discard its logical envelope');
    assert.deepEqual(focus.panels.map(p => p.id), reading.panels.map(p => p.id));
    assert.deepEqual(focus.sequence, reading.sequence, 'Selecting a step must retain every alternative and its original position');
    assert.equal(focus.selection.nodeId, selected.id);
    const descendants = flatten(selected).map(n => n.id);
    assert.deepEqual([...focus.selection.descendantNodeIds].sort(), [...descendants].sort());
    const ancestors: string[] = [];
    let parent = parents.get(selected.id);
    while (parent) { ancestors.push(parent); parent = parents.get(parent); }
    assert.deepEqual([...focus.selection.ancestorNodeIds].sort(), ancestors.sort());
    const scope = semanticNodes.get(readingNode(focus, selected.id).scopeId)!;
    assert.deepEqual([...focus.selection.assumptionNodeIds].sort(), [...scope.assumptionNodeIds].sort());
    assert.deepEqual([...focus.selection.scopeObjectIds].sort(), [...scope.objectIds].sort());
    assert.deepEqual([...focus.selection.panelIds].sort(), focus.panels.filter(p => descendants.includes(p.nodeId)).map(p => p.id).sort());
  }
  assert.deepEqual(compileReading(semantic), reading, 'A reading must not depend on prior selection or exploration state');
}

async function compile(source: string, options?: AnalysisOptions, definitionBody = false): Promise<Compiled> {
  const output = await backend.analyze(source, undefined, options);
  assert.equal(output.ok, true, String(output.error ?? 'Native Lean elaboration failed'));
  const original = output as unknown as Analysis;
  let analysis = original;
  if (definitionBody) {
    assert.ok(original.definitionTree && original.definitionExpression, 'The selected definition needs a checked body');
    analysis = { ...original, tree: original.definitionTree, expression: original.definitionExpression };
  }
  const semantic = compileSemanticDocument(analysis), reading = compileReading(semantic);
  const result = { analysis, semantic, reading };
  assertReadingInvariants(result);
  if (definitionBody) assert.notEqual(original.tree.id, reading.root.id, 'Reading a body must leave the original signature distinct');
  return result;
}

const cases: Case[] = [
  {
    name: 'the arbitrary center encloses its dependent point witness',
    source: '∀ c : ℝ, ∃ p : ℝ, p ∈ Metric.ball c 1',
    check: ({ semantic, reading }) => {
      assert.deepEqual(reading.quantifierGroups.map(g => g.kind), ['forall', 'exists']);
      const witness = reading.quantifierGroups[1]!.binders[0]!;
      assert.deepEqual(witness.dependsOn.map(id => objectName(semantic, id)), ['c']);
      assert.equal(reading.root.children[0]!.kind, 'exists');
      assert.ok(reading.panels[0]!.sceneIds.length, 'Geometry is attached to the quantified clause');
    },
  },
  {
    name: 'a point witness chosen first stays outside the later universal center',
    source: '∃ p : ℝ, ∀ c : ℝ, p ∈ Metric.ball c 1',
    check: ({ reading }) => {
      assert.deepEqual(reading.quantifierGroups.map(g => g.kind), ['exists', 'forall']);
      assert.deepEqual(reading.quantifierGroups[0]!.binders[0]!.dependsOn, []);
      assert.equal(reading.root.children[0]!.kind, 'forall');
    },
  },
  {
    name: 'membership remains explicitly nested inside its negation',
    source: '∀ x : ℝ, ¬ (x ∈ Metric.ball 0 1)',
    check: ({ reading }) => {
      const not = reading.nodes.find(n => n.kind === 'not'); assert.ok(not);
      assert.equal(not.children[0]!.edgeFromParent?.role, 'negated');
      assert.equal(reading.panels[0]!.nodeId, not.children[0]!.id);
      assert.ok(not.children[0]!.context.some(c => /negation/i.test(c)));
    },
  },
  {
    name: 'a negated existential keeps its negation in the quantifier branch path',
    source: '∀ (X : Type) (P : X → Prop), ¬ ∃ x : X, P x',
    check: ({ reading }) => {
      const exists = reading.quantifierGroups.find(g => g.kind === 'exists'); assert.ok(exists);
      assert.ok(exists.branchPath.some(step => step.edge.role === 'negated'));
    },
  },
  {
    name: 'implication composes its premise and consequence around their shared point',
    source: '∀ x : ℝ, x ∈ Metric.ball 0 1 → x ∈ Metric.ball 0 2',
    check: ({ semantic, reading }) => {
      const implication = reading.nodes.find(n => n.kind === 'implies'); assert.ok(implication);
      assert.deepEqual(implication.children.map(n => n.edgeFromParent?.role), ['assumption', 'conclusion']);
      assert.equal(reading.panels.length, 2);
      assert.deepEqual(implication.children[0]!.assumptionNodeIds, []);
      assert.ok(implication.children[1]!.assumptionNodeIds.includes(implication.children[0]!.id));
      const pointId = semantic.objects.find(o => o.binder?.name === 'x')!.id;
      assert.ok(reading.panels.every(p => p.objectIds.includes(pointId)));
    },
  },
  {
    name: 'disjunction is an explicit pair of alternatives rather than simultaneous conditions',
    source: '∀ x : ℝ, x < 0 ∨ x > 1',
    check: ({ reading }) => {
      const either = reading.nodes.find(n => n.kind === 'or'); assert.ok(either);
      assert.deepEqual(either.children.map(n => n.edgeFromParent?.role), ['alternative', 'alternative']);
      assert.deepEqual(either.children.map(n => n.edgeFromParent?.index), [0, 1]);
      assert.ok(reading.panels.every(panel => either.children.some(child => child.id === panel.nodeId)));
    },
  },
  {
    name: 'conjunction retains both of its required clauses',
    source: '∀ (X : Type) (s t : Set X) (x : X), x ∈ s ∧ s ⊆ t',
    check: ({ reading }) => {
      const both = reading.nodes.find(n => n.kind === 'and'); assert.ok(both);
      assert.deepEqual(both.children.map(n => n.edgeFromParent?.role), ['conjunct', 'conjunct']);
      assert.equal(reading.panels.length, 2);
    },
  },
  {
    name: 'equivalence supplies two directions with exchanged assumptions',
    source: '∀ x : ℝ, x ∈ Metric.ball 0 1 ↔ |x| < 1',
    check: ({ reading }) => {
      const equivalence = reading.nodes.find(n => n.kind === 'iff'); assert.ok(equivalence);
      assert.equal(equivalence.directions?.length, 2);
      assert.equal(equivalence.directions![0]!.assumptionNodeId, equivalence.directions![1]!.conclusionNodeId);
      assert.equal(equivalence.directions![0]!.conclusionNodeId, equivalence.directions![1]!.assumptionNodeId);
      assert.ok(equivalence.children.every(n => n.assumptionNodeIds.length === 0));
    },
  },
  {
    name: 'function equality remains the clause and its graph is a supporting illustration',
    source: '∀ f : ℝ → ℝ, f = (fun x : ℝ => x * x)',
    check: result => {
      assert.equal(result.reading.root.kind, 'forall');
      assert.equal(result.reading.root.binder?.name, 'f');
      assert.ok(atomicRelations(result).some(r => r.kind === 'equality'));
      const panel = result.reading.panels[0]!;
      assert.ok(panel.sceneIds.some(id => result.semantic.scenes.find(s => s.id === id)?.kind === 'graph'));
      const equality = atomicRelations(result).find(r => r.kind === 'equality')!;
      assert.ok(equality.ports.some(port => objectName(result.semantic, port.objectId) === 'f'));
    },
  },
  {
    name: 'clause relations and lambda-body relations occupy separate scopes',
    source: '∀ (P : (ℝ → Prop) → Prop), P (fun x : ℝ => x = 0)',
    check: ({ semantic, reading }) => {
      const panel = reading.panels[0]!;
      assert.ok(panel.groups.some(g => g.role === 'clause'));
      assert.ok(panel.groups.some(g => g.role === 'local-expression'));
      const equality = semantic.relations.find(r => r.kind === 'equality'); assert.ok(equality);
      const local = panel.groups.find(g => g.relationIds.includes(equality.id)); assert.equal(local?.role, 'local-expression');
      assert.ok(local?.context.some(c => /function body/i.test(c)));
    },
  },
  {
    name: 'separate disjunction branches do not merge their universal binders',
    source: '∀ (X : Type) (P : X → Prop), (∀ x : X, P x) ∨ (∀ y : X, P y)',
    check: ({ reading }) => {
      const xGroup = reading.quantifierGroups.find(g => g.binders.some(b => b.name === 'x'));
      const yGroup = reading.quantifierGroups.find(g => g.binders.some(b => b.name === 'y'));
      assert.ok(xGroup && yGroup); assert.notEqual(xGroup.id, yGroup.id);
      assert.ok(xGroup.branchPath.some(step => step.edge.role === 'alternative' && step.edge.index === 0));
      assert.ok(yGroup.branchPath.some(step => step.edge.role === 'alternative' && step.edge.index === 1));
    },
  },
  {
    name: 'proof hypotheses are available only in the consequent and cannot leak to siblings',
    source: '∀ (X : Type) (P : X → Prop), ((∀ x : X, P x) → ∀ y : X, P y) ∧ (∃ z : X, P z)',
    check: ({ semantic, reading }) => {
      const implication = reading.nodes.find(n => n.kind === 'implies'); assert.ok(implication);
      const hypothesis = semantic.choices.find(c => c.nodeId === implication.id && c.role === 'assumption'); assert.ok(hypothesis);
      const premise = compileReading(semantic, { selectedNodeId: implication.children[0]!.id });
      const conclusion = compileReading(semantic, { selectedNodeId: implication.children[1]!.id });
      assert.ok(!premise.selection.scopeObjectIds.includes(hypothesis.objectId));
      assert.ok(conclusion.selection.scopeObjectIds.includes(hypothesis.objectId));
      const z = reading.nodes.find(n => n.binder?.name === 'z'); assert.ok(z);
      const sibling = compileReading(semantic, { selectedNodeId: z.id });
      assert.deepEqual(sibling.selection.assumptionNodeIds, []);
      assert.ok(!sibling.selection.scopeObjectIds.includes(hypothesis.objectId));
    },
  },
  {
    name: 'uninterpreted topology retains a full atomic reading rather than disappearing',
    source: '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y), Continuous f',
    check: ({ reading }) => {
      assert.equal(reading.panels.length, 1);
      assert.equal(reading.panels[0]!.coverage, 'structural');
      assert.ok(reading.panels[0]!.opaqueRegionIds.length);
      assert.equal(reading.panels[0]!.sceneIds.length, 0);
    },
  },
  {
    name: 'recognized children stay inside their uninterpreted parent clause',
    source: 'Set.Nonempty (Metric.ball (0 : ℝ) 1)',
    check: result => {
      assert.equal(result.reading.panels.length, 1);
      const panel = result.reading.panels[0]!;
      assert.equal(panel.coverage, 'partial');
      assert.ok(panel.opaqueRegionIds.length);
      assert.ok(panel.sceneIds.length);
      assert.ok(atomicRelations(result).some(r => r.fidelity === 'structural'));
    },
  },
  {
    name: 'abstract relations have typed quantifier structure without a numerical scenario',
    source: '∀ (X : Type) (R : X → X → Prop) (x : X), ∃ y : X, R x y',
    check: result => {
      assert.deepEqual(result.reading.quantifierGroups.map(g => g.kind), ['forall', 'exists']);
      assert.equal(result.reading.panels[0]!.sceneIds.length, 0);
      assert.ok(atomicRelations(result).some(r => r.kind === 'predicate' && r.fidelity === 'symbolic'));
    },
  },
  {
    name: 'abstract function composition reads without choosing coordinates',
    source: '∀ (A B C : Type) (f : A → B) (g : B → C) (x : A), (g ∘ f) x = g (f x)',
    check: result => {
      const { semantic, reading } = result;
      assert.equal(reading.panels.length, 1);
      assert.ok(atomicRelations(result).some(r => r.kind === 'equality'));
      for (const name of ['A', 'B', 'C', 'f', 'g', 'x']) assert.ok(reading.nodes.some(n => n.binder?.name === name));
      assert.ok(semantic.scenes.every(scene => scene.kind === 'mapping'), 'Abstract carriers cannot acquire numerical coordinates');
      assert.equal(semantic.objects.find(o => o.binder?.name === 'f')?.kind, 'function');
      assert.equal(semantic.objects.find(o => o.binder?.name === 'g')?.kind, 'function');
      assert.ok(reading.panels[0]!.rootRelationIds.some(id => semantic.relations.find(r => r.id === id)?.kind === 'equality'));
    },
  },
  {
    name: 'dependent morphism families retain their carriers and declared composition only',
    source: '∀ (Obj : Type) (Hom : Obj → Obj → Type) (comp : ∀ {A B C : Obj}, Hom B C → Hom A B → Hom A C) (A B C D : Obj) (f : Hom A B) (g : Hom B C) (h : Hom C D), comp h (comp g f) = comp (comp h g) f',
    check: result => {
      const { semantic, reading } = result;
      assert.equal(reading.panels.length, 1);
      assert.ok(atomicRelations(result).some(r => r.kind === 'equality'));
      for (const name of ['Obj', 'Hom', 'comp', 'A', 'B', 'C', 'D', 'f', 'g', 'h']) assert.ok(reading.nodes.some(n => n.binder?.name === name));
      assert.equal(semantic.objects.find(o => o.binder?.name === 'f')?.type, 'Hom A B');
      assert.equal(semantic.objects.find(o => o.binder?.name === 'h')?.type, 'Hom C D');
      assert.ok(semantic.scenes.every(scene => scene.kind === 'mapping'));
      assert.equal(semantic.relations.filter(r => r.kind === 'function-property').length, 0, 'Composition does not imply injectivity, invertibility, or other undeclared properties');
      assert.equal(result.analysis.validation, 'kernel-type-checked-statement', 'The supplied associativity condition has been typed, not proved');
    },
  },
  {
    name: 'imported theorem statements retain their complete quantified equivalence',
    source: 'Metric.mem_ball', options: { inputMode: 'declaration' },
    check: ({ analysis, reading }) => {
      assert.equal(analysis.provenance?.declaration?.kind, 'theorem');
      assert.equal(reading.root.kind, 'forall');
      assert.ok(reading.nodes.some(n => n.kind === 'iff'));
      assert.equal(reading.panels.length, 2);
    },
  },
  {
    name: 'a typed definition signature presents parameters without asserting a proposition',
    source: 'Function.comp', options: { inputMode: 'declaration' },
    check: ({ analysis, reading }) => {
      assert.equal(analysis.provenance?.inspected, 'signature');
      assert.equal(reading.root.kind, 'parameter');
      assert.ok(reading.quantifierGroups.every(g => g.kind === 'parameter'));
      assert.ok(reading.nodes.filter(n => n.binder).every(n => n.binder?.role === 'parameter'));
    },
  },
  {
    name: 'a definition body keeps its parameters outside its internal quantified condition',
    source: 'Function.Injective', options: { inputMode: 'declaration' }, definitionBody: true,
    check: ({ reading }) => {
      assert.equal(reading.root.id, 'definition');
      assert.deepEqual(reading.quantifierGroups.map(g => g.kind), ['parameter', 'forall']);
      assert.equal(reading.quantifierGroups[0]!.binders.length, 3);
      assert.equal(reading.quantifierGroups[1]!.binders.length, 2);
      assert.ok(reading.nodes.some(n => n.kind === 'implies'));
      assert.equal(reading.panels.length, 2);
    },
  },
];

let passed = 0, failed = 0;
try {
  for (const test of cases) {
    try {
      test.check(await compile(test.source, test.options, test.definitionBody));
      passed += 1; console.log(`PASS ${test.name}`);
    } catch (error) {
      failed += 1; console.error(`FAIL ${test.name}: ${error instanceof Error ? error.message : String(error)}`);
    }
  }
  console.log(`${passed}/${passed + failed} native Lean → semantic document → statement-first reading checks passed.`);
  process.exitCode = failed ? 1 : 0;
} finally {
  backend.close?.();
}
