import assert from 'node:assert/strict';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/compiler.ts';
import { compileSetConstruction } from '../src/set-constructions/model.ts';

const backend = createWorkerBackend({ rootDir: process.cwd() });
const cases = [
  { name: 'nested union and intersection under membership', source: '∀ (X : Type) (A B C : Set X) (x : X), x ∈ ((A ∪ B) ∩ C)', operations: ['intersection', 'union'], root: 'membership' },
  { name: 'difference and complement under inclusion', source: '∀ (X : Type) (A B C : Set X), A \\ B ⊆ Cᶜ', operations: ['difference', 'complement'], root: 'subset' },
  { name: 'composed set equality', source: '∀ (X : Type) (A B C : Set X), A ∩ (B ∪ C) = (A ∩ B) ∪ (A ∩ C)', operations: ['intersection', 'union', 'union', 'intersection', 'intersection'], root: 'equality' },
  { name: 'direct imported constructors', source: '∀ (X : Type) (A B : Set X), Set.diff (Set.union A B) (Set.compl A) = Set.inter A B', operations: ['difference', 'union', 'complement', 'intersection'], root: 'equality' },
  { name: 'a local overloaded union instance stays uninterpreted', source: '∀ (X : Type) (u : Union (Set X)) (A B : Set X) (x : X), x ∈ @Union.union (Set X) u A B', operations: [], root: 'membership' },
  { name: 'partially applied union is not a completed construction', source: '∀ (X : Type) (A : Set X) (P : (Set X → Set X) → Prop), P (Set.union A)', operations: [], root: 'predicate' },
  { name: 'image of a union keeps source and target memberships distinct', source: '∀ (X Y : Type) (f : X → Y) (A B : Set X) (C : Set Y), Set.image f (A ∪ B) ⊆ C', operations: ['union'], root: 'subset' },
];
let failed = 0;
try {
  for (const test of cases) {
    try {
      const output = await backend.analyze(test.source);
      assert.equal(output.ok, true, JSON.stringify(output));
      const document = compileSemanticDocument(output as unknown as Analysis);
      const constructors = document.relations.filter(relation => relation.kind === 'set-construction');
      assert.deepEqual(constructors.map(relation => relation.setOperation), test.operations);
      const root = document.relations.find(relation => relation.provenance.expressionPath === 'expression');
      assert.ok(root);
      assert.equal(root.kind, test.root);
      const model = compileSetConstruction(document, root);
      if (test.operations.length) {
        assert.ok(model);
        assert.equal(model.relation.id, root.id);
        assert.ok(model.steps.every(step => step.relationId && document.relations.some(relation => relation.id === step.relationId && relation.scopeId === root.scopeId)));
        assert.ok(constructors.every(relation => relation.ports.at(-1)?.role === 'result'));
        if (test.name.startsWith('image')) assert.equal(model.atoms.length, 2);
        if (test.name === 'composed set equality') assert.ok(model.regions?.every(region => !region.highlighted), 'Distributivity leaves no forbidden membership combinations');
      } else assert.equal(model, undefined);
      console.log(`PASS ${test.name}`);
    } catch (error) { failed++; console.error(`FAIL ${test.name}: ${error instanceof Error ? error.message : String(error)}`); }
  }
} finally { backend.close?.(); }
if (failed) process.exitCode = 1;
console.log(`${cases.length - failed}/${cases.length} native set construction checks passed.`);
