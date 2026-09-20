import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(root, '.local/config.json'), 'utf8'));
const tests = [
  ['polymorphic constants retain their exact universe arguments', '∀ (A : Type) (B : Type 1) (a : A) (b : B), a = a ∧ b = b', result => {
    const equalities = collect(result.originalExpression, x => x.kind === 'const' && x.name === 'Eq');
    assert.ok(equalities.some(x => JSON.stringify(x.levels) === '["1"]'));
    assert.ok(equalities.some(x => JSON.stringify(x.levels) === '["2"]'));
  }],
  ['product ball has the canonical sup metric', '∀ (ε : ℝ) (c P : ℝ × ℝ), 0 < ε → P ∈ Metric.ball c ε → dist P c < ε', result => metric(result, 'Metric.ball', 'sup2', 2)],
  ['Euclidean ball uses L2', '∀ p : EuclideanSpace ℝ (Fin 2), p ∈ Metric.closedBall 0 1', result => metric(result, 'Metric.closedBall', 'euclidean2', 2)],
  ['a 4D sphere preserves its ambient dimension', '∀ p : EuclideanSpace ℝ (Fin 4), p ∈ Metric.sphere 0 1', result => metric(result, 'Metric.sphere', 'euclideanN', 4)],
  ['finite real functions use the sup metric', '∀ p : Fin 3 → ℝ, p ∈ Metric.sphere 0 1', result => metric(result, 'Metric.sphere', 'supN', 3)],
  ['quantifier dependencies preserve source order', '∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > 0 ∧ ∀ x : ℝ, |x| < δ → |x ^ 2| < ε', result => {
    const binders = collect(result.tree, x => x.binder && x.kind === 'exists').map(x => x.binder);
    assert.equal(binders[0].name, 'δ');
    assert.deepEqual(binders[0].dependsOn, ['n.binder']);
    for (const node of collect(result.tree, x => x.kind === 'implies' && x.children)) assert.equal(node.binder.role, 'assumption');
  }],
  ['bounded quantifiers elaborate into explicit logical structure', '∀ ε > (0 : ℝ), ∃ δ > (0 : ℝ), ∀ x ∈ Metric.ball (0 : ℝ) δ, |x| < ε', result => {
    metric(result, 'Metric.ball', 'real', 1);
    assert.equal(result.tree.kind, 'forall');
    assert.equal(result.tree.children[0].kind, 'implies');
    assert.equal(result.tree.children[0].children[1].kind, 'exists');
  }],
  ['function lambdas retain typed bodies', '∀ x : ℝ, (fun t : ℝ => t * t) x ≥ 0', result => assert.ok(collect(result, x => x.kind === 'lambda' && x.binder.type === 'ℝ').length)],
  ['tuples and projections elaborate', '∀ p : ℝ × ℝ, p ∈ Metric.ball (0, 0) 1 → p.1 ≤ 1', result => metric(result, 'Metric.ball', 'sup2', 2)],
  ['custom metrics are not mislabeled Euclidean or sup', '∀ (m : PseudoMetricSpace (ℝ × ℝ)) (p c : ℝ × ℝ), p ∈ @Metric.ball (ℝ × ℝ) m c 1', result => {
    const apps = applications(result, 'Metric.ball');
    assert.ok(apps.length);
    for (const app of apps) { assert.equal(app.metric, 'unknown'); assert.equal(app.standard, false); }
  }],
  ['custom arithmetic is not evaluated as standard real arithmetic', '∀ (h : HAdd ℝ ℝ ℝ) (x : ℝ), @HAdd.hAdd ℝ ℝ ℝ h x x = x', result => {
    const apps = applications(result, 'HAdd.hAdd');
    assert.ok(apps.length);
    for (const app of apps) assert.equal(app.standard, false);
  }],
  ['abstract metric spaces remain typed but unrendered', '∀ (X : Type) [MetricSpace X] (c p : X) (ε : ℝ), p ∈ Metric.ball c ε → dist p c < ε', result => {
    const apps = applications(result, 'Metric.ball');
    assert.ok(apps.length);
    for (const app of apps) assert.equal(app.metric, 'unknown');
  }],
  ['supported fragments survive beside abstract predicates', '∀ (X : Type) (f : X → ℝ), (∀ x : X, f x ≥ 0) → ∀ p : ℝ × ℝ, p ∈ Metric.ball (0, 0) 1', result => metric(result, 'Metric.ball', 'sup2', 2)],
  ['False is a well-typed statement, not a proof', 'False', result => {
    assert.equal(result.validation, 'kernel-type-checked-statement');
    assert.equal(result.pretty, 'False');
    assert.equal(result.type, 'Prop');
  }],
  ['shadowed variables retain distinct identities', '∀ x : ℝ, x > 0 → ∃ x : ℝ, x < 0', result => {
    const universal = result.tree.binder;
    const existential = result.tree.children[0].children[1].binder;
    assert.equal(universal.name, existential.name);
    assert.notEqual(universal.id, existential.id);
    assert.deepEqual(existential.dependsOn, [universal.id]);
  }],
  ['general sets keep element types and typed subset structure', '∀ (X : Type) (A B : Set X), A ⊆ B → ∀ x ∈ A, x ∈ B', result => {
    assert.equal(result.schemaVersion, 2);
    const sets = collect(result.tree, x => x.typeDescriptor?.kind === 'set');
    assert.ok(sets.length >= 2);
    assert.equal(sets[0].typeDescriptor.element.lean, 'X');
    assert.ok(applications(result, 'HasSubset.Subset').every(x => x.standard === true));
    assert.ok(applications(result, 'Membership.mem').every(x => x.standard === true));
  }],
  ['set builders, intersections and function composition elaborate', '∀ (A B : Set ℝ) (f g : ℝ → ℝ), (∀ x ∈ A ∩ B, (g ∘ f) x ∈ { y : ℝ | 0 < y })', result => {
    assert.ok(applications(result, 'Function.comp').length);
    assert.ok(applications(result, 'setOf').length);
    assert.ok(applications(result, 'Inter.inter').length);
  }],
  ['set lattice notation retains canonical meanings on abstract types', '∀ (X : Type) (s t : Set X), s \\ t ⊆ s ∧ s ∪ t = t ∪ s ∧ s ∩ sᶜ = ∅', result => {
    assert.ok(applications(result, 'SDiff.sdiff').length);
    for (const name of ['SDiff.sdiff', 'Union.union', 'Inter.inter']) {
      assert.ok(applications(result, name).every(x => x.standard === true));
    }
  }],
  ['custom set membership retains its replacement instance boundary', '∀ (X : Type) (m : Membership X (Set X)) (x : X) (s : Set X), @Membership.mem X (Set X) m s x', result => {
    const apps = applications(result, 'Membership.mem');
    assert.ok(apps.length);
    assert.ok(apps.every(x => x.standard === false));
  }],
  ['curried abstract relations retain their typed arity', '∀ (X : Type) (R : X → X → Prop), ∀ x : X, R x x', result => {
    const relation = result.tree.children[0].binder;
    assert.equal(relation.typeDescriptor.kind, 'relation');
    assert.equal(relation.typeDescriptor.codomain.kind, 'relation');
    assert.equal(relation.typeDescriptor.domain.lean, 'X');
  }],
  ['arbitrary topology stays structural without invented geometry', '∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (f : X → Y), Continuous f', result => {
    const f = collect(result.tree, x => x.binder?.name === 'f')[0].binder;
    assert.equal(f.typeDescriptor.kind, 'map');
    assert.equal(f.typeDescriptor.domain.lean, 'X');
    assert.ok(applications(result, 'Continuous').length);
  }],
  ['high-dimensional metadata is not restricted to a preset menu', '∀ p : EuclideanSpace ℝ (Fin 21), p ∈ Metric.sphere 0 1', result => metric(result, 'Metric.sphere', 'euclideanN', 21)],
  ['native source coordinates remain exact UTF-8 byte ranges', '∀ ε : ℝ, ε > 0 → ∃ δ : ℝ, δ > ε', result => {
    assert.ok(result.sourceTerms.length > 0);
    const source = Buffer.from(result.source, 'utf8');
    for (const term of result.sourceTerms) {
      assert.equal(term.origin, 'lean-infotree');
      assert.ok(term.startByte >= 0 && term.endByte <= source.length && term.endByte > term.startByte);
      assert.equal(Buffer.from(source.subarray(term.startByte, term.endByte).toString('utf8')).length, term.endByte - term.startByte);
    }
    assert.ok(result.sourceTerms.some(term => source.subarray(term.startByte, term.endByte).toString('utf8') === 'ε'));
  }],
  ['application arguments distinguish values from instances and types', '∀ x : ℝ, x + x = x', result => {
    const app = applications(result, 'HAdd.hAdd')[0];
    assert.equal(app.argumentKinds.length, app.args.length);
    assert.ok(app.argumentKinds.includes('instance'));
    assert.ok(app.argumentKinds.includes('type'));
    assert.equal(app.argumentKinds.at(-1), 'value');
  }],
  ['definition expansion exposes scoped logical structure', { source: '∀ (X Y : Type) (f : X → Y), Function.Injective f', expansion: { constants: ['Function.Injective'], maxDepth: 2 } }, result => {
    const expanded = collect(result.tree, x => x.expansion?.constant === 'Function.Injective')[0];
    assert.ok(expanded);
    assert.equal(expanded.expansion.definitionalEquality, true);
    assert.equal(expanded.kind, 'forall');
    assert.equal(expanded.scope.length, 3);
    assert.ok(collect(expanded, x => x.kind === 'implies' && x.children).length);
    assert.ok(result.definitions.some(x => x.name === 'Function.Injective' && x.canExpand));
  }],
  ['ordinary imported theorems expose their statements and module provenance', { source: 'Metric.mem_ball', inputMode: 'declaration' }, result => {
    assert.equal(result.provenance.declaration.kind, 'theorem');
    assert.equal(result.provenance.declaration.module, 'Mathlib.Topology.MetricSpace.Pseudo.Defs');
    assert.equal(result.provenance.inspected, 'statement');
    assert.equal(result.type, 'Prop');
    assert.ok(collect(result.tree, x => x.kind === 'iff' && x.children).length);
    assert.deepEqual(result.sourceTerms, []);
    for (const node of collect(result.tree, x => x.binder)) assert.ok(!node.binder.name.includes('_@'));
    assert.equal(result.definitionTree, null);
  }],
  ['definition signatures preserve parameters without asserting quantification', { source: 'Function.comp', inputMode: 'declaration' }, result => {
    assert.equal(result.provenance.inspected, 'signature');
    assert.equal(result.validation, 'kernel-type-checked-declaration-type');
    assert.equal(result.tree.kind, 'parameter');
    assert.equal(result.tree.binder.role, 'parameter');
    assert.equal(collect(result.tree, x => x.kind === 'forall' && x.children).length, 0);
    assert.equal(result.definitionExpression.kind, 'lambda');
    assert.equal(result.definitionBodyStatus, 'available');
    assert.equal(result.definitionTree.kind, 'parameter');
    assert.equal(result.definitionTree.id, 'definition');
    assert.equal(result.definitionTree.expression.kind, 'lambda');
    assert.ok(result.definitions.some(x => x.name === 'Function.comp'));
  }],
  ['universe-polymorphic definition bodies preserve typed abstraction', { source: 'Function.Injective', inputMode: 'declaration' }, result => {
    assert.equal(result.provenance.inspected, 'signature');
    assert.equal(result.definitionExpression.kind, 'lambda');
    assert.ok(collect(result.definitionExpression, x => x.kind === 'forall').length);
    assert.equal(result.definitionTree.kind, 'parameter');
    assert.equal(result.definitionTree.children[0].children[0].binder.name, 'f');
    assert.equal(result.definitionTree.children[0].children[0].binder.role, 'parameter');
    assert.ok(collect(result.definitionTree, x => x.kind === 'forall' && x.children).length);
    assert.ok(collect(result.definitionTree, x => x.kind === 'implies' && x.children).length);
  }],
  ['declaration mode rejects commands and compound inputs', { source: 'Function.comp Nat.succ', inputMode: 'declaration' }, /one exact imported declaration name/],
  ['declaration mode does not silently resolve unknown names', { source: 'StatementLens.nonexistent', inputMode: 'declaration' }, /Unknown imported declaration/],
  ['theorem proofs cannot be unfolded as definitions', { source: 'True', expansion: { constants: ['Metric.mem_ball'], maxDepth: 1 } }, /Only safe imported definitions/],
  ['unknown definition expansion is rejected', { source: 'True', expansion: { constants: ['Missing.definition'], maxDepth: 1 } }, /Unknown imported definition/],
  ['definition expansion depth is bounded', { source: 'True', expansion: { constants: [], maxDepth: 10 } }, /between 1 and 3/],
  ['definition expansion depth cannot silently accept malformed data', { source: 'True', expansion: { constants: [], maxDepth: 'two' } }, /must be an integer/],
  ['independent requests retain the original unexpanded environment', '∀ (X Y : Type) (f : X → Y), Function.Injective f', result => {
    assert.equal(collect(result.tree, x => x.expansion).length, 0);
    assert.equal(result.tree.children[0].children[0].children[0].kind, 'predicate');
  }],
  ['tactics rejected before elaboration', 'by exact True', /Unsupported Lean term syntax/],
  ['executable tactics rejected before elaboration', 'by run_tac Lean.logInfo "must not execute"; exact True', /Unsupported Lean term syntax/],
  ['sorry rejected', 'sorry', /Unsupported Lean term syntax|sorry/],
  ['direct sorry axiom rejected', 'sorryAx Prop false', /sorry/],
  ['unknown names rejected', '∀ x : ℝ, x < missing', /Unknown identifier/],
  ['missing types rejected', '∀ x, x = x', /metavariable|infer|implicit|type|synthesize/i],
  ['non-propositions rejected', 'Nat', /type|Prop/i],
  ['commands after terms rejected', 'True\n#eval IO.println "must not execute"', /expected end of input/],
  ['import commands rejected', 'import Mathlib', /expected|Unsupported/],
  ['quotations rejected', '`(True)', /Unsupported Lean term syntax/],
  ['unknown notation rejected', '∀ p : ℝ, p ∈', /unexpected|expected/],
];
function collect(value, predicate, result = []) {
  if (value && typeof value === 'object') {
    if (!Array.isArray(value) && predicate(value)) result.push(value);
    for (const child of Object.values(value)) collect(child, predicate, result);
  }
  return result;
}
function applications(result, name) { return collect(result, x => x.kind === 'app' && x.fn?.name === name); }
function metric(result, name, expected, dimension) {
  const apps = applications(result, name);
  assert.ok(apps.length, `Expected ${name}`);
  for (const app of apps) { assert.equal(app.metric, expected); assert.equal(app.dimension, dimension); assert.equal(app.standard, true); }
}
const processResult = spawnSync(config.workerExecutable, [], {
  cwd: root, encoding: 'utf8', timeout: 90_000, maxBuffer: 16 * 1024 * 1024,
  env: { ...process.env, LEAN_PATH: config.leanPath.join(path.delimiter), STATEMENTLENS_LEAN_SYSROOT: config.leanSysroot },
  input: tests.map(([, source], requestId) => JSON.stringify({ ...(typeof source === 'string' ? { source } : source), requestId })).join('\n') + '\n',
});
assert.ifError(processResult.error);
assert.equal(processResult.status, 0, processResult.stderr);
const outputs = processResult.stdout.trim().split('\n').map(line => JSON.parse(line));
assert.equal(outputs.length, tests.length, 'One JSON result is required for each input line.');
let failures = 0;
tests.forEach(([name, , check], i) => {
  try {
    const result = outputs[i];
    assert.equal(result.requestId, i, "Responses must echo the server request identity.");
    if (check instanceof RegExp) { assert.equal(result.ok, false); assert.match(result.error, check); }
    else { assert.equal(result.ok, true, result.error); check(result); }
    console.log(`PASS ${name}`);
  } catch (error) { failures += 1; console.error(`FAIL ${name}: ${error.message}`); }
});
console.log(`${tests.length - failures}/${tests.length} real Lean integration checks passed.`);
process.exitCode = failures ? 1 : 0;
