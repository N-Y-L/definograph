import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';

const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(root, '.local/config.json'), 'utf8'));
const tests = [
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
  input: tests.map(([, source], requestId) => JSON.stringify({ source, requestId })).join('\n') + '\n',
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
