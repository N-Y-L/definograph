import assert from 'node:assert/strict';
import { spawnSync } from 'node:child_process';
import { readFile, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis } from '../src/core/types.ts';
import type { AnalysisOptions } from '../src/protocol.ts';
import { examples } from '../src/examples.ts';
import { typesetStatement } from '../src/notation/render.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
let checks = 0;
async function compile(source: string, options?: AnalysisOptions): Promise<Analysis> {
  const result = await backend.analyze(source, undefined, options);
  assert.equal(result.ok, true, String(result.error ?? 'Elaboration failed'));
  const analysis = result as unknown as Analysis;
  assert.ok(analysis.tree && analysis.expression && analysis.originalExpression);
  assert.equal(analysis.readableMath?.provider, 'leantex');
  return analysis;
}
function rendered(analysis: Analysis, body = false): string {
  const notation = body ? analysis.definitionReadableMath : analysis.readableMath;
  assert.equal(notation?.status, 'rendered', notation?.reason ?? 'Readable notation was not rendered');
  assert.ok(notation?.latex);
  assert.ok(notation.latex.length <= 32_768 && Buffer.byteLength(notation.latex) <= 65_536);
  assert.equal(typesetStatement(notation.latex).status, 'rendered', notation.latex);
  assert.ok(!notation.latex.includes('\\texttip'), 'MathJax tooltips must remain disabled');
  return notation.latex;
}
function pass(name: string): void { checks += 1; console.log(`PASS ${name}`); }

try {
  for (const example of examples) {
    rendered(await compile(example.source));
    pass(`${example.id}: checked Lean expression → LeanTeX → strict local KaTeX`);
  }
  const dependent = rendered(await compile('∀ x : ℝ, ∃ y : ℝ, x < y'));
  const fixed = rendered(await compile('∃ y : ℝ, ∀ x : ℝ, x < y'));
  assert.ok(dependent.indexOf('\\forall') < dependent.indexOf('\\exists'));
  assert.ok(fixed.indexOf('\\exists') < fixed.indexOf('\\forall'));
  assert.ok(dependent.includes('\\mathbb{R}') && !dependent.includes('\\text{Real}'));
  pass('quantifier order, typed binders, and exact Real display rule');

  const logic = rendered(await compile('∀ (P Q : Prop), ¬(P ∧ Q) ↔ (¬P ∨ ¬Q)'));
  assert.ok(logic.includes('\\neg') && logic.includes('(P') && logic.includes('Q)'));
  assert.ok(logic.includes('and') && logic.includes('or') && logic.includes('⇔'));
  const negative = rendered(await compile('∀ (x y : ℚ), -(x + y) = -x - y'));
  assert.ok(negative.includes('\\mathbb{Q}') && negative.includes('(x + y)'));
  pass('negation, alternatives, iff, and arithmetic grouping');

  const application = rendered(await compile('∀ (P : (ℝ → Prop) → Prop), P (fun x : ℝ => x = 0)'));
  assert.ok(application.includes('P((') && application.includes('\\mapsto') && application.includes('x = 0'));
  rendered(await compile('∀ (P : (ℝ → ℝ → Prop) → Prop), P (@Eq ℝ)'));
  pass('higher-order application and partially applied constants remain printable');

  const custom = await compile('∀ (X : Type) (m : Membership X (Set X)) (x : X) (s : Set X), @Membership.mem X (Set X) m s x');
  assert.ok(rendered(custom).includes('Membership'), 'The custom instance binder must stay visible');
  assert.ok(!compileSemanticDocument(custom).relations.some(r => r.kind === 'membership'));
  pass('readable membership notation does not grant custom instances set semantics');

  const definition = await compile('Function.Injective', { inputMode: 'declaration' });
  const signature = rendered(definition), body = rendered(definition, true);
  assert.notEqual(signature, body);
  assert.ok(signature.includes('\\prod') && !signature.includes('\\forall'));
  assert.ok(body.includes('\\mapsto') && body.includes('\\forall') && body.includes('\\implies'));
  pass('definition signature and parameterized body have separate mathematical notation');

  // This trusted fixture is generated only by the test runner, never from client input.
  // Compile it in the same isolated module path as production to exercise actual Lean code.
  const config = JSON.parse(await readFile(path.join(rootDir, '.local/config.json'), 'utf8'));
  const fixture = path.join(rootDir, '.local/notation-bounds.lean');
  await writeFile(fixture, String.raw`import StatementLens.Response
import StatementLens.ReadableMath
open Lean StatementLens
def require (condition : Bool) (message : String) : IO Unit :=
  unless condition do throw (IO.userError message)
#eval do
  let cap := 2 * 1024 * 1024
  let mandatory := Json.mkObj [("ok", toJson true), ("requestId", toJson "λ-request"),
    ("tree", toJson (String.ofList (List.replicate (cap - 1000) 'x')))]
  let latexField := Json.mkObj [("provider", toJson "leantex"), ("status", toJson "rendered"),
    ("latex", toJson (String.ofList (List.replicate 40000 'λ')))]
  let enriched := mandatory.setObjVal! "readableMath" latexField |>.setObjVal! "definitionReadableMath" latexField
  let limited := Response.serializeResponse enriched cap
  require (limited.utf8ByteSize + 1 ≤ cap) "optional notation exceeded total UTF-8 response cap"
  let result ← IO.ofExcept (Json.parse limited)
  require ((result.getObjVal? "tree").toOption == (mandatory.getObjVal? "tree").toOption) "mandatory tree changed"
  require ((result.getObjVal? "requestId").toOption == (mandatory.getObjVal? "requestId").toOption) "request ID changed"
  require ((result.getObjVal? "readableMath" >>= fun j => j.getObjValAs? String "status").toOption == some "unavailable") "missing bounded status"
  let exactCap := mandatory.compress.utf8ByteSize + 1
  let exact := Response.serializeResponse enriched exactCap
  require (exact == mandatory.compress) "optional status fields should be omitted when they cannot fit"
  require (Response.serializeResponse mandatory exactCap == mandatory.compress) "exact cap should include newline"
  require (Response.serializeResponse mandatory 1 == mandatory.compress) "oversized semantic content must not be truncated"
  let error := Json.mkObj [("ok", toJson false), ("error", toJson "failure")]
  require (Response.serializeResponse error 1 == error.compress) "error responses must not acquire notation fields"
  IO.println "PASS response serialization byte bounds and mandatory-field preservation"
run_elab do
  let mut large := mkConst (Name.mkSimple "True")
  for _ in [:70] do large := mkApp (mkConst (Name.mkSimple "Not")) large
  for _ in [:3] do
    let fallback ← ReadableMath.render large
    unless (fallback.getObjValAs? String "status").toOption == some "unavailable" do
      throwError "An excessive expression did not use bounded fallback"
    let normal ← ReadableMath.render (mkConst (Name.mkSimple "True"))
    unless (normal.getObjValAs? String "status").toOption == some "rendered" do
      throwError "A bounded fallback contaminated the next printer invocation"
  logInfo "PASS repeated size fallback leaves subsequent notation available"
`);
  const result = spawnSync(config.leanExecutable, [fixture], {
    cwd: rootDir, encoding: 'utf8', timeout: 30_000, maxBuffer: 1_000_000,
    env: { ...process.env, LEAN_PATH: config.leanPath.join(path.delimiter) },
  });
  assert.equal(result.error, undefined);
  assert.equal(result.status, 0, result.stdout + result.stderr);
  assert.ok(result.stdout.includes('PASS response serialization') && result.stdout.includes('PASS repeated size fallback'));
  pass('native printer fallback and aggregate transport-byte bounds');
  assert.equal((await compile('∀ n : ℕ, n = n')).tree.kind, 'forall');
  pass('persistent worker remains healthy after bounded-printer checks');
  console.log(`${checks}/${checks} native notation checks passed.`);
} finally {
  backend.close?.();
}
