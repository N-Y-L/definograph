/** RC3 acceptance corpus: fresh editor processes over a representative set of
 * mathematical distinctions, each with a stated reader question. Real captures
 * only; refusals are recorded as data. Writes outside the repository when
 * DEFINOGRAPH_ACCEPTANCE_CAPTURE_OUT is set. DEFINOGRAPH_ACCEPTANCE_ONLY
 * (case ids separated by |) runs a subset for exploration; a delivered corpus
 * is always a full run. */
import assert from 'node:assert/strict';
import { execFile } from 'node:child_process';
import { mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { promisify } from 'node:util';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { analyzeEditorContext, type EditorContextRequest, type EditorRange } from '../server/editor-context.js';
import { hashContextExecutable, sourceCaptureEngine } from '../server/source-capture-origin.js';
import { SourceSnapshotError, validateSourceSnapshot } from '../src/editor/source-snapshot.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceOccurrence } from '../src/editor/source-occurrence.js';
import type { HeadExposureBundle } from '../src/editor/source-history.js';
import type { SourceOccurrenceStep } from '../src/editor/source-occurrence.js';
import { decompositionPlan, validateDecompositionHistory, validateSourceDecomposition, type DecompositionOperation,
  type SourceDecompositionBundle } from '../src/editor/source-decomposition.js';
import { createExactJsonTools, type JsonValue } from '../src/packets/packet.js';
import { requireRecordedRefusal } from './acceptance-response.js';

const run = promisify(execFile);
const engine = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const configText = await readFile(path.join(engine, '.local/config.json'), 'utf8');
const config = JSON.parse(configText) as { leanExecutable: string; leanPath: string[] };
const executable = path.join(engine, '.local/statementlens-context');
const executableHash = await hashContextExecutable(executable);
assert.ok(sourceCaptureEngine(JSON.parse(configText), executableHash), 'Build the source capture engine first.');
const project = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-acceptance-')));
const fileName = path.join(project, 'Main.lean');
const libraryPaths = config.leanPath.filter(entry => !entry.includes('/leantex/'));
// One bounded canonicalization session per comparison: the bound is per session, and a run of many cases must not exhaust a shared one.
const canonical = (value: JsonValue) => createExactJsonTools().canonical(value);
const records: unknown[] = [], cases: unknown[] = [], refusals: unknown[] = [];
let version = 0;

/** `unavailable`: the engine must answer with an explicit recorded refusal. `planRefused`: the shared planner, asked directly,
 * must refuse the operation, and the editor context call must refuse with the identical error; the message is recorded, no
 * record is added and the history must be unchanged. */
interface Case { id: string; category: string; question: string; expected: string; source: string; selected: string; path?: SourceOccurrenceStep[];
  operations: (DecompositionOperation | { unavailable: DecompositionOperation } | { planRefused: DecompositionOperation })[] }
function range(source: string, selected: string): EditorRange {
  const start = source.lastIndexOf(selected); assert.ok(start >= 0, `selection not found: ${selected}`);
  const position = (offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
  return { start: position(start), end: position(start + selected.length) };
}
function request(source: string, selected: string): EditorContextRequest {
  return { engineDirectory: engine, fileName, source, selection: range(source, selected), workspaceTrusted: true, libraryPaths, document: { uri: pathToFileURL(fileName).href, version: ++version } };
}
async function seed(test: Case) {
  const base = request(test.source, test.selected);
  const first = await analyzeEditorContext(base);
  if (first.sourceSnapshotUnavailable !== undefined || first.sourceSnapshot === undefined) {
    return { kind: 'refusal' as const, refusal: `snapshot: ${first.sourceSnapshotUnavailable ?? 'unavailable'}` };
  }
  const response = await analyzeEditorContext({ ...base, occurrence: {
    snapshot: validateSourceSnapshot(first.sourceSnapshot), origin: first.sourceSnapshotOrigin as SourceSnapshotOrigin, path: test.path ?? [] } });
  if (response.sourceOccurrenceUnavailable !== undefined || response.sourceOccurrence === undefined) {
    return { kind: 'refusal' as const, refusal: `occurrence: ${response.sourceOccurrenceUnavailable ?? 'unavailable'}` };
  }
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const occurrence = validateSourceOccurrence(response.sourceOccurrence, snapshot);
  const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  if (!(occurrence.checking.status === 'captured' && occurrence.checking.action.status === 'completed' && occurrence.checking.selected)) {
    return { kind: 'refusal' as const, refusal: `original pair: ${JSON.stringify(occurrence.checking).slice(0, 300)}` };
  }
  return { kind: 'session' as const, label: test.id, request: base, parent: { snapshot, origin, occurrence }, original: occurrence.checking.selected,
    seed: null as HeadExposureBundle | null, attempts: [] as SourceDecompositionBundle[] };
}
type Session = Extract<Awaited<ReturnType<typeof seed>>, { kind: 'session' }>;
async function append(session: Session, previousCaptureId: string, parentStepIndex: number, operation: DecompositionOperation, expectUnavailable: boolean) {
  const before = canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue);
  const decomposition = { ...session.parent, seed: session.seed, attempts: session.attempts, previousCaptureId, parentStepIndex, operation, version: 3 as const };
  const response = await analyzeEditorContext({ ...session.request, decomposition });
  requireRecordedRefusal(response, expectUnavailable, session.label);
  if (response.sourceDecompositionUnavailable !== undefined || response.sourceDecomposition === undefined) {
    return { unavailable: response.sourceDecompositionUnavailable ?? 'unavailable' } as const;
  }
  const snapshot = validateSourceSnapshot(response.sourceSnapshot);
  const history = validateDecompositionHistory({ snapshot: session.parent.snapshot, occurrence: session.parent.occurrence,
    seed: session.seed ? { snapshot: session.seed.snapshot, record: session.seed.record } : null,
    attempts: session.attempts.map(bundle => ({ snapshot: bundle.snapshot, record: bundle.record })) });
  const record = validateSourceDecomposition(response.sourceDecomposition, snapshot, history);
  assert.equal(record.previousCaptureId, previousCaptureId); assert.equal(record.parentStepIndex, parentStepIndex);
  assert.ok(record.checking.status === 'captured', JSON.stringify(record.checking));
  const last = record.checking.steps.at(-1)!;
  if (expectUnavailable) assert.ok(last.output.status === 'unavailable' || record.checking.stop !== null, `expected an explicit refusal for ${session.label}`);
  assert.ok(record.checking.steps.slice(0, -1).every(step => step.replay === 'matched'));
  assert.equal(canonical({ parent: session.parent, seed: session.seed, attempts: session.attempts } as unknown as JsonValue), before);
  const bundle = { snapshot, origin: response.sourceSnapshotOrigin as SourceSnapshotOrigin, record };
  records.push({ label: session.label, source: session.request.source, selection: session.request.selection,
    parent: session.parent, seed: session.seed, priorAttempts: [...session.attempts], operation, previousCaptureId, parentStepIndex, response });
  session.attempts.push(bundle);
  return { record } as const;
}
async function runCase(test: Case) {
  const started = await seed(test);
  if (started.kind === 'refusal') { refusals.push({ id: test.id, category: test.category, question: test.question, expected: test.expected, source: test.source, selected: test.selected, refusal: started.refusal }); console.log(`refused ${test.id}: ${started.refusal.slice(0, 120)}`); return; }
  let previous = started.parent.occurrence.captureId, step = 0, outcome = 'completed', executed = 0;
  for (const item of test.operations) {
    if ('planRefused' in item) {
      const before = canonical({ parent: started.parent, seed: started.seed, attempts: started.attempts } as unknown as JsonValue), count = records.length;
      // The shared planner is asked directly first; only its own refusal counts. The request is still sent through the editor
      // context call, which must refuse with the identical error; any other error is rethrown.
      const history = validateDecompositionHistory({ snapshot: started.parent.snapshot, occurrence: started.parent.occurrence,
        seed: started.seed ? { snapshot: started.seed.snapshot, record: started.seed.record } : null, attempts: started.attempts.map(bundle => ({ snapshot: bundle.snapshot, record: bundle.record })) });
      const refusal = (error: unknown) => { if (error instanceof SourceSnapshotError) return `${error.code}: ${error.message}`; throw error; };
      let planned: string | undefined, called: string | undefined;
      try { decompositionPlan(history, previous, step, item.planRefused, 3); } catch (error) { planned = refusal(error); }
      assert.ok(planned !== undefined, `expected the planner to refuse ${test.id}`);
      try { await append(started, previous, step, item.planRefused, false); } catch (error) { called = refusal(error); }
      assert.equal(called, planned, 'the editor context call must refuse with the planner error');
      assert.equal(records.length, count); assert.equal(canonical({ parent: started.parent, seed: started.seed, attempts: started.attempts } as unknown as JsonValue), before);
      outcome = `plan refused after step ${executed}: ${planned}`; break;
    }
    const operation = 'unavailable' in item ? item.unavailable : item, expectUnavailable = 'unavailable' in item;
    const result = await append(started, previous, step, operation, expectUnavailable);
    if ('unavailable' in result) { outcome = `unavailable: ${result.unavailable}`; break; }
    executed++;
    const last = result.record.checking.status === 'captured' ? result.record.checking.steps.at(-1) : undefined;
    if (last?.output.status === 'unavailable' || (result.record.checking.status === 'captured' && result.record.checking.stop)) { outcome = `refused at step ${executed}: ${JSON.stringify(result.record.checking.status === 'captured' ? result.record.checking.stop : null)?.slice(0, 200)}`; break; }
    previous = result.record.captureId; step = result.record.operations.length - 1;
  }
  cases.push({ id: test.id, category: test.category, question: test.question, expected: test.expected, selected: test.selected, operations: test.operations, executed, outcome,
    originalArity: started.original.home.arity, records: records.filter(row => (row as { label: string }).label === test.id).length });
  console.log(`${test.id}: ${executed}/${test.operations.length} operations, ${outcome}`);
}

const dependency = `namespace Acceptance
def Twice (n : Nat) : Nat := n + n
structure Pair where
  fst : Nat
  snd : Nat
def Balanced (p : Pair) : Prop := p.fst = p.snd
end Acceptance
`;
const gadget = `structure Gadget where
  Carrier : Type
  op : Carrier → Carrier
  law₁ : ∀ x, op x = x
  law₂ : ∀ x, op (op x) = x
`;
const tests: Case[] = [
  { id: 'proof binder not referenced by the body', category: 'binders', question: 'Which binder is a proof, and may the existential candidate depend on it?', expected: 'n is universal over a type; h is a proof binder that the body does not reference, so the inner forall reads as an implication; the candidate m is entered in the scope of n and h; no witness is named.',
    source: 'example : Prop := ∀ (n : Nat) (h : n > 0), ∃ m : Nat, m < n\n', selected: '∀ (n : Nat) (h : n > 0), ∃ m : Nat, m < n',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['appArg', 'lamBody'] }, { kind: 'logical' }] },
  { id: 'proposition object then implication', category: 'binders', question: 'Is P a proposition object or a proof, and is the inner arrow an implication?', expected: 'P is a proposition object (domain Prop at Sort 1); the inner forall has a proof binder unused in its body, so it reads as an implication.',
    source: 'example : Prop := ∀ (P : Prop), P → P\n', selected: '∀ (P : Prop), P → P',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'statement selected', category: 'proposition versus proof', question: 'Is the selection a formed proposition, and which receipt establishes that?', expected: 'An equality proposition; the logical root receipt at Sort zero establishes formation, no proof is claimed.',
    source: 'example : 2 + 2 = 4 := rfl\n', selected: '2 + 2 = 4', operations: [{ kind: 'logical' }] },
  { id: 'proof term selected', category: 'proposition versus proof', question: 'Which statement does the bare constant rfl carry, and on which receipts would it be read as its supplier?', expected: 'The selection captures the constant rfl at its captured universe instantiation (level 1) with its own statement ∀ {α} {a : α}, a = a, not the instantiated proof the surrounding declaration uses, which this selection does not capture. Within the checked pair and its closed declarations, the enclosing declaration statement 2 + 2 = 4 occurs only as the type of the context entry _example, to which the constant does not refer. The snapshot separately records an expected-type annotation. The constant is read as the supplier of its own statement, never of the enclosing declaration statement, only when its typing receipt is accepted and the formation of that statement is established as a proposition; in this capture that formation rests on the type-component receipt and the logical-root receipt, both accepted at Sort zero, two receipts of one checked judgement and not independent confirmation; the supplier rule itself is decided by the supplier module, not by this corpus.',
    source: 'example : 2 + 2 = 4 := rfl\n', selected: 'rfl', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'ascribed proof term selected', category: 'proposition versus proof', question: 'Which statement does a type-ascribed proof term carry after capture, and is the source ascription retained?', expected: 'The captured pair is @rfl Nat (2 + 2) : 2 + 2 = 2 + 2, the statement inferred for the term, in a context with one entry, _example, whose type is the enclosing declaration statement 2 + 2 = 4. The inferred type differs syntactically from the source ascription: within the checked pair and its closed declarations, the literal 4 occurs only in that context entry, never in the checked term or its checked type, and the term does not refer to that entry. The snapshot separately records the expected-type annotation containing 4. No conversion step comparing the inferred type with the source ascription is recorded in this derivation. The term is read as the supplier of the captured reflexive equality only when its typing receipt is accepted and the formation of that statement is established as a proposition; in this capture that formation rests on the type-component receipt and the logical-root receipt, both accepted at Sort zero, two receipts of one checked judgement and not independent confirmation; the equality shape is read from the logical step.',
    source: 'example : 2 + 2 = 4 := (rfl : 2 + 2 = 4)\n', selected: '(rfl : 2 + 2 = 4)', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'unproved false existential', category: 'empty and unproved', question: 'Can a false, unproved proposition be inspected without being asserted?', expected: 'Yes: formed existential, candidate n, body an unexpanded proposition; no witness, no truth claim.',
    source: 'example : Prop := ∃ n : Nat, n < 0\n', selected: '∃ n : Nat, n < 0', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['appArg', 'lamBody'] }, { kind: 'logical' }] },
  { id: 'statement with sorry proof', category: 'empty and unproved', question: 'Does a statement whose proof is sorry stay inspectable without any claim about the proof?', expected: 'The statement False is a formed proposition with the constant False form. The proof term is not part of this selection: no pair, receipt or context entry of the capture refers to it, and the reading says nothing about it. The editor response saved with the record keeps the warning that the declaration uses sorry; that is a buffer diagnostic outside the capture, not a check, and no reading is derived from it. Selecting the sorry term itself is the separate case sorry proof term selected.',
    source: 'example : False := sorry\n', selected: 'False', operations: [{ kind: 'logical' }] },
  { id: 'empty type', category: 'empty and unproved', question: 'Is an empty type distinguished from a false proposition?', expected: 'Empty is a type above Prop; formation reads as a type, not a proposition, and nothing is asserted about inhabitants.',
    source: 'example : Type := Empty\n', selected: 'Empty', operations: [{ kind: 'logical' }] },
  { id: 'local definition', category: 'local definitions', question: 'Does the reader keep the let value exact and separate from a binder?', expected: 'The let enters the context as an owned value; the body equality is read after entering it.',
    source: 'example : Prop := let f := fun n : Nat => n + 1; f 2 = 3\n', selected: 'let f := fun n : Nat => n + 1; f 2 = 3',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['letBody'] }, { kind: 'logical' }] },
  { id: 'second law of a structure', category: 'structure laws', question: 'Whose law is this, does the field supply its proof, and is the focused body a specialized proof?', expected: 'The law belongs to the Gadget owner g, a variable of the context. The projected field is read as the supplier of the law statement only when its typing receipt is accepted and the formation of the law is established as a proposition; in this capture that formation rests on the type-component receipt and the logical-root receipt, two receipts of one checked judgement. The focused body is a position inside the law; nothing is read about supply for this part by itself.',
    source: `${gadget}example (g : Gadget) : Gadget := g\n`, selected: 'g',
    operations: [{ kind: 'fields' }, { kind: 'project', index: 3 }, { kind: 'typeComponent' }, { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'nested structure field', category: 'structure laws', question: 'Is a field of a structure-valued field traced through both projections without a supplier claim?', expected: 'The field n is a projection of a projection: first the field inner of the owner o, then the field n of that result. Each occurrence keeps the origin of the record where it first appeared, so owner origin is preserved; no formation is read and no law is implied. Neither field records an embedded parent: inner is an ordinary structure-valued field, not a parent from extends.',
    source: 'structure Inner where\n  n : Nat\nstructure Outer where\n  inner : Inner\n  bound : inner.n ≤ inner.n\nexample (o : Outer) : Outer := o\n', selected: 'o',
    operations: [{ kind: 'fields' }, { kind: 'project', index: 0 }, { kind: 'fields' }, { kind: 'project', index: 0 }] },
  { id: 'function type universe', category: 'universes', question: 'Which sort does a function between types inhabit, and is it read as a proposition?', expected: 'Type → Type is a type above Prop (Sort 2); dependent-function reading only, no universal statement.',
    source: 'example : Type 1 := Type → Type\n', selected: 'Type → Type', operations: [{ kind: 'logical' }] },
  { id: 'universe parameter', category: 'universes', question: 'What does the reader say about Sort u itself?', expected: 'The inferred type of Sort u is Sort (succ u), a literal successor level, so the term is a type above Prop with no logical form; the general-level neutrality applies to terms whose own type is Sort u.',
    source: 'universe u\nexample : Sort (u + 1) := Sort u\n', selected: 'Sort u', operations: [{ kind: 'logical' }] },
  { id: 'general sort root', category: 'universes', question: 'Does a term whose type is Sort u keep the neutral general-level reading?', expected: 'A variable α : Sort u has inferred type Sort u with a parameter level, so formation is a general sort: neither a proposition nor a type above Prop is read.',
    source: 'universe u\nexample (α : Sort u) : Sort u := α\n', selected: 'α', operations: [{ kind: 'logical' }] },
  { id: 'binder over a general sort', category: 'universes', question: 'Does a binder whose domain lives at Sort u keep the neutral binder reading?', expected: 'The outer binder over Sort u is universal (its domain is a type above Prop); the inner binder over α : Sort u has a general-level domain and no binder classification, generic universal wording only.',
    source: 'universe u\nexample : Prop := ∀ (α : Sort u) (a : α), a = a\n', selected: '∀ (α : Sort u) (a : α), a = a',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'conjunction', category: 'standard forms', question: 'Are both conjuncts kept as required conditions without supplying either?', expected: 'A conjunction with two required conditions; focusing the left conjunct keeps the required-left role and supplies nothing.',
    source: 'example : Prop := (1 = 1) ∧ (2 = 2)\n', selected: '(1 = 1) ∧ (2 = 2)', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['appFun', 'appArg'] }, { kind: 'logical' }] },
  { id: 'equivalence', category: 'standard forms', question: 'Are the two sides of an equivalence kept without inventing implication proofs?', expected: 'An equivalence with two equivalent sides; focusing the right side keeps the equivalent-right role.',
    source: 'example : Prop := (1 = 1) ↔ (2 = 2)\n', selected: '(1 = 1) ↔ (2 = 2)', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['appArg'] }, { kind: 'logical' }] },
  { id: 'implication to True', category: 'standard forms', question: 'Is an arrow between propositions read as an implication with an unused proof binder, and is True a formed proposition?', expected: 'A literal forall over a Prop domain whose body ignores the binder reads as an implication; its body True is the constant True proposition.',
    source: 'example : Prop := (1 = 1) → True\n', selected: '(1 = 1) → True', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'universal then existential', category: 'binders', question: 'In ∀x∃y, may y depend on x?', expected: 'x is universal, then y is a candidate within the existential statement that may depend on x; no witness.',
    source: 'example : Prop := ∀ x : Nat, ∃ y : Nat, y = x\n', selected: '∀ x : Nat, ∃ y : Nat, y = x', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['appArg', 'lamBody'] }, { kind: 'logical' }] },
  { id: 'existential then universal', category: 'binders', question: 'In ∃y∀x, is y chosen before x?', expected: 'y is a candidate outside the universal, so it may not depend on x; x is universal inside; no witness.',
    source: 'example : Prop := ∃ y : Nat, ∀ x : Nat, y = x\n', selected: '∃ y : Nat, ∀ x : Nat, y = x', operations: [{ kind: 'logical' }, { kind: 'focus', path: ['appArg', 'lamBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'abstract existential predicate', category: 'binders', question: 'Does an existential over an abstract predicate stay folded rather than gaining a candidate?', expected: 'Exists p with a non-lambda predicate is a formed existential statement. A focus through a lambda body is refused by the shared planner, because the predicate is not a lambda, and the editor context call refuses with the same planner error; so no binder is entered and no candidate is created.',
    source: 'example (p : Nat → Prop) : Prop := Exists p\n', selected: 'Exists p', operations: [{ kind: 'logical' }, { planRefused: { kind: 'focus', path: ['appArg', 'lamBody'] } }] },
  { id: 'imported definition exposed', category: 'imported definitions', question: 'What does exposing an imported definition head show, and does it change the proposition claim?', expected: 'The safe definition body is exposed with a conversion receipt; the exposed equality is then read as a formed proposition; nothing is proved.',
    source: 'import Acceptance\nexample : Prop := Acceptance.Balanced ⟨1, 1⟩\n', selected: 'Acceptance.Balanced ⟨1, 1⟩',
    operations: [{ kind: 'logical' }, { kind: 'expose', target: 'term' }, { kind: 'logical' }] },
  { id: 'imported function applied', category: 'imported definitions', question: 'Is an ordinary imported function application read as a term rather than a proposition?', expected: 'The selected application Twice 3 (occurrence 1) has an accepted typing check and no formation is read for it. Its type Nat (occurrence 2, reached by the type-component step) is formed as a type above Prop, with no logical form. Nothing here is read as a proposition.',
    source: 'import Acceptance\nexample : Nat := Acceptance.Twice 3\n', selected: 'Acceptance.Twice 3', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'constructor head refusal', category: 'unsupported', question: 'Is an unsupported definition head refused explicitly?', expected: 'Exposure of a constructor head is refused with a reason; the pair stays inspectable.',
    source: 'example : Nat := Nat.succ 1\n', selected: 'Nat.succ 1', operations: [{ unavailable: { kind: 'expose', target: 'term' } }] },
  { id: 'aliased owner refusal', category: 'unsupported', question: 'Is a nonliteral owner type refused for field inspection?', expected: 'Fields of an alias owner are refused explicitly; no catalogue is invented.',
    source: `${gadget}def Alias := Gadget\nexample (g : Alias) : Alias := g\n`, selected: 'g', operations: [{ unavailable: { kind: 'fields' } }] },
  { id: 'proof binder referenced by the body', category: 'binders', question: 'When the body refers to the proof binder, does the inner binder stay a dependent universal statement rather than an implication?', expected: 'n is universal over a type; h is a proof binder that the body references through the subtype value built from n and h, so the inner forall stays a dependent universal statement over proofs of n > 0 and does not read as an implication; the body is an equality.',
    source: 'example : Prop := ∀ (n : Nat) (h : n > 0), (⟨n, h⟩ : { k : Nat // k > 0 }).val = n\n', selected: '∀ (n : Nat) (h : n > 0), (⟨n, h⟩ : { k : Nat // k > 0 }).val = n',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }, { kind: 'focus', path: ['piBody'] }, { kind: 'logical' }] },
  { id: 'named theorem constant selected', category: 'proposition versus proof', question: 'Does a named theorem constant carry its declared statement as its inferred type?', expected: 'The constant two_add_two has its declared statement 2 + 2 = 4 as its inferred type, with the literal 4 on the right side. The context has one entry, _example, carrying the enclosing declaration statement; the constant is closed and does not refer to it. It is read as the supplier of exactly that statement only when its typing receipt is accepted and the formation of that statement is established as a proposition; in this capture that formation rests on the type-component receipt and the logical-root receipt, both accepted at Sort zero, two receipts of one checked judgement and not independent confirmation; the equality shape is read from the logical step.',
    source: 'theorem two_add_two : 2 + 2 = 4 := rfl\nexample : 2 + 2 = 4 := two_add_two\n', selected: 'two_add_two', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'sorry proof term selected', category: 'empty and unproved', question: 'Is a proof term that is sorry recorded without being read as a proof?', expected: 'The selection is refused before any check is attempted, in the source-policy phase, because the prepared source contains a placeholder; no checked selected pair, receipt or derived reading is produced for this selection.',
    source: 'example : False := sorry\n', selected: 'sorry', operations: [] },
  { id: 'explicit universe constant', category: 'universes', question: 'Which sort does a constant with an explicit universe argument inhabit?', expected: 'PUnit.{2} has inferred type Sort 2, a literal successor level, so it is formed as a type above Prop; its shape is unexpanded and no logical form is read.',
    source: 'example : Type 1 := PUnit.{2}\n', selected: 'PUnit.{2}', operations: [{ kind: 'logical' }] },
  { id: 'core recursive definition head', category: 'imported definitions', question: 'What does exposing a core recursive definition head show?', expected: 'The head List.length is a definition in the initial environment, so the exposure step records its definition body with an accepted conversion receipt. The exposed term (occurrence 2) has an accepted typing check at type Nat, the same type as the selected application (occurrence 1); no formation is read for either occurrence; the definition is exposed with its leading arguments applied, but the length is not computed.',
    source: 'example : Nat := List.length [1, 2]\n', selected: 'List.length [1, 2]', operations: [{ kind: 'expose', target: 'term' }] },
  { id: 'inductive predicate head', category: 'unsupported', question: 'Is the head of an inductive predicate refused for exposure?', expected: 'Nat.le 1 2 is a formed proposition with an unexpanded shape. Exposure of its head is refused explicitly in the head phase because an inductive predicate is not a definition; the proposition stays inspectable.',
    source: 'example : Prop := Nat.le 1 2\n', selected: 'Nat.le 1 2', operations: [{ kind: 'logical' }, { unavailable: { kind: 'expose', target: 'term' } }] },
  { id: 'opaque head', category: 'unsupported', question: 'Is an opaque constant head refused for exposure?', expected: 'Exposure of an opaque constant is refused explicitly in the head phase because its head is not a definition in the initial environment; the pair stays inspectable.',
    source: 'opaque hidden : Nat\nexample : Nat := hidden\n', selected: 'hidden', operations: [{ unavailable: { kind: 'expose', target: 'term' } }] },
  { id: 'selection inside a binder', category: 'binders', question: 'When the original selection is reached by entering a binder, is that binder kept in the context without a logical role?', expected: 'The originally selected occurrence is the body x = x, reached inside the selected statement by entering the binder x. Its context lists the entry _example and then x, entered by the selection itself; no logical role is read for x because the chain starts below it. The body is a formed proposition with the equality shape, and its type Prop is formed as a type above Prop.',
    source: 'example : Prop := ∀ x : Nat, x = x\n', selected: '∀ x : Nat, x = x', path: ['piBody'], operations: [{ kind: 'logical' }, { kind: 'typeComponent' }] },
  { id: 'variable named like the auxiliary entry', category: 'context', question: 'Are two context entries with the same name kept apart by their recorded declaration kinds?', expected: 'The context has two entries named _example: the auxiliary declaration recorded for the declaration being elaborated, then the variable the user wrote. The capture records the first with kind auxDecl and the second with kind default, so they are told apart by the record, never by the name. The selected term is the variable, the innermost entry (occurrence 1); it has an accepted typing check at type Nat and no formation is read for it. Its type Nat (occurrence 2, reached by the type-component step) is formed as a type above Prop. Nothing is read as a proposition.',
    source: 'example (_example : Nat) : Nat := _example\n', selected: '_example', operations: [{ kind: 'typeComponent' }] },
  { id: 'term inside a named theorem', category: 'context', question: 'Which name does the auxiliary context entry carry inside a named theorem?', expected: 'Inside the body of the theorem helper the context lists the auxiliary declaration, recorded with kind auxDecl and named helper after the theorem, then the variable n. The selected constant rfl is captured with its own general statement at its captured universe instantiation and does not refer to either entry.',
    source: 'theorem helper (n : Nat) : n = n := rfl\n', selected: 'rfl', operations: [{ kind: 'typeComponent' }] },
  { id: 'selection inside a local definition', category: 'context', question: 'When the original selection is reached by entering a local definition, is the definition kept in the context as a let entry?', expected: 'The originally selected occurrence is the body f 2 = 3, reached inside the selected term by entering the local definition f. Its context lists the entry _example and then f as a let entry with its value, entered by the selection itself, so the capture records no declaration for f and no logical role is read for it. The body is a formed proposition with the equality shape, and its type Prop is formed as a type above Prop.',
    source: 'example : Prop := let f := fun n : Nat => n + 1; f 2 = 3\n', selected: 'let f := fun n : Nat => n + 1; f 2 = 3', path: ['letBody'], operations: [{ kind: 'logical' }, { kind: 'typeComponent' }] },
  { id: 'term under a context definition', category: 'context', question: 'When the selected term lies under a local definition, is the definition a recorded context declaration?', expected: 'The selected term is the body f 2 = 3 itself. Its context lists the entry _example and then f as a let entry with its value; the capture records f as a context declaration of kind default, a local definition the user wrote and not an auxiliary entry. The body is a formed proposition with the equality shape, and its type Prop is formed as a type above Prop.',
    source: 'example : Prop := let f := fun n : Nat => n + 1; f 2 = 3\n', selected: 'f 2 = 3', operations: [{ kind: 'logical' }, { kind: 'typeComponent' }] },
  { id: 'ordinary value inspected', category: 'proposition versus proof', question: 'Is an ordinary value read as a term, and its type as a type above Prop, each from its own recorded outcomes?', expected: 'The selected value 2 + 2 (occurrence 1) is inspected by a logical step: its accepted logical-root outcome has the inferred type Nat, which is not a sort, so its formation is established as an ordinary term, with an unexpanded shape and no logical form. Its type Nat (occurrence 2, reached by the type-component step) is formed as a type above Prop, on the type-component and logical-root outcomes at Sort 1, two receipts of one checked judgement. Nothing is read as a proposition and nothing is evaluated.',
    source: 'example : Nat := 2 + 2\n', selected: '2 + 2', operations: [{ kind: 'logical' }, { kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'two binders entered by one focus', category: 'binders', question: 'When one focus enters two binders, is each binder kept in order with the role read for it?', expected: 'One focus through two bodies enters n and then h. The outer statement was inspected, so the focus has the body role of that universal statement and n is read as a universal binder over a type; the inner statement was not inspected, so h is entered without a role; this chain does not establish a proof-binder reading for h. The reached occurrence has an accepted typing check and no formation read; its type Prop is formed as a type above Prop.',
    source: 'example : Prop := ∀ (n : Nat) (h : n > 0), ∃ m : Nat, m < n\n', selected: '∀ (n : Nat) (h : n > 0), ∃ m : Nat, m < n',
    operations: [{ kind: 'logical' }, { kind: 'focus', path: ['piBody', 'piBody'] }, { kind: 'typeComponent' }] },
  { id: 'embedded parent field', category: 'structure laws', question: 'Is a field inherited through extends traced through its embedded parent without a supplier claim?', expected: 'Derived extends Base, so the first direct field of Derived is toBase, which the catalogue records with the embedded parent Base. The field n is reached by projecting toBase and then n of that result; n itself records no parent. No formation is read for any of the three occurrences and no law or supplier is implied.',
    source: 'structure Base where\n  n : Nat\nstructure Derived extends Base where\n  m : Nat\nexample (d : Derived) : Derived := d\n', selected: 'd',
    operations: [{ kind: 'fields' }, { kind: 'project', index: 0 }, { kind: 'fields' }, { kind: 'project', index: 0 }] },
  { id: 'term using a lemma proved with a placeholder', category: 'empty and unproved', question: 'When a selected term uses a lemma whose proof is a placeholder, what does the record say about its typing check?', expected: 'The selected term, its type and context contain no direct placeholder, so the source placeholder policy permits capture. The recorded typing check of the constant claimed is accepted and its declaration audit lists the axiom sorryAx. The statement 2 + 2 = 5 is a formed proposition with the equality shape. Any reading of the constant as the supplier of that statement is relative to the recorded axiom, which a reader must be shown; nothing is read as established beyond the recorded checks.',
    source: 'theorem claimed : 2 + 2 = 5 := sorry\nexample : 2 + 2 = 5 := claimed\n', selected: 'claimed', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'term using a user axiom', category: 'empty and unproved', question: 'When a selected term is an axiom the user declared, what does the record say about its typing check?', expected: 'The selected constant assumed is an axiom declared in the same buffer. Its typing check is accepted, and the declaration audit recorded for that check lists the axiom assumed itself. The statement 2 + 2 = 5 is a formed proposition with the equality shape. Any reading of the constant as the supplier of that statement is relative to that recorded axiom, which a reader must be shown.',
    source: 'axiom assumed : 2 + 2 = 5\nexample : 2 + 2 = 5 := assumed\n', selected: 'assumed', operations: [{ kind: 'typeComponent' }, { kind: 'logical' }] },
  { id: 'metavariable placeholder', category: 'unsupported', question: 'Is a placeholder selection refused rather than read?', expected: 'The selection is a placeholder that elaboration leaves unresolved. Occurrence capture was attempted and refused during source admission in the occurrence-capture phase, before any declaration check, because the exact source term or its supplied type is outside the named source admission profile; no checked selected pair, receipt or derived reading is produced for this selection.',
    source: 'example : Nat := _\n', selected: '_', operations: [] },
];

try {
  await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
  await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
  await writeFile(path.join(project, 'lakefile.toml'), 'name = "definograph_acceptance"\n[[lean_lib]]\nname = "Acceptance"\n');
  await writeFile(path.join(project, 'Acceptance.lean'), dependency);
  await run(config.leanExecutable, ['-o', '.lake/build/lib/lean/Acceptance.olean', 'Acceptance.lean'], { cwd: project, env: { ...process.env, LEAN_PATH: '' }, timeout: 60_000 });
  await writeFile(fileName, '-- Source buffers are submitted without editing this file.\n');
  const saved = await readFile(fileName);
  const only = process.env.DEFINOGRAPH_ACCEPTANCE_ONLY?.split('|');
  for (const test of tests) if (!only || only.includes(test.id)) await runCase(test);
  assert.deepEqual(await readFile(fileName), saved);
  assert.equal(await readFile(path.join(engine, '.local/config.json'), 'utf8'), configText);
  assert.equal(await hashContextExecutable(executable), executableHash);
  const output = process.env.DEFINOGRAPH_ACCEPTANCE_CAPTURE_OUT;
  if (output) {
    const destination = path.resolve(output), relative = path.relative(engine, destination);
    assert.ok(relative === '..' || relative.startsWith('..' + path.sep) || path.isAbsolute(relative), 'Keep generated captures outside the repository.');
    await mkdir(path.dirname(destination), { recursive: true });
    await writeFile(destination, JSON.stringify(records, null, 2) + '\n');
    await writeFile(destination.replace(/\.json$/, '') + '.cases.json', JSON.stringify({ engineExecutableSha256: executableHash, dependency, cases, refusals }, null, 2) + '\n');
  }
  console.log(`Captured ${records.length} acceptance records over ${cases.length} cases with ${refusals.length} seed refusals; source and build unchanged.`);
} catch (error) {
  if (process.env.DEFINOGRAPH_ACCEPTANCE_CAPTURE_OUT) await writeFile(`${path.resolve(process.env.DEFINOGRAPH_ACCEPTANCE_CAPTURE_OUT)}.failed.json`, JSON.stringify({ records, cases, refusals }, null, 2) + '\n');
  throw error;
} finally { await rm(project, { recursive: true, force: true }); }
