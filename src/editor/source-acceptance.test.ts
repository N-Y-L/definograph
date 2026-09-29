/** RC3 acceptance corpus: each real capture answers a stated reader question
 * through the accepted provenance module and the read-only panel. Gated on
 * DEFINOGRAPH_ACCEPTANCE_FIXTURES (captures written outside the repository by
 * scripts/source-acceptance-integration.ts; the companion .cases.json carries
 * the questions, expected answers and recorded refusals). */
import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { JsonObject, JsonValue } from '../packets/packet';
import { SourceSnapshotError, type SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import type { HeadExposureBundle } from './source-history';
import { decompositionPlan, validateDecompositionHistory, validateSourceDecomposition, type DecompositionOperation, type SourceDecompositionBundle } from './source-decomposition';
import { occurrenceProvenance, type OccurrenceProvenance } from './source-provenance';
import { ProvenancePanel } from './SourceProvenanceReading';
import { requireRecordedRefusal } from '../../scripts/acceptance-response';

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  seed: HeadExposureBundle | null; priorAttempts: SourceDecompositionBundle[]; operation: DecompositionOperation;
  previousCaptureId: string; parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: SourceSnapshotOrigin; sourceDecomposition: SourceDecompositionBundle['record'];
    diagnostics: { line: number; column: number; severity: string; message: string }[] };
}
interface Case { id: string; category: string; question: string; expected: string; executed: number; outcome: string; operations: unknown[] }
interface Refusal { id: string; category: string; question: string; expected: string; source: string; selected: string; refusal: string }
/** The stricter vocabulary of the independent oracle, applied to what a reader sees: text nodes only, identifiers in code set apart. */
const STRICT = /witness|there exists|there is |holds|\bverified\b|checked now|not a proposition|\binvalid\b|proves|supplier|\bvalid\b|\bfalse\b|\bfailed\b|\btrue\b|refuted|∀|∃/i;
const seen = (text: string) => text.replace(/<code>[^<]*<\/code>/g, ' § ').replace(/<[^>]+>/g, ' ');
const location = process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES;
const rows: Row[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
const manifest: { cases: Case[]; refusals: Refusal[] } = location ? JSON.parse(readFileSync(location.replace(/\.json$/, '') + '.cases.json', 'utf8')) : { cases: [], refusals: [] };
const ends = rows.filter((row, index) => rows[index + 1]?.label !== row.label);
function fixture(row: Row) {
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  const record = validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  return { history, record, last: record.operations.length - 1 };
}
/** One line per chain: occurrence statuses and forms, then relations with roles and binder roles. The expected table below is the reader answer. */
function summarize(provenance: OccurrenceProvenance): string {
  const occurrences = provenance.occurrences.map(occurrence => `${occurrence.formation.status === 'established' ? occurrence.formation.kind : occurrence.formation.status}`
    + `/${occurrence.domain.status === 'established' ? occurrence.domain.kind : occurrence.domain.status}`
    + (occurrence.inspections.length ? `:${occurrence.inspections.map(inspection => inspection.form ?? 'none').join('|')}` : ''));
  const edges = provenance.edges.map(edge => edge.relation.kind !== 'containment' ? edge.relation.kind
    : `contain(${edge.relation.path.join('/')}${edge.relation.role ? ` ${edge.relation.role.form}/${edge.relation.role.operand}` : ''}${edge.relation.binders.length ? ` ${edge.relation.binders.map(binder => binder.role ?? 'none').join(',')}` : ''})`);
  return `${occurrences.join(' ')} | ${edges.join(' > ')}`;
}
const EXPECTED: Record<string, string> = {
  'proof binder not referenced by the body': 'proposition/type:forall proposition/proposition:implies proposition/unestablished:exists proposition/unestablished:unexpanded | contain(piBody forall/body universal) > contain(piBody implies/body proof) > contain(appArg/lamBody exists/predicate candidate)',
  'proposition object then implication': 'proposition/type:forall proposition/proposition:implies | contain(piBody forall/body universal)',
  'statement selected': 'proposition/unestablished:eq | ',
  'proof term selected': 'unestablished/unestablished proposition/type:forall | type-of',
  'ascribed proof term selected': 'unestablished/unestablished proposition/unestablished:eq | type-of',
  'unproved false existential': 'proposition/unestablished:exists proposition/unestablished:unexpanded | contain(appArg/lamBody exists/predicate candidate)',
  'statement with sorry proof': 'proposition/unestablished:false | ',
  'empty type': 'type/unestablished:none | ',
  'local definition': 'proposition/unestablished:unexpanded proposition/unestablished:eq | contain(letBody none)',
  'second law of a structure': 'unestablished/unestablished unestablished/unestablished proposition/type:forall proposition/unestablished:eq | projection-of > type-of > contain(piBody forall/body universal)',
  'nested structure field': 'unestablished/unestablished unestablished/unestablished unestablished/unestablished | projection-of > projection-of',
  'function type universe': 'type/type:none | ',
  'universe parameter': 'type/unestablished:none | ',
  'general sort root': 'general-sort/unestablished:none | ',
  'binder over a general sort': 'proposition/type:forall proposition/general-sort:forall proposition/unestablished:eq | contain(piBody forall/body universal) > contain(piBody forall/body none)',
  'conjunction': 'proposition/unestablished:and proposition/unestablished:eq | contain(appFun/appArg and/required-left)',
  'equivalence': 'proposition/unestablished:iff proposition/unestablished:eq | contain(appArg iff/equivalent-right)',
  'implication to True': 'proposition/proposition:implies proposition/unestablished:true | contain(piBody implies/body proof)',
  'universal then existential': 'proposition/type:forall proposition/unestablished:exists proposition/unestablished:eq | contain(piBody forall/body universal) > contain(appArg/lamBody exists/predicate candidate)',
  'existential then universal': 'proposition/unestablished:exists proposition/type:forall proposition/unestablished:eq | contain(appArg/lamBody exists/predicate candidate) > contain(piBody forall/body universal)',
  'abstract existential predicate': 'proposition/unestablished:exists | ',
  'imported definition exposed': 'proposition/unestablished:unexpanded proposition/unestablished:eq | conversion',
  'imported function applied': 'unestablished/unestablished type/unestablished:none | type-of',
  'proof binder referenced by the body': 'proposition/type:forall proposition/proposition:forall proposition/unestablished:eq | contain(piBody forall/body universal) > contain(piBody forall/body proof)',
  'named theorem constant selected': 'unestablished/unestablished proposition/unestablished:eq | type-of',
  'explicit universe constant': 'type/unestablished:none | ',
  'core recursive definition head': 'unestablished/unestablished unestablished/unestablished | conversion',
  'selection inside a binder': 'proposition/unestablished:eq type/unestablished | type-of',
  'variable named like the auxiliary entry': 'unestablished/unestablished type/unestablished | type-of',
  'term inside a named theorem': 'unestablished/unestablished proposition/unestablished | type-of',
  'selection inside a local definition': 'proposition/unestablished:eq type/unestablished | type-of',
  'term under a context definition': 'proposition/unestablished:eq type/unestablished | type-of',
  'ordinary value inspected': 'term/unestablished:none type/unestablished:none | type-of',
  'two binders entered by one focus': 'proposition/type:forall unestablished/unestablished type/unestablished | contain(piBody/piBody forall/body universal,none) > type-of',
  'embedded parent field': 'unestablished/unestablished unestablished/unestablished unestablished/unestablished | projection-of > projection-of',
  'term using a lemma proved with a placeholder': 'unestablished/unestablished proposition/unestablished:eq | type-of',
  'term using a user axiom': 'unestablished/unestablished proposition/unestablished:eq | type-of',
};
const REFUSED: Record<string, string> = { 'constructor head refusal': 'head', 'aliased owner refusal': 'field-owner', 'inductive predicate head': 'head', 'opaque head': 'head' };
/** Selections refused before any acceptance-corpus row exists, with the recorded phase. */
const SEED_REFUSED: [string, string][] = [['sorry proof term selected', 'source-policy'], ['metavariable placeholder', 'occurrence-capture']];
/** Arguments of an application spine, outermost function first. */
const spine = (term: JsonValue): JsonValue[] => { const args: JsonValue[] = []; let head = term; while (Array.isArray(head) && head[0] === 'app') { args.unshift(head[2]); head = head[1]; } return [head, ...args]; };
const o = (value: unknown) => value as JsonObject, a = (value: unknown) => value as JsonValue[];
const clone = <T,>(value: T): T => JSON.parse(JSON.stringify(value)) as T;
const SORT_ZERO: JsonValue = ['sort', ['zero']];
const renumber = (c: JsonObject) => {
  const checks = a(c.checks), audits = a(c.audits); let environment = 0;
  checks.forEach((check, index) => {
    const receipt = o(check), audit = o(audits[index]); receipt.envBefore = environment;
    if (o(receipt.outcome).tag === 'accepted') { environment++; audit.result = { tag: 'available', axioms: [] }; }
    else audit.result = { tag: 'unavailable', reason: 'declaration was not installed' };
    receipt.envAfter = environment; audit.environment = environment;
  });
  c.environmentSnapshotCount = environment + 1;
};
const verdict = (value: JsonObject, stepIndex: number, local: number, tag: 'rejected' | 'unknown') => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]);
  o(a(c.checks)[Number(step.receiptStart) + local]).outcome = tag === 'unknown' ? { tag: 'unknown', message: 'timeout control' } : { tag: 'rejected', kind: 'notConvertible' };
  renumber(c);
};
const setInferred = (value: JsonObject, stepIndex: number, local: 1 | 3, sort: JsonValue) => {
  const c = o(value.checking), step = o(a(c.steps)[stepIndex]), output = o(step.output);
  (local === 1 ? o(output.formation) : o(output.domain)).inferredType = sort;
  const replayed = a(o(c.binding).expectedHistory)[stepIndex];
  if (replayed !== undefined) o(local === 1 ? o(o(replayed).candidate).formation : o(o(replayed).candidate).domain).inferredType = sort;
  const arity = Number(o(o(output.result).home).arity), index = Number(step.receiptStart) + local, receipt = o(a(c.checks)[index]), decl = clone(o(receipt.declaration));
  const rebody = (node: JsonValue, depth: number): JsonValue => {
    if (depth === 0) return sort;
    const n = a(node);
    return n[0] === 'letE' ? [n[0], n[1], n[2], n[3], rebody(n[4], depth - 1), n[5]] : [n[0], n[1], n[2], rebody(n[3], depth - 1), n[4]];
  };
  decl.type = rebody(decl.type, arity);
  receipt.declaration = decl; o(receipt.subject).declaration = decl; o(a(c.audits)[index]).subject = decl;
};
/** Mutate the chain-end record and every prior attempt that contains the step, keeping replayed checkpoints consistent. */
function mutated(row: Row, stepIndex: number, mutate: (record: JsonObject) => void) {
  const priors = row.priorAttempts.map(bundle => clone(bundle.record as unknown as JsonObject));
  const value = clone(row.response.sourceDecomposition as unknown as JsonObject);
  for (const record of [...priors, value]) if (a(o(record.checking).steps).length > stepIndex) mutate(record);
  const prior = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence, seed: null,
    attempts: row.priorAttempts.map((bundle, i) => ({ snapshot: bundle.snapshot, record: priors[i] })) });
  const record = validateSourceDecomposition(value, row.response.sourceSnapshot, prior);
  const history = validateDecompositionHistory({ ...prior, attempts: [...prior.attempts, { snapshot: row.response.sourceSnapshot, record }] });
  return occurrenceProvenance(history, record.captureId, record.operations.length - 1);
}
const end = (label: string) => { const row = ends.find(row => row.label === label); if (!row) throw Error(`missing ${label}`); return row; };

describe('acceptance capture response boundary', () => {
  it('requires a record for expected operation refusals before normal validation', () => {
    for (const response of [{}, { sourceDecompositionUnavailable: 'capture unavailable' },
      { sourceDecomposition: {}, sourceDecompositionUnavailable: 'record omitted' }]) {
      expect(() => requireRecordedRefusal(response, true, 'control')).toThrow(/explicit refusal record/);
      expect(() => requireRecordedRefusal(response, false, 'control')).not.toThrow();
    }
    // Presence only passes this boundary; the generator must still validate the record and its refusal outcome.
    expect(() => requireRecordedRefusal({ sourceDecomposition: {} }, true, 'control')).not.toThrow();
  });
});

describe.skipIf(!location)('RC3 acceptance corpus: real captures answer their reader questions', () => {
  it('validates every capture and carries a question, expected answer and outcome for every case', () => {
    expect(rows.length).toBeGreaterThan(30);
    for (const row of rows) { expect(row.seed).toBeNull(); fixture(row); }
    for (const test of manifest.cases) {
      expect(test.question.length).toBeGreaterThan(10); expect(test.expected.length).toBeGreaterThan(10);
      expect(rows.some(row => row.label === test.id)).toBe(test.executed > 0);
    }
    expect(manifest.refusals.map(refusal => refusal.id)).toEqual(SEED_REFUSED.map(([id]) => id));
    SEED_REFUSED.forEach(([, phase], index) => expect(manifest.refusals[index].refusal).toContain(`"phase":"${phase}"`));
    // The sorry term is refused before any check is attempted; no acceptance-corpus row exists for it.
    expect(manifest.refusals[0].refusal).toContain('"attempted":false'); expect(rows.some(row => row.label === 'sorry proof term selected')).toBe(false);
    // Every case is pinned by name: a renamed or added case without a pin, a pin without a case, or a label pinned twice fails here.
    const pinned = [...Object.keys(EXPECTED), ...Object.keys(REFUSED)].sort();
    expect([...new Set(ends.map(row => row.label))].sort()).toEqual(pinned);
    expect(manifest.cases.filter(test => test.executed > 0).map(test => test.id).sort()).toEqual(pinned);
    // A refused selection leaves no acceptance-corpus row; its question, expected answer, source and selection are in the case file.
    for (const refusal of manifest.refusals) for (const text of [refusal.question, refusal.expected, refusal.source, refusal.selected]) expect(text.length).toBeGreaterThan(0);
    for (const refusal of manifest.refusals) { expect(refusal.question.length).toBeGreaterThan(10); expect(refusal.expected.length).toBeGreaterThan(10); expect(pinned).not.toContain(refusal.id); }
  }, 240000);

  it('derives the expected distinction for every completed case and renders it faithfully', () => {
    for (const row of ends.filter(row => row.label in EXPECTED)) {
      const { history, record, last } = fixture(row);
      const provenance = occurrenceProvenance(history, record.captureId, last);
      expect(summarize(provenance), row.label).toBe(EXPECTED[row.label]);
      const html = renderToStaticMarkup(createElement(ProvenancePanel, { history, derived: { value: provenance }, currentOrigin: true }));
      for (const occurrence of provenance.occurrences) expect(html).toContain(`data-provenance-occurrence="${occurrence.index}" data-origin-kind="${occurrence.origin.kind}" data-origin-capture="${occurrence.origin.captureId}"`);
      for (const edge of provenance.edges) expect(html).toContain(`data-provenance-edge="${edge.from}-${edge.to}" data-relation-kind="${edge.relation.kind}"`);
      expect(html.replace(/<code>[^<]*<\/code>/g, '')).not.toMatch(/witness|proves|supplier|holds|\bvalid\b/i);
      // What the reader sees in the panel of every real case passes the stricter vocabulary.
      expect(seen(html.slice(html.indexOf('<section class="source-provenance"'))), row.label).not.toMatch(STRICT);
    }
  }, 240000);

  it('keeps refusals explicit: the stopped step refuses provenance, the prefix before it derives, and the reason is recorded', () => {
    for (const row of ends.filter(row => row.label in REFUSED)) {
      const { history, record, last } = fixture(row);
      if (record.checking.status !== 'captured') throw Error('missing checking');
      expect(record.checking.stop?.phase).toBe(REFUSED[row.label]);
      expect(record.checking.steps.at(-1)?.output.status).toBe('unavailable');
      expect(() => occurrenceProvenance(history, record.captureId, last)).toThrow(/not eligible/);
      const test = manifest.cases.find(test => test.id === row.label)!;
      expect(test.outcome).toContain(REFUSED[row.label]);
      expect(occurrenceProvenance(history, row.parent.occurrence.captureId, 0).occurrences).toHaveLength(1);
    }
    // The refused exposure of an inductive predicate leaves the proposition readable from the prefix before it.
    const inductive = fixture(end('inductive predicate head'));
    expect(summarize(occurrenceProvenance(inductive.history, inductive.record.captureId, 0))).toBe('proposition/unestablished:unexpanded | ');
  }, 240000);

  it('renders real unexpanded inspections and a selection reached through a binder without naming a candidate or a subject', () => {
    const block = (label: string, index: number) => {
      const { history, record, last } = fixture(end(label)), provenance = occurrenceProvenance(history, record.captureId, last);
      const html = renderToStaticMarkup(createElement(ProvenancePanel, { history, derived: { value: provenance }, currentOrigin: true }));
      return { provenance, text: html.split(`<li data-provenance-occurrence="${index}"`)[1].split('<details')[0] };
    };
    // An unexpanded shape records no candidate; the constant is formed as a type above Prop and nothing else is said about it.
    const constant = block('explicit universe constant', 0);
    expect(constant.provenance.occurrences[0].inspections[0]).toMatchObject({ shape: 'unexpanded', candidate: 'unexpanded', form: null, rootOutcome: 'accepted' });
    expect(constant.text).toContain('Logical inspection · shape unexpanded · root outcome accepted · no logical form is read · first appeared in');
    expect(constant.text).toContain('Formation: established as a type above Prop'); expect(constant.text).not.toMatch(/candidate|proposition|statement/);
    const applied = block('imported function applied', 1);
    expect(applied.provenance.occurrences[1].inspections[0]).toMatchObject({ shape: 'unexpanded', form: null });
    expect(applied.text).toContain('no logical form is read · first appeared in'); expect(applied.text).not.toMatch(/candidate|proposition|statement/);
    expect(applied.text).toContain('the checks that record made to produce this occurrence, also listed below as a formation outcome: the same recorded outcomes, not a second check');
    // Real read constant propositions: the constant is an identifier in code, and the visible wording passes the stricter vocabulary.
    const unproved = block('statement with sorry proof', 0), arrow = block('implication to True', 1);
    expect(unproved.provenance.occurrences[0].inspections[0]).toMatchObject({ form: 'false', rootOutcome: 'accepted' });
    expect(unproved.text).toContain('root outcome accepted · the constant <code>False</code> proposition · first appeared in');
    expect(arrow.provenance.occurrences[1].inspections[0]).toMatchObject({ form: 'true', rootOutcome: 'accepted' });
    expect(arrow.text).toContain('root outcome accepted · the constant <code>True</code> proposition · first appeared in');
    for (const item of [unproved, arrow, constant, applied]) expect(seen(item.text)).not.toMatch(STRICT);
    // The original selection reached by entering a binder: its own line lists all six checks of the extraction, worded as the event.
    const inside = block('selection inside a binder', 0);
    expect(inside.provenance.original.path).toEqual(['piBody']); expect(inside.provenance.occurrences[0].receipts).toMatchObject({ start: 0, count: 6 });
    expect(inside.text).toMatch(/<p data-provenance-own-outcomes="">Outcomes 1–6 recorded by attempt \d+ \([0-9a-f]{8}\) · the checks that record made to produce this occurrence<\/p>/);
    expect(inside.text).not.toMatch(/typing checks|for this occurrence|its context/);
  }, 240000);

  it('records an embedded parent only where the structure extends another, and an ordinary term only from its own logical-root outcome', () => {
    const fields = (label: string) => { const { record } = fixture(end(label)); if (record.checking.status !== 'captured') throw Error('missing checking');
      return record.checking.steps.map(step => step.output).filter(output => 'catalogue' in output || 'field' in output).map(output => 'catalogue' in output
        ? (output.catalogue as { fields: { name: JsonValue; parent: JsonValue | null }[] }).fields.map(entry => [a(entry.name)[2], entry.parent === null ? null : a(entry.parent)[2]])
        : [a((output.field as { name: JsonValue }).name)[2], (output.field as { parent: JsonValue | null }).parent === null ? null : a((output.field as { parent: JsonValue }).parent)[2]]); };
    expect(fields('embedded parent field')).toEqual([[['toBase', 'Base'], ['m', null]], ['toBase', 'Base'], [['n', null]], ['n', null]]);
    expect(fields('nested structure field')).toEqual([[['inner', null], ['bound', null]], ['inner', null], [['n', null]], ['n', null]]);
    // An ordinary value is established as a term by the logical-root outcome of a step on the value itself, never by its typing check.
    const value = fixture(end('ordinary value inspected')), read = occurrenceProvenance(value.history, value.record.captureId, value.last);
    expect(read.occurrences[0].formations.map(formation => [formation.source, formation.kind, formation.outcome])).toEqual([['logical', 'term', 'accepted']]);
    expect(read.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'term' }); expect(read.occurrences[0].inspections[0]).toMatchObject({ shape: 'unexpanded', form: null });
    const unread = fixture(end('variable named like the auxiliary entry')), variable = occurrenceProvenance(unread.history, unread.record.captureId, unread.last);
    expect(variable.occurrences[0].formations).toEqual([]); expect(variable.occurrences[0].formation).toEqual({ status: 'unestablished' });
  }, 240000);

  it('records the axioms of a declaration that passes capture although its proof rests on a placeholder or an axiom', () => {
    const audits = (label: string) => { const { record } = fixture(end(label)); if (record.checking.status !== 'captured') throw Error('missing checking');
      return record.checking.checks.map((check, index) => [check.label, check.outcome.tag, (record.checking as { audits: { result: { tag: string; axioms?: JsonValue[] } }[] }).audits[index].result.axioms?.map(axiom => a(axiom)[2])]); };
    // The three components that close the selected constant record the axiom; the statement's own formation receipts record none.
    const placeholder = audits('term using a lemma proved with a placeholder');
    expect(placeholder.filter(item => item[0] === 'component').map(item => item[2])).toEqual([['sorryAx'], ['sorryAx'], ['sorryAx'], []]);
    expect(placeholder.every(item => item[1] === 'accepted')).toBe(true); expect(placeholder.filter(item => item[0] !== 'component').every(item => (item[2] as unknown[]).length === 0)).toBe(true);
    expect(audits('term using a user axiom').filter(item => item[0] === 'component').map(item => item[2])).toEqual([['assumed'], ['assumed'], ['assumed'], []]);
    // The selected term itself holds no placeholder, which is why the syntactic source policy lets it through; the buffer diagnostic is kept.
    const row = end('term using a lemma proved with a placeholder');
    expect(row.parent.occurrence.checking.status === 'captured' && row.parent.occurrence.checking.selected?.term).toEqual(['const', ['str', ['anonymous'], 'claimed'], []]);
    expect(row.response.diagnostics.map(item => [item.severity, item.message])).toEqual([['warning', 'declaration uses `sorry`']]);
    // Every other case of the corpus records no axiom on any receipt.
    for (const other of ends.filter(item => !['term using a lemma proved with a placeholder', 'term using a user axiom'].includes(item.label)))
      for (const item of audits(other.label)) expect(item[2] ?? [], other.label).toEqual([]);
  }, 240000);

  it('records a planner refusal as data: the abstract predicate gains no binder', () => {
    const test = manifest.cases.find(test => test.id === 'abstract existential predicate')!;
    expect(test.executed).toBe(1); expect(test.operations).toHaveLength(2);
    const { history, record } = fixture(end('abstract existential predicate'));
    expect(record.operations).toEqual([{ kind: 'logical' }]); expect(rows.filter(row => row.label === 'abstract existential predicate')).toHaveLength(1);
    // The recorded outcome is the shared planner's own refusal, reproduced here from the saved history.
    let refused: unknown;
    try { decompositionPlan(history, record.captureId, 0, { kind: 'focus', path: ['appArg', 'lamBody'] }, 3); } catch (error) { refused = error; }
    expect(refused).toBeInstanceOf(SourceSnapshotError);
    expect(test.outcome).toBe(`plan refused after step 1: ${(refused as SourceSnapshotError).code}: ${(refused as SourceSnapshotError).message}`);
    expect((refused as SourceSnapshotError).message).toMatch(/does not address an ordinary occurrence/);
    // For the stated reason: the predicate operand sits at the argument, which the planner accepts as a focus, and the term there is not a lambda.
    const inspection = occurrenceProvenance(history, record.captureId, 0).occurrences[0].inspections[0];
    expect(inspection.operands.find(operand => operand.role === 'predicate')?.path).toEqual(['appArg']);
    expect(a(a(occurrenceProvenance(history, record.captureId, 0).occurrences[0].pair.term as JsonValue)[2])[0]).not.toBe('lam');
    expect(() => decompositionPlan(history, record.captureId, 0, { kind: 'focus', path: ['appArg'] }, 3)).not.toThrow();
  }, 240000);

  it('separates a proof binder the body references from one it does not, on two real captures', () => {
    const inner = (label: string) => { const { history, record, last } = fixture(end(label)); return occurrenceProvenance(history, record.captureId, last).occurrences[1].inspections[0]; };
    expect(inner('proof binder referenced by the body')).toMatchObject({ shape: 'forall', candidate: 'forall', form: 'forall', proofBinder: true, bodyUsesBinder: true });
    expect(inner('proof binder not referenced by the body')).toMatchObject({ shape: 'forall', candidate: 'forall', form: 'implies', proofBinder: true, bodyUsesBinder: false });
    // Negative beside the new capture: with the domain receipt rejected the binder has no role and no proof binder is read.
    const noDomain = mutated(end('proof binder referenced by the body'), 2, record => verdict(record, 2, 3, 'rejected'));
    expect(summarize(noDomain)).toBe('proposition/type:forall proposition/unestablished:forall proposition/unestablished:eq | contain(piBody forall/body universal) > contain(piBody forall/body none)');
    expect(noDomain.occurrences[1].inspections[0]).toMatchObject({ form: 'forall', proofBinder: false, bodyUsesBinder: true });
  }, 240000);

  it('keeps the statement a term carries exact: declared for a named theorem, inferred for an ascribed term, instantiated for a bare constant', () => {
    const pair = (label: string) => { const { history, record, last } = fixture(end(label)); return occurrenceProvenance(history, record.captureId, last).occurrences[0].pair; };
    const literal = (node: JsonValue) => JSON.stringify(node).match(/\["lit",\["natVal",\["nat","(\d+)"\]\]\]/g) ?? [];
    // Named theorem: the inferred type is the declared statement 2 + 2 = 4, with the literal 4 on the right side only.
    const named = pair('named theorem constant selected'), [, , namedLeft, namedRight] = spine(named.type as JsonValue);
    expect(named.term).toEqual(['const', ['str', ['anonymous'], 'two_add_two'], []]);
    expect(literal(namedLeft).join()).not.toContain('"4"'); expect(literal(namedRight).join()).toContain('"4"'); expect(namedLeft).not.toEqual(namedRight);
    // Ascribed term: within the checked pair and its closed declarations, 4 occurs only in the context port _example,
    // never in the checked term or inferred type. The separately recorded expected-type annotation also contains 4.
    const ascribed = pair('ascribed proof term selected'), [, , left, right] = spine(ascribed.type as JsonValue);
    expect(left).toEqual(right);
    expect(literal(ascribed.type as JsonValue).join()).not.toContain('"4"'); expect(literal(ascribed.term as JsonValue).join()).not.toContain('"4"');
    const expectedType = end('ascribed proof term selected').parent.snapshot.expectedType;
    expect(expectedType.status).toBe('available');
    if (expectedType.status === 'available') expect(literal(expectedType.expression).join()).toContain('"4"');
    for (const label of ['ascribed proof term selected', 'named theorem constant selected', 'proof term selected']) {
      const { home, term } = pair(label), entry = a(home.telescope);
      expect(home.arity, label).toBe(1); expect(entry[0]).toBe('port'); expect(a(entry[1])[0]).toBe('nil');
      expect(o(entry[2]).name).toEqual(['str', ['anonymous'], '_example']);
      const [, , portLeft, portRight] = spine(entry[3]);
      expect(literal(portRight).join(), label).toContain('"4"'); expect(portLeft).not.toEqual(portRight);
      expect(JSON.stringify(term), label).not.toContain('"bvar"');
    }
    expect(pair('statement selected').home.arity).toBe(0);
    // The capture records a declaration kind for every context entry; names do not determine it. Two entries can share a name, and the
    // auxiliary entry of a named theorem carries the theorem's name.
    const declarations = (label: string) => { const checking = end(label).parent.snapshot.checking; if (checking.status !== 'captured') throw Error('missing capture'); return checking.binding.context.originalDeclarations.map(item => [a(item.userName)[2], item.kind]); };
    expect(declarations('variable named like the auxiliary entry')).toEqual([['_example', 'auxDecl'], ['_example', 'default']]);
    expect(pair('variable named like the auxiliary entry').term).toEqual(['bvar', ['nat', '0']]);
    expect(declarations('term inside a named theorem')).toEqual([['helper', 'auxDecl'], ['n', 'default']]);
    expect(declarations('named theorem constant selected')).toEqual([['_example', 'auxDecl']]);
    // A local definition is a let entry of the context: entered by the selection itself, the capture records no declaration for it;
    // under a selected body, the capture records it as a context declaration of the user's, distinct from the auxiliary entry.
    const entered = pair('selection inside a local definition'), held = pair('term under a context definition');
    for (const item of [entered, held]) { expect(item.home.arity).toBe(2); expect(a(item.home.telescope)[0]).toBe('letE'); expect(a(item.home.telescope)[2]).toEqual(['str', ['anonymous'], 'f']); }
    expect(end('selection inside a local definition').parent.occurrence.path).toEqual(['letBody']); expect(end('term under a context definition').parent.occurrence.path).toEqual([]);
    expect(declarations('selection inside a local definition')).toEqual([['_example', 'auxDecl']]);
    expect(declarations('term under a context definition')).toEqual([['_example', 'auxDecl'], ['f', 'default']]);
    expect(entered.term).toEqual(held.term);
    // A selection reached by entering a binder keeps that binder in its context, after the captured context entry.
    const inside = end('selection inside a binder'), body = pair('selection inside a binder');
    expect(inside.parent.occurrence.path).toEqual(['piBody']); expect(body.home.arity).toBe(2);
    expect(a(body.home.telescope)[0]).toBe('port'); expect(o(a(body.home.telescope)[2]).name).toEqual(['str', ['anonymous'], 'x']);
    expect(o(a(a(body.home.telescope)[1])[2]).name).toEqual(['str', ['anonymous'], '_example']);
    // Bare constant: captured at universe level 1 with its own general statement.
    expect(pair('proof term selected').term).toEqual(['const', ['str', ['anonymous'], 'rfl'], [['succ', ['zero']]]]);
    expect((pair('proof term selected').type as JsonValue[])[0]).toBe('forallE');
  }, 240000);

  it('keeps each reader answer evidence-driven: the negative beside every real capture (saved-data mutations)', () => {
    // Proof binder: reject the domain receipt of the implication step; the binder loses its role and the form falls back to a plain forall.
    const noDomain = mutated(end('proof binder not referenced by the body'), 2, record => verdict(record, 2, 3, 'rejected'));
    expect(summarize(noDomain)).toBe('proposition/type:forall proposition/unestablished:forall proposition/unestablished:exists proposition/unestablished:unexpanded | contain(piBody forall/body universal) > contain(piBody forall/body none) > contain(appArg/lamBody exists/predicate candidate)');
    // False existential: reject the root receipt; no form, no candidate.
    const noRoot = mutated(end('unproved false existential'), 0, record => verdict(record, 0, 1, 'rejected'));
    expect(summarize(noRoot)).toBe('unestablished/unestablished:none proposition/unestablished:unexpanded | contain(appArg/lamBody none)');
    // General sort: a domain receipt at literal Sort zero flips the inner binder to a proof binder, so the null was evidence-driven.
    const proof = mutated(end('binder over a general sort'), 2, record => setInferred(record, 2, 3, SORT_ZERO));
    expect(summarize(proof)).toBe('proposition/type:forall proposition/proposition:forall proposition/unestablished:eq | contain(piBody forall/body universal) > contain(piBody forall/body proof)');
    // Implication: reject the domain receipt; the arrow reads as a plain forall with a role-less binder.
    const arrow = mutated(end('implication to True'), 0, record => verdict(record, 0, 3, 'unknown'));
    expect(summarize(arrow)).toBe('proposition/unestablished:forall proposition/unestablished:true | contain(piBody forall/body none)');
    // Exposure: a mutated head descriptor is refused by validation; a rejected conversion receipt leaves the conversion edge role-free and the exposed reading intact.
    const exposed = end('imported definition exposed');
    expect(() => mutated(exposed, 1, record => { const step = o(a(o(record.checking).steps)[1]); o(o(o(step.output).definition)).name = ['str', ['anonymous'], 'Other']; })).toThrow();
    const conversionRejected = mutated(exposed, 1, record => verdict(record, 1, 2, 'rejected'));
    expect(summarize(conversionRejected)).toBe(EXPECTED['imported definition exposed']);
    expect(Object.keys(conversionRejected.edges[0].relation).sort()).toEqual(['head', 'kind', 'target']);
    expect(conversionRejected.edges[0].relation.kind).toBe('conversion');
  }, 240000);

  it('captured one real v3 definition-head exposure with its conversion receipt', () => {
    const row = ends.find(row => row.label === 'imported definition exposed')!;
    const { history, record, last } = fixture(row);
    if (record.checking.status !== 'captured') throw Error('missing checking');
    const exposure = record.checking.steps.find(step => step.operation.kind === 'expose')!;
    expect(exposure.receiptCount).toBe(3);
    expect(record.checking.checks.slice(exposure.receiptStart, exposure.receiptStart + 3).map(check => check.outcome.tag)).toEqual(['accepted', 'accepted', 'accepted']);
    const provenance = occurrenceProvenance(history, record.captureId, last);
    expect(provenance.edges[0].relation).toMatchObject({ kind: 'conversion', target: 'term' });
    expect(provenance.occurrences[1].receipts).toEqual({ captureId: record.captureId, start: exposure.receiptStart, count: 3 });
  }, 240000);

  it('states the sorry case honestly: the statement is formed, the capture holds nothing of its proof, and the saved response keeps the warning', () => {
    const row = ends.find(row => row.label === 'statement with sorry proof')!;
    const { history, record, last } = fixture(row);
    const provenance = occurrenceProvenance(history, record.captureId, last);
    expect(provenance.occurrences[0].formation).toMatchObject({ status: 'established', kind: 'proposition' });
    expect(provenance.occurrences[0].inspections[0].form).toBe('false');
    expect(provenance.edges).toEqual([]);
    expect(provenance.occurrences).toHaveLength(1); expect(provenance.occurrences[0].pair.home.arity).toBe(0);
    expect(provenance.occurrences[0].pair.term).toEqual(['const', ['str', ['anonymous'], 'False'], []]);
    // None of the four capture records of the row mentions the proof, and every declaration audit is clean.
    const captured = [row.parent.snapshot, row.parent.occurrence, row.response.sourceSnapshot, row.response.sourceDecomposition];
    for (const item of captured) expect(JSON.stringify(item)).not.toMatch(/sorry/i);
    for (const item of captured) { const checking = (item as unknown as { checking: { audits?: { result: unknown }[] } }).checking; for (const audit of checking.audits ?? []) expect(audit.result).toEqual({ tag: 'available', axioms: [] }); }
    // The editor response saved with the record keeps the buffer diagnostic; it is outside the capture and read by nothing.
    expect(row.response.diagnostics).toEqual([{ line: 1, column: 0, severity: 'warning', message: 'declaration uses `sorry`' }]);
  }, 240000);
});
