import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { SourceSnapshot } from './source-snapshot';
import type { SourceSnapshotOrigin } from './source-origin';
import type { SourceOccurrence } from './source-occurrence';
import type { HeadExposureBundle } from './source-history';
import { decompositionPlan, validateDecompositionHistory, validateSourceDecomposition,
  type DecompositionOperation, type SourceDecompositionBundle } from './source-decomposition';
import { parseEditorMessage } from './host';
import { savedSourceSnapshot } from './SourceSnapshotReading';
import { logicalInspectionReading } from './logical-inspection-reading';
import { decompositionReading } from './source-decomposition-reading';
import { deriveProvenance, guidedLogicalRoot } from './SourceProvenanceReading';
import { compileReading } from '../reading/compiler';
import { compileReadingCues } from '../reading/cues';

interface Row {
  label: string; parent: { snapshot: SourceSnapshot; origin: SourceSnapshotOrigin; occurrence: SourceOccurrence };
  seed: HeadExposureBundle | null; priorAttempts: SourceDecompositionBundle[]; operation: DecompositionOperation;
  previousCaptureId: string; parentStepIndex: number;
  response: { sourceSnapshot: SourceSnapshot; sourceSnapshotOrigin: SourceSnapshotOrigin; sourceDecomposition: SourceDecompositionBundle['record'] };
}
const location = process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES;
const rows: Row[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
const o = (value: unknown) => value as JsonObject;
const a = (value: unknown) => value as JsonValue[];
const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
function fixture(row: Row) {
  const history = validateDecompositionHistory({ snapshot: row.parent.snapshot, occurrence: row.parent.occurrence,
    seed: row.seed ? { snapshot: row.seed.snapshot, record: row.seed.record } : null,
    attempts: row.priorAttempts.map(({ snapshot, record }) => ({ snapshot, record })) });
  return { history, record: validateSourceDecomposition(row.response.sourceDecomposition, row.response.sourceSnapshot, history) };
}
/** The guided root comes from the accepted provenance module over a history that includes the record. */
function rootFor(history: ReturnType<typeof validateDecompositionHistory>, snapshot: SourceSnapshot, record: ReturnType<typeof validateSourceDecomposition>, index: number) {
  const full = validateDecompositionHistory({ ...history, attempts: [...history.attempts, { snapshot, record }] });
  return guidedLogicalRoot(deriveProvenance(full, record.captureId, index));
}
function find(kind: DecompositionOperation['kind']) {
  const row = rows.find(row => row.label === 'literal Rotor law' && row.operation.kind === kind);
  if (!row) throw Error(`Missing actual ${kind} record`);
  return row;
}
function message(row: Row) {
  const origin = row.parent.origin;
  return { type: 'statementlens.error', requestId: '4', message: 'Independent guided export unavailable.',
    document: { ...origin.document!, fileName: new URL(origin.document!.uri).pathname, selection: origin.selection },
    sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: origin, sourceOccurrence: row.parent.occurrence,
    decompositions: [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }] };
}

describe.skipIf(!location)('actual v3 editor formation transport', () => {
  it('validates every fresh record, exact declaration and retained prefix without changing its history', () => {
    expect(rows).toHaveLength(50);
    let checks = 0;
    for (const row of rows) {
      const before = canonical(row), { record } = fixture(row);
      expect(record.schema).toBe('definograph.source-decomposition.v3');
      if (record.checking.status !== 'captured') throw Error('Missing checking');
      checks += record.checking.checks.length;
      for (const step of record.checking.steps) if (step.output.status === 'candidate') {
        if (step.operation.kind === 'typeComponent') {
          expect(step.output.result.home).toEqual(step.input.home);
          expect(step.output.result.term).toEqual(step.input.type);
        }
        if (step.operation.kind === 'logical') expect(step.output.result).toEqual(step.input);
      }
      expect(canonical(row)).toBe(before);
    }
    expect(checks).toBe(699);
  }, 60000);

  it('admits live bundles but exports only revision6 with unverified saved provenance', () => {
    for (const row of rows.filter((row, index) => rows[index + 1]?.label !== row.label)) {
      const msg = message(row), parsed = parseEditorMessage(msg);
      expect(parsed?.type).toBe('statementlens.error');
      if (!parsed || parsed.type === 'statementlens.status') throw Error('Missing parsed message');
      expect(Object.isFrozen(parsed.decompositions)).toBe(true);
      const saved = savedSourceSnapshot(row.parent.snapshot, row.parent.origin, row.parent.occurrence,
        row.seed ?? undefined, undefined, msg.decompositions);
      expect(saved.version).toBe(6);
      expect(saved.provenance).toBe('unverified-saved-record');
      expect(saved.decompositions).toEqual(msg.decompositions);
    }
  }, 60000);

  it('rejects changed type-component input, home and receipt associations', () => {
    const row = find('typeComponent'), { history } = fixture(row);
    for (const mutation of ['term', 'home', 'receipt'] as const) {
      const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
      const c = o(value.checking), output = o(o(a(c.steps).at(-1)).output);
      if (mutation === 'term') o(output.result).term = ['sort', ['zero']];
      if (mutation === 'home') o(o(output.result).home).arity = 0;
      if (mutation === 'receipt') o(o(a(c.checks).at(-1)).declaration).value = ['sort', ['zero']];
      expect(() => validateSourceDecomposition(value, row.response.sourceSnapshot, history)).toThrow();
    }
  });

  it.each([0, 1, 2, 3, 4])('retains exactly %s logical callbacks after interruption', count => {
    const row = find('logical'), { history } = fixture(row);
    const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
    const c = o(value.checking), step = o(a(c.steps).at(-1)), output = o(step.output);
    expect(o(output.shape).kind).toBe('forall');
    const total = Number(step.receiptStart) + count;
    step.receiptCount = count; step.replay = 'not-compared';
    output.checking = { status: 'error', reason: 'callback interruption' };
    c.stop = { status: 'unavailable', kind: 'error', phase: 'operation-checking', reason: 'callback interruption' };
    c.checks = a(c.checks).slice(0, total); c.audits = a(c.audits).slice(0, total);
    c.environmentSnapshotCount = Number(o(a(c.checks).at(-1)).envAfter) + 1;
    const validated = validateSourceDecomposition(value, row.response.sourceSnapshot, history);
    expect(validated).toEqual(value);
    expect(logicalInspectionReading(validated, Number(step.index))?.formation).toBe(count >= 2 ? 'proposition' : 'unestablished');
    expect(logicalInspectionReading(validated, Number(step.index))?.domain?.formation).toBe(count >= 4 ? 'type' : 'unestablished');
  });

  it('distinguishes proposition formation from positive-sort types and refuses unvalidated receipt claims', () => {
    const law = fixture(find('logical')).record;
    expect(logicalInspectionReading(law, 3)).toMatchObject({ formation: 'proposition', form: 'forall', proofBinder: false });
    expect(logicalInspectionReading(structuredClone(law), 3)).toBeUndefined();
    const ordinary = fixture(rows.find(row => row.label === 'ordinary function type')!).record;
    expect(logicalInspectionReading(ordinary, 0)).toMatchObject({ formation: 'type', proofBinder: false });
    expect(logicalInspectionReading(ordinary, 0)?.form).toBeUndefined();
    const existential = fixture(rows.find(row => row.label === 'abstract existential predicate')!).record;
    expect(logicalInspectionReading(existential, 0)).toMatchObject({ formation: 'proposition', form: 'exists' });
  });

  it('uses the shared reader for exactly one logical layer and retains every exact source position', () => {
    for (const row of rows) {
      const { history, record } = fixture(row);
      if (record.checking.status !== 'captured') throw Error('Missing checking');
      for (const step of record.checking.steps.filter(step => step.operation.kind === 'logical')) {
        const evidence = logicalInspectionReading(record, step.index)!;
        const root = rootFor(history, row.response.sourceSnapshot, record, step.index);
        const model = decompositionReading(record, step.index, 'term', root)!;
        expect(model.document, model.reason).toBeDefined();
        expect(model.document!.presentation?.logicalRootNodeId).toBe(evidence.form ? model.targetNodeId : undefined);
        const reading = compileReading(model.document!);
        const target = reading.nodes.find(node => node.id === model.targetNodeId)!;
        if (evidence.form === 'forall') expect(target.binder?.role).toBe('universal');
        if (evidence.form === 'eq') expect(model.document!.relations.filter(relation => relation.kind === 'equality')).toHaveLength(1);
        for (const node of reading.nodes) {
          expect(node.assumptionNodeIds).toEqual([]);
          if (node.id !== model.targetNodeId) expect(['forall', 'exists', 'and', 'or', 'iff', 'not', 'implies']).not.toContain(node.kind);
        }
        for (const source of Object.values(model.sourceById)) {
          const actual = source.path.reduce<unknown>((value, part) => (value as Record<string | number, unknown>)[part], record);
          expect(canonical(source.syntax)).toBe(canonical(actual));
        }
        expect(decompositionReading(record, step.index, 'type', root)?.document?.presentation?.logicalRootNodeId).toBeUndefined();
      }
    }
  }, 60000);

  it('keeps existential candidates within their literal lambda and folds an abstract predicate', () => {
    const concreteRow = rows.find(row => row.label === 'existential owner' && row.operation.kind === 'logical')!, concreteFixture = fixture(concreteRow), concrete = concreteFixture.record;
    const model = decompositionReading(concrete, 0, 'term', rootFor(concreteFixture.history, concreteRow.response.sourceSnapshot, concrete, 0))!;
    const reading = compileReading(model.document!), target = reading.nodes.find(node => node.id === model.targetNodeId)!;
    expect(target.kind).toBe('exists'); expect(target.binder?.role).toBe('existential');
    const binderSource = model.sourceById[target.binder!.binderId];
    expect(a(binderSource.syntax)[0]).toBe('lam');
    const choice = model.document!.choices.find(choice => choice.binderId === target.binder!.binderId)!;
    expect(choice.dependsOn).toEqual(choice.availableObjectIds);
    const cues = compileReadingCues(reading, model.document!);
    expect(cues.cues.find(cue => cue.nodeId === target.id)?.role).toBe('candidate');
    expect(cues.cues.some(cue => cue.role === 'witness')).toBe(false);
    const abstractRow = rows.find(row => row.label === 'abstract existential predicate')!, abstractFixture = fixture(abstractRow), abstract = abstractFixture.record;
    const folded = decompositionReading(abstract, 0, 'term', rootFor(abstractFixture.history, abstractRow.response.sourceSnapshot, abstract, 0))!, foldedReading = compileReading(folded.document!);
    const foldedTarget = foldedReading.nodes.find(node => node.id === folded.targetNodeId)!;
    expect(foldedTarget.binder).toBeUndefined(); expect(foldedTarget.children).toEqual([]);
    expect(foldedTarget.phrase).toContain('unexpanded predicate');
  });

  it.each(['rejected', 'unknown'] as const)('gates only the exact component outcome when a context or component is %s', verdict => {
    const row = find('logical'), { history } = fixture(row);
    for (const local of [0, 1]) {
      const value = structuredClone(row.response.sourceDecomposition) as unknown as JsonObject;
      const c = o(value.checking), step = o(a(c.steps).at(-1));
      const checks = a(c.checks), audits = a(c.audits), changed = Number(step.receiptStart) + local;
      o(checks[changed]).outcome = verdict === 'unknown' ? { tag: 'unknown', message: 'timeout control' } : { tag: 'rejected', kind: 'notConvertible' };
      let environment = 0;
      checks.forEach((check, index) => {
        const receipt = o(check), audit = o(audits[index]);
        receipt.envBefore = environment;
        if (o(receipt.outcome).tag === 'accepted') environment++;
        else audit.result = { tag: 'unavailable', reason: 'declaration was not installed' };
        receipt.envAfter = environment; audit.environment = environment;
      });
      c.environmentSnapshotCount = environment + 1;
      const validated = validateSourceDecomposition(value, row.response.sourceSnapshot, history);
      const reading = logicalInspectionReading(validated, Number(step.index));
      expect(reading?.formation).toBe(local === 0 ? 'proposition' : 'unestablished');
      expect(reading?.form).toBe(local === 0 ? 'forall' : undefined);
      expect(reading?.rootReceipt?.outcome.tag).toBe(local === 0 ? 'accepted' : verdict);
      // The guided root now comes from the accepted module: a rejected root outcome beside the accepted type-component receipt keeps the established reading.
      const model = decompositionReading(validated, Number(step.index), 'term', rootFor(history, row.response.sourceSnapshot, validated, Number(step.index)))!;
      expect(model.document?.presentation?.logicalRootNodeId).toBe(model.targetNodeId);
    }
  });

  it('does not allow old profiles to reinterpret a new operation or a v3 parent', () => {
    const row = find('logical'), { history } = fixture(row);
    for (const version of [1, 2] as const) {
      expect(() => decompositionPlan(history, row.previousCaptureId, row.parentStepIndex, { kind: 'fields' }, version)).toThrow();
      expect(() => decompositionPlan(history, row.parent.occurrence.captureId, 0, { kind: 'logical' }, version)).toThrow();
      expect(() => decompositionPlan(history, row.parent.occurrence.captureId, 0, { kind: 'typeComponent' }, version)).toThrow();
    }
    for (const kind of ['logical', 'typeComponent'] as const) {
      expect(decompositionPlan(history, row.parent.occurrence.captureId, 0, { kind }, 3).expectedHistory).toEqual([]);
    }
  });
});
