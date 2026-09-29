/** Interpret only independently associated formation receipts. The process and
 * standard-core trust boundaries remain separate from this saved-record model. */
import type { JsonValue } from '../packets/packet';
import type { SnapshotReceipt } from './source-snapshot';
import { isValidatedSourceDecomposition, type SourceDecomposition } from './source-decomposition';

export type FormationKind = 'proposition' | 'type' | 'general-sort' | 'term' | 'unestablished';
export type LogicalForm = 'forall' | 'implies' | 'eq' | 'and' | 'or' | 'iff' | 'not' | 'exists' | 'true' | 'false' | 'unexpanded';
export interface LogicalInspectionReading {
  formation: FormationKind;
  inferredType: JsonValue;
  rootReceipt?: SnapshotReceipt;
  domain?: { formation: FormationKind; inferredType: JsonValue; receipt?: SnapshotReceipt };
  /** Absent unless an actual root component accepted at literal Sort.zero. */
  form?: LogicalForm;
  proofBinder: boolean;
  bodyUsesBinder?: boolean;
}

function formation(type: JsonValue, receipt?: SnapshotReceipt): FormationKind {
  if (receipt?.outcome.tag !== 'accepted') return 'unestablished';
  if (!Array.isArray(type) || type[0] !== 'sort') return 'term';
  const level = type[1] as JsonValue[];
  return level[0] === 'zero' ? 'proposition' : level[0] === 'succ' ? 'type' : 'general-sort';
}

/** A raw JSON copy is deliberately insufficient: run the shared history and
 * record validator first, which reconstructs every closed declaration. */
export function logicalInspectionReading(record: SourceDecomposition, index: number): LogicalInspectionReading | undefined {
  if (!isValidatedSourceDecomposition(record) || !Number.isSafeInteger(index) || index < 0 || record.checking.status !== 'captured') return;
  const step = record.checking.steps[index], output = step?.output;
  if (step?.operation.kind !== 'logical' || output?.status !== 'candidate' || !('formation' in output)) return;
  const localReceipt = (local: number) => local < step.receiptCount ? record.checking.status === 'captured'
    ? record.checking.checks[step.receiptStart + local] : undefined : undefined;
  const rootReceipt = localReceipt(1), rootFormation = formation(output.formation.inferredType, rootReceipt);
  const domainReceipt = localReceipt(3);
  const domain = output.domain ? { formation: formation(output.domain.inferredType, domainReceipt),
    inferredType: output.domain.inferredType, receipt: domainReceipt } : undefined;
  const proofBinder = rootFormation === 'proposition' && domain?.formation === 'proposition';
  const bodyUsesBinder = output.shape.kind === 'forall' ? output.shape.bodyUsesBinder as boolean : undefined;
  const form: LogicalForm | undefined = rootFormation !== 'proposition' ? undefined
    : output.shape.kind === 'forall' ? proofBinder && !bodyUsesBinder ? 'implies' : 'forall'
      : output.shape.kind === 'standard' ? output.shape.form as LogicalForm : 'unexpanded';
  return { formation: rootFormation, inferredType: output.formation.inferredType, rootReceipt,
    domain, form, proofBinder, bodyUsesBinder };
}

/** Formation of a type-component result term from that step's own accepted
 * component receipt A : U in the exact context. It reads no shape; only a
 * logical step supplies operator/operand structure. */
export function typeComponentFormation(record: SourceDecomposition, index: number):
  { formation: FormationKind; inferredType: JsonValue; receipt?: SnapshotReceipt } | undefined {
  if (!isValidatedSourceDecomposition(record) || !Number.isSafeInteger(index) || index < 0 || record.checking.status !== 'captured') return;
  const step = record.checking.steps[index], output = step?.output;
  if (step?.operation.kind !== 'typeComponent' || output?.status !== 'candidate') return;
  const receipt = 1 < step.receiptCount ? record.checking.checks[step.receiptStart + 1] : undefined;
  return { formation: formation(output.result.type, receipt), inferredType: output.result.type, receipt };
}
