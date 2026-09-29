import type { DecompositionOperation } from './source-decomposition';

/** Labels identify the recorded operation, label and local receipt position.
 * An unexpected schedule stays explicit rather than inheriting another check's title. */
const schedules = Object.freeze({
  focus: [['context', 'Focused context'], ['component', 'Focused component']],
  typeComponent: [['context', 'Type-component context'], ['component', 'Type component']],
  expose: [['context', 'Result context'], ['component', 'Result component'], ['conversion', 'Definition-head conversion']],
  project: [['context', 'Field context'], ['component', 'Field component'], ['conversion', 'Field projection conversion']],
  logical: [['logical.root.context', 'Logical root context'], ['logical.root.component', 'Logical root component'],
    ['logical.domain.context', 'Binder-domain context'], ['logical.domain.component', 'Binder-domain component']],
  fields: [],
} satisfies Record<DecompositionOperation['kind'], string[][]>);
export function operationOutcomeLabel(kind: DecompositionOperation['kind'], label: string, position: number): string {
  const expected = schedules[kind][position];
  return expected?.[0] === label ? expected[1] : `Recorded ${label} · position ${position + 1}`;
}
