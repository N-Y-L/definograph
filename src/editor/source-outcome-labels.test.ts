import { describe, expect, it } from 'vitest';
import { operationOutcomeLabel } from './source-outcome-labels';
import type { DecompositionOperation } from './source-decomposition';

type Kind = DecompositionOperation['kind'];

// Independent expected wording for the recorded operation schedules. Do not
// import or enumerate the production schedules: changing them must not change
// this oracle. Positions are local to the operation, not global receipt IDs.
const EXPECTED: readonly (readonly [Kind, string, number, string])[] = [
  ['focus', 'context', 0, 'Focused context'],
  ['focus', 'component', 1, 'Focused component'],
  ['typeComponent', 'context', 0, 'Type-component context'],
  ['typeComponent', 'component', 1, 'Type component'],
  ['expose', 'context', 0, 'Result context'],
  ['expose', 'component', 1, 'Result component'],
  ['expose', 'conversion', 2, 'Definition-head conversion'],
  ['project', 'context', 0, 'Field context'],
  ['project', 'component', 1, 'Field component'],
  ['project', 'conversion', 2, 'Field projection conversion'],
  ['logical', 'logical.root.context', 0, 'Logical root context'],
  ['logical', 'logical.root.component', 1, 'Logical root component'],
  ['logical', 'logical.domain.context', 2, 'Binder-domain context'],
  ['logical', 'logical.domain.component', 3, 'Binder-domain component'],
];

describe('recorded operation outcome labels', () => {
  it.each(EXPECTED)('%s / %s / position %i names that recorded check', (kind, label, position, expected) => {
    expect(operationOutcomeLabel(kind, label, position)).toBe(expected);
  });

  it('requires operation, recorded label and local position to agree', () => {
    const kinds: readonly Kind[] = ['focus', 'typeComponent', 'expose', 'project', 'logical', 'fields'];
    const labels = ['context', 'component', 'conversion', 'logical.root.context',
      'logical.root.component', 'logical.domain.context', 'logical.domain.component'];
    for (const kind of kinds) for (const label of labels) for (const position of [0, 1, 2, 3, 4, 6]) {
      const expected = EXPECTED.find(row => row[0] === kind && row[1] === label && row[2] === position);
      expect(operationOutcomeLabel(kind, label, position), `${kind}/${label}/${position}`)
        .toBe(expected?.[3] ?? `Recorded ${label} · position ${position + 1}`);
    }
  });

  it.each([
    ['logical', 'conversion', 2, 'Recorded conversion · position 3'],
    ['expose', 'logical.domain.context', 2, 'Recorded logical.domain.context · position 3'],
    ['logical', 'logical.domain.context', 0, 'Recorded logical.domain.context · position 1'],
    ['logical', 'logical.domain.component', 2, 'Recorded logical.domain.component · position 3'],
    ['fields', 'component', 0, 'Recorded component · position 1'],
    ['focus', 'future.component', 1, 'Recorded future.component · position 2'],
    ['typeComponent', 'component', 9, 'Recorded component · position 10'],
  ] as const)('keeps an unexpected schedule explicit: %s / %s / %i', (kind, label, position, expected) => {
    expect(operationOutcomeLabel(kind, label, position)).toBe(expected);
  });

  // Receipt lists are prefixes when native checking stops. These are recorded
  // label sequences, not synthetic accepted outcomes or claims of completion.
  // Rendering tests separately establish that missing checks are stated and
  // global Outcome n references resolve to visible numbered rows.
  it.each([
    ['no retained checks', [], []],
    ['stopped after root context', ['logical.root.context'], ['Logical root context']],
    ['root-only logical check', ['logical.root.context', 'logical.root.component'],
      ['Logical root context', 'Logical root component']],
    ['stopped before domain component', ['logical.root.context', 'logical.root.component', 'logical.domain.context'],
      ['Logical root context', 'Logical root component', 'Binder-domain context']],
    ['complete binder schedule', ['logical.root.context', 'logical.root.component', 'logical.domain.context', 'logical.domain.component'],
      ['Logical root context', 'Logical root component', 'Binder-domain context', 'Binder-domain component']],
  ] as const)('%s preserves the labels of exactly the recorded logical prefix', (_name, recorded, expected) => {
    const actual = recorded.map((label, local) => operationOutcomeLabel('logical', label, local));
    expect(actual).toEqual(expected);
    expect(actual.some(label => /conversion/i.test(label))).toBe(false);
  });

  it('does not renumber a domain check into a root check after a gap', () => {
    const observed = ['logical.root.context', 'logical.domain.context', 'logical.domain.component'];
    expect(observed.map((label, local) => operationOutcomeLabel('logical', label, local))).toEqual([
      'Logical root context',
      'Recorded logical.domain.context · position 2',
      'Recorded logical.domain.component · position 3',
    ]);
  });
});
