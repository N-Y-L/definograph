import type { SemanticRelation } from './types';

/** Common input→map→output composition shared by independently audited vocabularies.
 * This records expression evaluation order, never an inverse law or membership fact. */
export interface ApplicationFlow {
  readonly functionId: string;
  readonly inputIds: readonly string[];
  readonly outputId: string;
  readonly direction: 'forward' | 'inverse';
}
export function applicationFlow(relation: SemanticRelation | undefined): ApplicationFlow | undefined {
  if (!relation || relation.fidelity === 'structural') return;
  const one = (role: string) => {
    const matches = relation.ports.filter(port => port.role === role);
    return matches.length === 1 ? matches[0]!.objectId : undefined;
  };
  let fn: string | undefined, output: string | undefined, inputs: readonly string[] = [], direction: ApplicationFlow['direction'] = 'forward';
  if (relation.kind === 'application') {
    fn = one('function'); output = one('output');
    const ordered = relation.ports.filter(port => /^input [1-9]\d*$/.test(port.role)).sort((a, b) => Number(a.role.slice(6)) - Number(b.role.slice(6)));
    if (ordered.some((port, index) => port.role !== `input ${index + 1}`)) return;
    inputs = ordered.map(port => port.objectId);
  } else if (relation.kind === 'restricted-application') {
    if (!relation.restrictedDirection) return;
    fn = one('map'); output = one('output'); inputs = one('input') ? [one('input')!] : []; direction = relation.restrictedDirection;
  } else if (relation.kind === 'graph-coloring') {
    fn = one('coloring'); output = one('color'); inputs = one('vertex') ? [one('vertex')!] : [];
  } else if (relation.kind === 'graph-map') {
    fn = one('map'); output = one('target vertex'); inputs = one('source vertex') ? [one('source vertex')!] : [];
  }
  return fn && output && inputs.length ? { functionId: fn, inputIds: inputs, outputId: output, direction } : undefined;
}
