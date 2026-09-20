import type { Analysis, Expr } from '../core/types';
import { selectedNodeIds } from './planner';
import type { SemanticDocument } from './types';

export interface InterpretationGap {
  readonly id: string;
  readonly name: string;
  readonly constant?: string;
  readonly kind: 'definition' | 'opaque' | 'symbolic';
  readonly nodeIds: readonly string[];
  readonly scopeIds: readonly string[];
  readonly occurrences: number;
  readonly canExpand: boolean;
  readonly module?: string;
  readonly retainedRelationIds: readonly string[];
}
export interface InterpretationReport {
  readonly schemaVersion: 1;
  readonly selectedNodeId: string;
  readonly clauses: { readonly total: number; readonly interpreted: number; readonly partial: number; readonly structural: number };
  readonly vocabulary: readonly { readonly id: string; readonly label: string; readonly relationCount: number }[];
  readonly gaps: readonly InterpretationGap[];
  readonly diagnostics: readonly string[];
}

const vocabularyLabels: Record<string, string> = {
  sets: 'Sets and membership', mappings: 'Maps and applications', relations: 'Equality and order',
  metric: 'Metric regions and distance', graphs: 'Graphs and coloring',
};

/** Report unknown symbols without treating their display names as mathematical meaning. */
function gapHead(expression: Expr): { name: string; constant?: string; kind: InterpretationGap['kind'] } {
  let head = expression;
  while (head.kind === 'app') head = head.fn;
  if (head.kind === 'const') return { name: head.name, constant: head.name, kind: 'definition' };
  if (head.kind === 'var') return { name: head.name, kind: 'symbolic' };
  if (head.kind === 'opaque') return { name: head.text, kind: 'opaque' };
  return { name: 'Uninterpreted expression', kind: 'symbolic' };
}

/** Coverage is relative to the installed vocabulary. It is neither truth nor an
 * estimate of how much mathematics a reader will understand. Branches stay separate. */
export function compileInterpretationReport(document: SemanticDocument, definitions: Analysis['definitions'] = [], selectedNodeId = document.tree.id): InterpretationReport {
  const selected = selectedNodeIds(document.tree, selectedNodeId);
  if (!selected.size) throw new Error(`Unknown statement node: ${selectedNodeId}`);
  const clauses = document.coverage.filter(fragment => selected.has(fragment.nodeId));
  const vocabulary = new Map<string, number>();
  for (const relation of document.relations) if (selected.has(relation.nodeId) && relation.fidelity !== 'structural') {
    vocabulary.set(relation.pluginId, (vocabulary.get(relation.pluginId) ?? 0) + 1);
  }
  const groups = new Map<string, { head: ReturnType<typeof gapHead>; nodes: Set<string>; scopes: Set<string>; relations: Set<string>; occurrences: number }>();
  for (const region of document.opaqueRegions) if (selected.has(region.nodeId)) {
    const head = gapHead(region.expression);
    // Bound variables with the same printed name are distinct gaps. Constants can
    // be grouped for reporting, while their exact scopes and occurrence IDs remain.
    let expressionHead = region.expression;
    while (expressionHead.kind === 'app') expressionHead = expressionHead.fn;
    const key = head.constant ? `constant:${head.constant}` : expressionHead.kind === 'var' ? `variable:${expressionHead.id}` : `region:${region.id}`;
    let group = groups.get(key);
    if (!group) { group = { head, nodes: new Set(), scopes: new Set(), relations: new Set(), occurrences: 0 }; groups.set(key, group); }
    group.occurrences++;
    group.nodes.add(region.nodeId); group.scopes.add(region.scopeId);
    region.supportedRelationIds.forEach(id => group.relations.add(id));
  }
  const byName = new Map(definitions.map(definition => [definition.name, definition]));
  const gaps: InterpretationGap[] = [...groups].map(([id, group]) => {
    const definition = group.head.constant ? byName.get(group.head.constant) : undefined;
    return { id, ...group.head, nodeIds: [...group.nodes], scopeIds: [...group.scopes], occurrences: group.occurrences,
      canExpand: definition?.canExpand === true, module: definition?.module, retainedRelationIds: [...group.relations] };
  });
  return { schemaVersion: 1, selectedNodeId,
    clauses: { total: clauses.length, interpreted: clauses.filter(c => c.status === 'interpreted').length,
      partial: clauses.filter(c => c.status === 'partial').length, structural: clauses.filter(c => c.status === 'structural').length },
    vocabulary: [...vocabulary].map(([id, relationCount]) => ({ id, label: vocabularyLabels[id] ?? id, relationCount })),
    gaps, diagnostics: document.diagnostics };
}
