import { headName } from '../core/expression';
import type { Expr } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';

/** Slots belong to this schematic only. A slot without an object is not a vertex
 * of a chosen graph and must never acquire an interactive semantic object ID. */
export interface GraphEndpoint {
  readonly id: string;
  readonly label: string;
  readonly object?: SemanticObject;
  readonly role: 'source-object' | 'arbitrary-slot';
}
export interface GraphPalette {
  readonly kind: 'finite' | 'symbolic';
  readonly object: SemanticObject;
  /** Exact decimal cardinality, without floating-point conversion. */
  readonly count?: string;
  /** Displayed labels of Fin n, never a choice of vertex colors. */
  readonly labels: readonly string[];
  readonly omittedCount?: string;
}
export interface GraphConstraintModel {
  readonly kind: 'adjacency' | 'coloring' | 'colorable' | 'map';
  readonly relation: SemanticRelation;
  readonly nodeId: string;
  readonly scopeId: string;
  readonly graph: SemanticObject;
  readonly targetGraph?: SemanticObject;
  readonly coloring?: SemanticObject;
  readonly map?: SemanticObject;
  readonly mapKind?: 'homomorphism' | 'embedding';
  readonly palette?: GraphPalette;
  readonly endpoints: readonly [GraphEndpoint, GraphEndpoint];
  readonly sameEndpoint: boolean;
  readonly application?: { readonly vertex: SemanticObject; readonly value: SemanticObject };
  /** Related expression stages are exact-source and exact-scope only. */
  readonly relatedRelationIds: readonly string[];
  readonly omittedRelatedRelationCount: number;
  readonly title: string;
  readonly explanation: string;
}

const PALETTE_LIMIT = 8;
const RELATED_LIMIT = 48;

function literalNatural(expression: Expr): bigint | undefined {
  if (expression.kind !== 'literal') return;
  if (typeof expression.value === 'number') return Number.isSafeInteger(expression.value) && expression.value >= 0 ? BigInt(expression.value) : undefined;
  // The literal is already typed by Lean. Bound conversion independently of
  // renderer capacity, and retain unusually large values symbolically.
  if (expression.value.length > 128 || !/^\d+$/.test(expression.value)) return;
  return BigInt(expression.value);
}

/** Only exact exported literals are counted. An arbitrary n stays symbolic;
 * there is no scenario evaluation or parsing of displayed type text. */
function naturalBound(expression: Expr): bigint | undefined {
  const direct = literalNatural(expression);
  if (direct !== undefined) return direct;
  if (expression.kind !== 'app' || expression.fn.kind !== 'const' || expression.fn.canonical !== true || headName(expression) !== 'OfNat.ofNat' || expression.standard !== true || expression.args.length !== 3) return;
  if (expression.typeDescriptor?.kind !== 'natural') return;
  return literalNatural(expression.args[1]);
}

function palette(object: SemanticObject, isBound: boolean): GraphPalette {
  const expression = object.expression;
  let count: bigint | undefined;
  if (isBound) count = naturalBound(expression);
  else if (expression.kind === 'app' && expression.fn.kind === 'const' && expression.fn.canonical === true && headName(expression) === 'Fin' && expression.args.length === 1) count = naturalBound(expression.args[0]);
  if (count === undefined) return { kind: 'symbolic', object, labels: [] };
  const shown = Number(count < BigInt(PALETTE_LIMIT) ? count : BigInt(PALETTE_LIMIT));
  return { kind: 'finite', object, count: count.toString(), labels: Array.from({ length: shown }, (_, index) => String(index)), ...(count > BigInt(shown) ? { omittedCount: (count - BigInt(shown)).toString() } : {}) };
}

function isUntrustedHead(expression: Expr): boolean {
  let head = expression;
  // The semantic exporter already bounds expressions; this loop also handles a
  // malformed cyclic application without allowing an interpretation through it.
  const seen = new Set<Expr>();
  while (head.kind === 'app') {
    if (seen.has(head)) return true;
    seen.add(head); head = head.fn;
  }
  return head.kind === 'const' && head.canonical === false;
}

/** Consume recognized graph semantics, never theorem names or printed types.
 * No graph instance, edge set, vertex cardinality, or coloring is synthesized. */
export function compileGraphConstraint(document: SemanticDocument, relation: SemanticRelation, relations: readonly SemanticRelation[] = document.relations): GraphConstraintModel | undefined {
  const relationKind: string = relation.kind;
  if (!['graph-adjacency', 'graph-coloring', 'graph-colorable', 'graph-map'].includes(relationKind) || relation.fidelity === 'structural' || isUntrustedHead(relation.expression)) return;
  const scope = document.scopes.find(scope => scope.id === relation.scopeId);
  if (!scope || scope.nodeId !== relation.nodeId) return;
  const objects = new Map(document.objects.map(object => [object.id, object]));
  if (new Set(relation.ports.map(port => port.role)).size !== relation.ports.length || relation.ports.some(port => !objects.has(port.objectId))) return;
  if (relation.ports.some(port => objects.get(port.objectId)!.binder && !scope.objectIds.includes(port.objectId))) return;
  const port = (role: string): SemanticObject | undefined => {
    const ports = relation.ports.filter(port => port.role === role);
    return ports.length === 1 ? objects.get(ports[0].objectId) : undefined;
  };
  const kind = relationKind === 'graph-adjacency' ? 'adjacency' : relationKind === 'graph-coloring' ? 'coloring' : relationKind === 'graph-colorable' ? 'colorable' : 'map';
  const graph = port(kind === 'map' ? 'source graph' : 'graph');
  if (!graph) return;
  const knownIds = new Set(relation.ports.map(port => port.objectId));
  const related = relations.filter(candidate => candidate.nodeId === relation.nodeId && candidate.scopeId === relation.scopeId && candidate.id !== relation.id && candidate.ports.some(port => knownIds.has(port.objectId)));
  const relatedRelationIds = related.slice(0, RELATED_LIMIT).map(relation => relation.id);
  const actual = (object: SemanticObject): GraphEndpoint => ({ id: object.id, label: object.label, object, role: 'source-object' });
  const slot = (index: 1 | 2): GraphEndpoint => ({ id: `slot:${relation.id}:${index}`, label: index === 1 ? 'v₁' : 'v₂', role: 'arbitrary-slot' });
  const base = { relation, nodeId: relation.nodeId, scopeId: relation.scopeId, graph, relatedRelationIds, omittedRelatedRelationCount: Math.max(0, related.length - RELATED_LIMIT) };
  if (kind === 'adjacency') {
    const left = port('left vertex'), right = port('right vertex');
    if (!left || !right) return;
    return { ...base, kind, endpoints: [actual(left), actual(right)], sameEndpoint: left.id === right.id,
      title: 'Adjacency condition', explanation: 'The condition requires these named vertices to be adjacent in this graph. Read it within its enclosing assumptions, alternatives, or negation.' };
  }
  const endpoints: readonly [GraphEndpoint, GraphEndpoint] = [slot(1), slot(2)];
  if (kind === 'colorable') {
    const bound = port('color bound');
    if (!bound) return;
    const colors = palette(bound, true);
    return { ...base, kind, endpoints, sameEndpoint: false, palette: colors,
      title: 'Existence of a proper coloring', explanation: colors.count === '0' ? 'A map into an empty palette can exist only if the vertex type is empty. For an empty vertex type, the edge rule is vacuous.' : 'This condition asks for a map into the available color labels such that adjacent vertices receive different labels. A coloring is not chosen here.' };
  }
  const vertex = port(kind === 'map' ? 'source vertex' : 'vertex'), value = port(kind === 'map' ? 'target vertex' : 'color');
  if (!!vertex !== !!value) return;
  if (kind === 'coloring') {
    const coloring = port('coloring'), colors = port('colors');
    if (!coloring || !colors) return;
    const paletteModel = palette(colors, false);
    return { ...base, kind, endpoints, sameEndpoint: false, coloring, palette: paletteModel, ...(vertex && value ? { application: { vertex, value } } : {}),
      title: vertex ? 'Apply the proper coloring' : 'A proper coloring', explanation: paletteModel.count === '0' ? 'A coloring into the empty palette has an empty vertex type. There are no endpoints to assign; the edge rule is vacuous.' : 'This typed coloring assigns a label to each vertex. For every adjacent pair, its two assigned labels must differ.' };
  }
  const targetGraph = port('target graph'), map = port('map');
  if (!targetGraph || !map) return;
  const mapKind = relation.graphMapKind === 'embedding' ? 'embedding' : relation.graphMapKind === 'homomorphism' ? 'homomorphism' : undefined;
  return { ...base, kind, endpoints, sameEndpoint: false, targetGraph, map, mapKind, ...(vertex && value ? { application: { vertex, value } } : {}),
    title: mapKind === 'embedding' ? 'A graph embedding' : 'An edge-preserving graph map',
    explanation: mapKind === 'embedding' ? 'Adjacency is preserved and reflected, and distinct vertices have distinct images.' : mapKind === 'homomorphism' ? 'Every source edge must map to a target edge. Other vertex pairs may share an image; injectivity is not required.' : 'Every source edge must map to a target edge. Any additional properties remain in the source type.' };
}
