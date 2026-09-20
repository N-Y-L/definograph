import type { Expr } from '../core/types';
import type { SemanticDocument, SemanticObject, SemanticRelation } from '../semantic/types';

export interface RestrictedRegion {
  readonly role: 'source' | 'target';
  readonly label: string;
  /** Only a projection present in this exact source clause has an object ID. */
  readonly object?: SemanticObject;
  readonly empty: boolean;
}

/** Shared containment/map/law vocabulary, independent of Lean bundle names.
 * A future chart or trivialization adapter can compose the same structure. */
export interface RestrictedMapStructure {
  readonly map: SemanticObject;
  /** Carriers and region roles always use the original map's orientation. */
  readonly sourceCarrier: SemanticObject;
  readonly targetCarrier: SemanticObject;
  readonly source: RestrictedRegion;
  readonly target: RestrictedRegion;
  readonly direction: 'forward' | 'inverse';
  readonly sameCarrier: boolean;
  readonly properties: {
    readonly sourceOpen: boolean;
    readonly targetOpen: boolean;
    readonly forwardContinuousOnSource: boolean;
    readonly inverseContinuousOnTarget: boolean;
  };
}

export interface RestrictedMapModel extends RestrictedMapStructure {
  readonly kind: 'equivalence' | 'region' | 'application';
  readonly relation: SemanticRelation;
  readonly nodeId: string;
  readonly scopeId: string;
  readonly mapKind: 'partial-equivalence' | 'open-partial-homeomorphism';
  readonly selectedRegion?: 'source' | 'target';
  readonly application?: { readonly input: SemanticObject; readonly output: SemanticObject };
  readonly title: string;
  readonly explanation: string;
}

const kinds = ['restricted-equivalence', 'restricted-region', 'restricted-application'];
const baseRoles = ['map', 'source carrier', 'target carrier'];

function trustedHead(expression: Expr): boolean {
  let head = expression;
  const seen = new Set<Expr>();
  while (head.kind === 'app') {
    if (seen.has(head)) return false;
    seen.add(head); head = head.fn;
  }
  return head.kind !== 'const' || head.canonical !== false;
}

/** Empty is recognized from an audited constructor, never from its label. */
function isEmpty(expression: Expr): boolean {
  return expression.kind === 'app' && expression.fn.kind === 'const'
    && expression.fn.canonical === true && expression.fn.name === 'Set.empty'
    && expression.args.length === 1 && expression.argumentKinds?.length === 1
    && expression.argumentKinds[0] === 'type';
}

/** Render the audited bundled meaning. No membership, nonemptiness, or global
 * inverse is inferred from the fact that a total function can be applied. */
export function compileRestrictedMap(document: SemanticDocument, relation: SemanticRelation, relations: readonly SemanticRelation[] = document.relations): RestrictedMapModel | undefined {
  if (!kinds.includes(relation.kind) || relation.fidelity === 'structural' || !trustedHead(relation.expression)) return;
  if (!['partial-equivalence', 'open-partial-homeomorphism'].includes(relation.restrictedMapKind ?? '')
    || !['forward', 'inverse'].includes(relation.restrictedDirection ?? '')) return;
  const scope = document.scopes.find(scope => scope.id === relation.scopeId);
  if (!scope || scope.nodeId !== relation.nodeId) return;
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const boundObjects = new Map(document.objects.flatMap(object => object.binder ? [[object.binder.id, object] as const] : []));
  const available = (object: SemanticObject): boolean => {
    if (object.binder && !scope.objectIds.includes(object.id)) return false;
    // Composite projection/application expressions can reference a hidden bound
    // map even when the composite object itself has no binder metadata.
    const visit = (expression: Expr, locals: ReadonlySet<string>, depth: number): boolean => {
      if (depth > 128) return false;
      if (expression.kind === 'var') {
        const bound = boundObjects.get(expression.id);
        return locals.has(expression.id) || !bound || scope.objectIds.includes(bound.id);
      }
      if (expression.kind === 'app') return visit(expression.fn, locals, depth + 1) && expression.args.every(argument => visit(argument, locals, depth + 1));
      if (expression.kind === 'forall' || expression.kind === 'lambda') {
        return (!expression.binderType || visit(expression.binderType, locals, depth + 1)) && visit(expression.body, new Set([...locals, expression.binder.id]), depth + 1);
      }
      return true;
    };
    return visit(object.expression, new Set(), 0);
  };
  const validPorts = (candidate: SemanticRelation): boolean => new Set(candidate.ports.map(port => port.role)).size === candidate.ports.length
    && candidate.ports.every(port => { const object = objects.get(port.objectId); return object && available(object); });
  if (!validPorts(relation)) return;
  const port = (candidate: SemanticRelation, role: string): SemanticObject | undefined => {
    const matching = candidate.ports.filter(port => port.role === role);
    return matching.length === 1 ? objects.get(matching[0].objectId) : undefined;
  };
  const kind = relation.kind === 'restricted-equivalence' ? 'equivalence' : relation.kind === 'restricted-region' ? 'region' : 'application';
  const required = [...baseRoles, ...(kind === 'region' ? ['region'] : kind === 'application' ? ['input', 'output'] : [])];
  if (relation.ports.length !== required.length || required.some(role => !port(relation, role))) return;
  if (kind === 'region' && !['source', 'target'].includes(relation.restrictedRegion ?? '')) return;
  const map = port(relation, 'map')!, sourceCarrier = port(relation, 'source carrier')!, targetCarrier = port(relation, 'target carrier')!;
  const projection = (role: 'source' | 'target'): SemanticObject | undefined => {
    if (kind === 'region' && relation.restrictedRegion === role) return port(relation, 'region');
    const candidates = relations.filter(candidate => candidate.kind === 'restricted-region' && candidate.nodeId === relation.nodeId && candidate.scopeId === relation.scopeId
      && candidate.fidelity !== 'structural' && candidate.restrictedMapKind === relation.restrictedMapKind && candidate.restrictedRegion === role && trustedHead(candidate.expression)
      && candidate.ports.length === 4 && validPorts(candidate)
      && port(candidate, 'map')?.id === map.id && port(candidate, 'source carrier')?.id === sourceCarrier.id && port(candidate, 'target carrier')?.id === targetCarrier.id);
    const observed = new Map(candidates.flatMap(candidate => { const object = port(candidate, 'region'); return object ? [[object.id, object] as const] : []; }));
    // Different exported expressions can denote the same field (e.symm.source
    // and e.target); do not silently replace either expression's identity.
    return observed.size === 1 ? [...observed.values()][0] : undefined;
  };
  const region = (role: 'source' | 'target'): RestrictedRegion => {
    const object = projection(role);
    return { role, label: object?.label ?? `${map.label}.${role}`, ...(object ? { object } : {}), empty: object ? isEmpty(object.expression) : false };
  };
  const open = relation.restrictedMapKind === 'open-partial-homeomorphism';
  return {
    kind, relation, nodeId: relation.nodeId, scopeId: relation.scopeId, map,
    mapKind: relation.restrictedMapKind!, direction: relation.restrictedDirection!, sourceCarrier, targetCarrier,
    source: region('source'), target: region('target'), sameCarrier: sourceCarrier.id === targetCarrier.id,
    properties: { sourceOpen: open, targetOpen: open, forwardContinuousOnSource: open, inverseContinuousOnTarget: open },
    ...(kind === 'region' ? { selectedRegion: relation.restrictedRegion! } : {}),
    ...(kind === 'application' ? { application: { input: port(relation, 'input')!, output: port(relation, 'output')! } } : {}),
    title: kind === 'application' ? `Apply the ${relation.restrictedDirection === 'inverse' ? 'inverse' : 'forward'} map`
      : kind === 'region' ? `The ${relation.restrictedRegion} region` : open ? 'An equivalence between open regions' : 'An equivalence between specified regions',
    explanation: kind === 'application'
      ? 'This is the application appearing in the statement. Its type alone does not establish membership in the valid region; the round-trip law requires that membership.'
      : open
        ? 'The source and target are open subsets of their carrier spaces. The forward and inverse maps are continuous on their respective regions, and undo each other there.'
        : 'The forward map takes the source region to the target region. The inverse takes the target back to the source, and each undoes the other on its valid region.',
  };
}
