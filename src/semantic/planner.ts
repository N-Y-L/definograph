import { expressionVariables } from '../core/expression';
import type { StatementNode } from '../core/types';
import type { PlannedView, PlannerOptions, RepresentationCapability, SemanticDocument, ViewPlan } from './types';

/** Inspectable representation contracts, shared by ranking and future editor integrations. */
export const representationCapabilities: readonly RepresentationCapability[] = [
  { kind: 'semantic-map', fidelity: 'structural', baseScore: 60, requires: ['An elaborated statement'], preserves: ['Object identity', 'Expression relationships', 'Source provenance', 'Logical scope'], doesNotEncode: ['Uninterpreted definitions', 'A proof of the statement'] },
  { kind: 'relation-map', fidelity: 'symbolic', baseScore: 80, requires: ['At least one semantic or structural relation'], preserves: ['Relation argument roles', 'Shared objects', 'Assumptions and branches'], doesNotEncode: ['Geometric distances', 'Set cardinalities', 'Truth of displayed relations'] },
  { kind: 'quantifier-flow', fidelity: 'symbolic', baseScore: 72, requires: ['At least one scoped choice'], preserves: ['Binder order', 'Witness dependencies', 'Definition parameters'], doesNotEncode: ['All values of an infinite domain', 'Existence of a witness'] },
  { kind: 'ball', fidelity: 'numerical', baseScore: 110, requires: ['Audited metric instance', 'Supported finite dimension', 'Numeric center and radius for sampled geometry'], preserves: ['Metric shape', 'Open or closed boundary', 'Ambient dimension', 'Coordinate slice', 'All-coordinate distance profile when a point is supplied'], doesNotEncode: ['Off-slice points as projected points', 'All points of an infinite region'] },
  { kind: 'graph', fidelity: 'numerical', baseScore: 105, requires: ['Audited real function expression', 'A numerical sampling domain'], preserves: ['Function input and output correspondence'], doesNotEncode: ['Behavior between samples', 'A proof of continuity or boundedness'] },
  { kind: 'mapping', fidelity: 'symbolic', baseScore: 81, requires: ['Recognized function application or property'], preserves: ['Mapping direction', 'Named function property'], doesNotEncode: ['A numerical function', 'A finite model of an arbitrary domain'] },
  { kind: 'interval', fidelity: 'numerical', baseScore: 75, requires: ['Audited scalar relation', 'A real variable in scope'], preserves: ['Sampled scalar condition'], doesNotEncode: ['An exact solution set', 'Truth of a quantified statement'] },
];

export function selectedNodeIds(tree: StatementNode, selectedNodeId: string): Set<string> {
  const nodes = new Set<string>();
  const collect = (node: StatementNode): void => { nodes.add(node.id); node.children.forEach(collect); };
  const find = (node: StatementNode): StatementNode | undefined => node.id === selectedNodeId ? node : node.children.map(find).find(Boolean);
  const selected = find(tree);
  if (selected) collect(selected);
  return nodes;
}

/** Rank a composition of representations by semantic coverage, connections and specificity. */
export function planViews(document: SemanticDocument, options: PlannerOptions = {}): ViewPlan {
  const selectedNodeId = options.selectedNodeId ?? document.tree.id;
  const nodeIds = selectedNodeIds(document.tree, selectedNodeId);
  if (!nodeIds.size) throw new Error(`Unknown statement node: ${selectedNodeId}`);
  const fragments = document.coverage.filter(c => nodeIds.has(c.nodeId));
  const relations = document.relations.filter(r => nodeIds.has(r.nodeId));
  const selectedScopes = document.scopes.filter(s => nodeIds.has(s.nodeId));
  const objectIds = new Set([...fragments.flatMap(c => c.objectIds), ...selectedScopes.flatMap(s => s.objectIds)]);
  const visibleChoices = document.choices.filter(c => objectIds.has(c.objectId));
  const objectUse = new Map<string, Set<string>>();
  for (const relation of relations) for (const port of relation.ports) {
    const uses = objectUse.get(port.objectId) ?? new Set<string>(); uses.add(relation.nodeId); objectUse.set(port.objectId, uses);
  }
  const sharedObjectIds = [...objectUse].filter(([, uses]) => uses.size > 1).map(([id]) => id);
  const symbolic = relations.filter(r => r.fidelity !== 'structural');
  const views: PlannedView[] = [{ id: `view:semantic:${selectedNodeId}`, kind: 'semantic-map', title: 'Statement structure', score: symbolic.length ? 60 : 90, reason: 'Links typed objects and uninterpreted regions to their source fragments. Use the statement navigator to inspect each logical branch.', fidelity: 'structural', nodeIds: [...nodeIds], objectIds: [...objectIds], relationIds: relations.map(r => r.id), sceneIds: [], conditions: ['Logical structure is exact; a diagram does not establish the proposition.'] }];
  if (relations.length) views.push({ id: `view:relations:${selectedNodeId}`, kind: 'relation-map', title: 'Connected objects', score: symbolic.length ? 80 + Math.min(14, sharedObjectIds.length * 3 + symbolic.length) + (nodeIds.size === 1 ? 24 : fragments.length > 1 ? 5 : 0) : 70, reason: sharedObjectIds.length ? `${sharedObjectIds.length} shared object${sharedObjectIds.length === 1 ? '' : 's'} connect relationships across the statement.` : 'Shows which objects participate in each relationship, retaining symbolic and uninterpreted applications.', fidelity: symbolic.length ? 'symbolic' : 'structural', nodeIds: [...nodeIds], objectIds: [...objectIds], relationIds: relations.map(r => r.id), sceneIds: [], conditions: ['Spacing and shape are schematic unless a numerical metric view is shown.', ...new Set(selectedScopes.flatMap(s => s.context))] });
  if (visibleChoices.length) views.push({ id: `view:quantifiers:${selectedNodeId}`, kind: 'quantifier-flow', title: 'Choices and dependencies', score: 72 + Math.min(17, visibleChoices.length * 3) + (visibleChoices.some(c => c.role === 'existential') && visibleChoices.some(c => c.role === 'universal') ? 7 : 0), reason: 'Shows the order of arbitrary choices, candidate witnesses, and the information each choice may depend on.', fidelity: 'symbolic', nodeIds: visibleChoices.map(c => c.nodeId), objectIds: visibleChoices.map(c => c.objectId), relationIds: [], sceneIds: [], conditions: ['A witness may use earlier choices in its branch; displayed samples are not proofs.'] });
  const detailed: PlannedView[] = document.scenes.filter(scene => nodeIds.has(scene.nodeId)).map(scene => {
    const variableIds = new Set(expressionVariables(scene.expression));
    const linkedObjects = document.objects.filter(o => o.binder && variableIds.has(o.binder.id)).map(o => o.id);
    const sameNodeRelations = relations.filter(r => r.nodeId === scene.nodeId);
    const conditions = [...scene.context, ...(scene.guards.length ? ['This view is conditional on the active implication premises.'] : [])];
    if (scene.kind === 'ball' && scene.dimension > 2) conditions.push(`A ${scene.dimension}-dimensional ambient object. The distance profile uses all coordinates; points outside the adjustable coordinate slice are not projected into its plane.`);
    if (scene.kind === 'mapping') conditions.push('Symbolic mapping: no numerical function or finite cardinality is inferred.');
    else conditions.push('Numerical samples use finite precision and do not certify the statement.');
    const capability = representationCapabilities.find(capability => capability.kind === scene.kind)!;
    const score = capability.baseScore + Math.min(6, linkedObjects.filter(id => sharedObjectIds.includes(id)).length * 2) + (fragments.length === 1 ? 10 : 0);
    return { id: `view:scene:${scene.id}`, kind: scene.kind, title: scene.title, score, reason: scene.kind === 'ball' ? scene.dimension > 8 && scene.point ? 'The elaborated metric supports an all-coordinate distance profile and an adjustable coordinate slice of this region.' : `The elaborated metric supports an explicit ${scene.dimension > 2 ? 'coordinate slice' : 'geometric view'} of this region.` : scene.kind === 'mapping' ? 'A recognized mapping or function property has a direct symbolic representation.' : 'Audited operations provide a numerical illustration linked to the selected statement.', fidelity: scene.kind === 'mapping' ? 'symbolic' : 'numerical', nodeIds: [scene.nodeId], objectIds: linkedObjects, relationIds: sameNodeRelations.map(r => r.id), sceneIds: [scene.id], conditions };
  });
  detailed.sort((a, b) => b.score - a.score || a.id.localeCompare(b.id));
  const maxDetailed = options.maxDetailedViews === undefined ? 4 : Number.isFinite(options.maxDetailedViews) ? Math.max(0, Math.floor(options.maxDetailedViews)) : 4;
  views.push(...detailed.slice(0, maxDetailed));
  views.sort((a, b) => b.score - a.score || a.id.localeCompare(b.id));
  const counts = { fragments: fragments.length, interpreted: fragments.filter(c => c.status === 'interpreted').length, partial: fragments.filter(c => c.status === 'partial').length, structural: fragments.filter(c => c.status === 'structural').length };
  return { selectedNodeId, views, primaryViewId: views[0]!.id, sharedObjectIds, coverage: counts, explanation: `Selected ${views[0]!.title.toLowerCase()} for its semantic coverage and directness. ${counts.interpreted} of ${counts.fragments} predicate fragments have interpreted relations${counts.partial ? `; ${counts.partial} retain uninterpreted parts` : ''}. The statement map remains available for complete logical context.` };
}
