import type { SemanticDocument, SemanticRelation, SemanticScope } from '../semantic/types';
import { planReadingPresentation, type ReadingRegion } from './presentation';
import type { ReadingBinder, ReadingDocument, ReadingNode, ReadingPanel, ReadingQuantifierGroup } from './types';

export const READING_CUE_VERSION = '1.0.0' as const;
export type ReadingCueIntent = 'introduce' | 'logic' | 'apply' | 'compare' | 'condition';
export type ReadingCueRole = 'statement' | 'parameter' | 'arbitrary' | 'witness' | 'assumption' | 'conclusion' | 'conjunct' | 'alternative' | 'equivalence-left' | 'equivalence-right' | 'negated' | 'result' | 'contained';
export interface ReadingCue {
  readonly id: string;
  readonly ordinal: number;
  readonly intent: ReadingCueIntent;
  /** The immediate role; branchPath and roles retain every enclosing logical position. */
  readonly role: ReadingCueRole;
  readonly roles: readonly ReadingCueRole[];
  readonly nodeId: string;
  readonly regionId: string;
  readonly sourceNodeIds: readonly string[];
  readonly panelId?: string;
  readonly scopeId: string;
  /** Includes nested lambda/forall expression scopes absent from the statement AST. */
  readonly scopePath: readonly string[];
  readonly ancestorNodeIds: readonly string[];
  readonly assumptionNodeIds: readonly string[];
  readonly branchPath: ReadingQuantifierGroup['branchPath'];
  readonly contextLabels: readonly string[];
  readonly title: string;
  readonly detail: string;
  readonly focusObjectIds: readonly string[];
  readonly focusRelationIds: readonly string[];
  readonly contextObjectIds: readonly string[];
  /** Previously displayed identities still available in this cue's exact scope/group. */
  readonly retainedObjectIds: readonly string[];
  readonly binders: readonly ReadingBinder[];
  readonly stage: {
    readonly kind: 'introduction' | 'logic' | 'construction' | 'clause' | 'contained';
    readonly index: number;
    readonly count: number;
    readonly relationId?: string;
    readonly relationKind?: SemanticRelation['kind'];
  };
}
export interface ReadingCuePlan {
  readonly schemaVersion: typeof READING_CUE_VERSION;
  readonly cues: readonly ReadingCue[];
  readonly totalCueCount: number;
  readonly truncated: boolean;
  readonly omittedCueCount: number;
  /** Includes clauses whose internal stages were only partly emitted. */
  readonly omittedNodeIds: readonly string[];
  readonly diagnostics: readonly string[];
}
export interface ReadingCueOptions { readonly maxCues?: number }

const unique = <T>(items: readonly T[]): T[] => [...new Set(items)];
const producedRoles = new Set(['output', 'result', 'region', 'distance', 'color', 'target vertex']);
const short = (text: string, limit = 100): string => text.length > limit ? `${text.slice(0, limit - 1)}…` : text;
const edgeRoles = new Set<ReadingCueRole>(['assumption', 'conclusion', 'conjunct', 'alternative', 'equivalence-left', 'equivalence-right', 'negated', 'result']);
type Draft = Omit<ReadingCue, 'ordinal' | 'retainedObjectIds'>;

function roleOfBinder(binder: ReadingBinder): ReadingCueRole {
  return binder.role === 'existential' ? 'witness' : binder.role === 'universal' ? 'arbitrary'
    : binder.role === 'assumption' ? 'assumption' : 'parameter';
}
function surroundingRoles(path: ReadingQuantifierGroup['branchPath']): ReadingCueRole[] {
  return path.flatMap(position => edgeRoles.has(position.edge.role as ReadingCueRole) ? [position.edge.role as ReadingCueRole] : []);
}
function contextLabels(node: ReadingNode, scope: SemanticScope, path: ReadingQuantifierGroup['branchPath']): string[] {
  const positions = path.flatMap(({ edge }) => {
    switch (edge.role) {
      case 'assumption': return ['Given assumption'];
      case 'conclusion': return ['Conditional conclusion'];
      case 'conjunct': return [`Required condition ${edge.index + 1}`];
      case 'alternative': return [`Alternative ${edge.index + 1}; at least one may hold`];
      case 'equivalence-left': return ['First equivalent condition'];
      case 'equivalence-right': return ['Second equivalent condition'];
      case 'negated': return ['Under negation'];
      default: return [];
    }
  });
  return unique([...positions, ...node.context, ...scope.context]);
}
function logicText(kind: ReadingNode['kind']): [string, string] {
  switch (kind) {
    case 'implies': return ['Given → then', 'Read the assumptions before their conditional conclusion. The assumptions are not asserted globally.'];
    case 'and': return ['Read the conditions together', 'Every enclosed condition is part of this conjunction.'];
    case 'or': return ['Read the alternatives', 'At least one alternative must hold; reading both branches does not require both to hold.'];
    case 'iff': return ['Read both directions', 'Each condition implies the other. Neither side is taken as a global assumption.'];
    case 'not': return ['Read the negation', 'Negation applies to the entire enclosed condition.'];
    default: return ['Read this logical region', 'Keep the enclosing structure attached to its clauses.'];
  }
}

/** Pure attention planning. A cue neither evaluates an expression nor establishes a fact.
 * The output is a prefix of the complete source-ordered plan, never a reordered selection.
 * Selection is deliberately ignored; the UI can locate a cue by its source identities. */
export function compileReadingCues(reading: ReadingDocument, document: SemanticDocument, options: ReadingCueOptions = {}): ReadingCuePlan {
  const requested = options.maxCues ?? 250;
  if (!Number.isInteger(requested) || requested < 0) throw new Error('maxCues must be a nonnegative integer.');
  const maxCues = Math.min(requested, 1000);
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const relations = new Map(document.relations.map(relation => [relation.id, relation]));
  const scopes = new Map(document.scopes.map(scope => [scope.id, scope]));
  const panels = new Map(reading.panels.map(panel => [panel.id, panel]));
  const nodes = new Map(reading.nodes.map(node => [node.id, node]));
  const steps = new Map(reading.sequence.map(step => [step.nodeId, step]));
  const presentation = planReadingPresentation(reading);
  const cues: ReadingCue[] = [];
  const omittedNodeIds = new Set<string>();
  const diagnostics = unique([...document.diagnostics, ...reading.diagnostics]);
  if (requested > maxCues) diagnostics.push('The cue limit was capped at 1000; the complete statement remains in the atlas.');
  let totalCueCount = 0;
  let previous: ReadingCue | undefined;

  const scopePath = (scope: SemanticScope): string[] => {
    const path: string[] = [], seen = new Set<string>();
    let current: SemanticScope | undefined = scope;
    while (current && !seen.has(current.id)) { path.unshift(current.id); seen.add(current.id); current = current.parentId ? scopes.get(current.parentId) : undefined; }
    return path;
  };
  const common = (node: ReadingNode, regionId: string, sourceNodeIds: readonly string[], scopeId = node.scopeId, panel?: ReadingPanel) => {
    const step = steps.get(node.id);
    if (!step) throw new Error(`Missing reading step for ${node.id}.`);
    let scope = scopes.get(scopeId);
    if (scope && scope.nodeId !== node.id || !scope && scopeId !== node.scopeId) throw new Error(`Cue scope ${scopeId} does not belong to source node ${node.id}.`);
    if (!scope) {
      const message = 'Some semantic scopes were not exported; their cues retain source logic without inferred relations.';
      if (!diagnostics.includes(message)) diagnostics.push(message);
      // The reading tree survives the semantic traversal budget. Its source-derived
      // edges still establish the enclosing logic, but add no fabricated objects.
      const assumptions = step.branchPath.filter(part => part.edge.role === 'conclusion')
        .flatMap(part => nodes.get(part.nodeId)?.children[0]?.id ?? []);
      scope = { id: node.scopeId, nodeId: node.id, parentId: node.parentId ? nodes.get(node.parentId)?.scopeId : undefined,
        kind: node.kind, label: node.phrase, objectIds: [], assumptionNodeIds: assumptions, context: node.context };
    }
    const roles = surroundingRoles(step.branchPath);
    return { nodeId: node.id, regionId, sourceNodeIds, panelId: panel?.id, scopeId,
      scopePath: scopePath(scope), ancestorNodeIds: step.ancestorNodeIds, assumptionNodeIds: scope.assumptionNodeIds,
      branchPath: step.branchPath, contextLabels: contextLabels(node, scope, step.branchPath),
      role: roles.at(-1) ?? 'statement', roles, contextObjectIds: scope.objectIds.filter(id => objects.has(id)), binders: [] as readonly ReadingBinder[] };
  };
  const emit = (draft: Draft, groupObjects: readonly string[] = []): void => {
    totalCueCount += 1;
    if (cues.length >= maxCues) { draft.sourceNodeIds.forEach(id => omittedNodeIds.add(id)); return; }
    for (const id of draft.focusObjectIds) if (!objects.has(id)) throw new Error(`Unknown cue object ${id}.`);
    for (const id of draft.focusRelationIds) {
      const relation = relations.get(id);
      const introducedType = draft.stage.kind === 'introduction' && relation?.provenance.expressionPath === 'binder.type' && draft.sourceNodeIds.includes(relation.nodeId) && relation.scopeId === `scope:${relation.nodeId}`;
      if (!relation || !introducedType && (relation.nodeId !== draft.nodeId || relation.scopeId !== draft.scopeId)) throw new Error(`Cue relation ${id} crosses its declared source scope.`);
    }
    const available = new Set([...draft.contextObjectIds, ...draft.focusObjectIds, ...groupObjects]);
    const retainedObjectIds = previous ? unique([...previous.retainedObjectIds, ...previous.focusObjectIds]).filter(id => available.has(id)) : [];
    const cue: ReadingCue = { ...draft, ordinal: cues.length + 1, retainedObjectIds };
    cues.push(cue); previous = cue;
  };
  const label = (id: string | undefined): string => id ? objects.get(id)?.label ?? 'expression' : 'expression';
  const port = (relation: SemanticRelation, role: string) => relation.ports.find(port => port.role === role)?.objectId;
  const relationText = (relation: SemanticRelation): [ReadingCueIntent, string, string] => {
    switch (relation.kind) {
      case 'application': return ['apply', `Follow ${short(label(port(relation, 'function')), 60)}`, `Follow the ordered inputs of ${short(label(port(relation, 'function')), 50)} to the expression ${short(label(port(relation, 'output')), 90)}.`];
      case 'image': return ['apply', 'Form the image', `Read the image of ${short(label(port(relation, 'set')), 60)} under ${short(label(port(relation, 'function')), 60)}.`];
      case 'preimage': return ['apply', 'Form the preimage', `Read the inputs whose images lie in ${short(label(port(relation, 'set')), 80)}.`];
      case 'set-construction': {
        const first = short(label(port(relation, 'operand 1')), 50), second = short(label(port(relation, 'operand 2')), 50);
        const description = relation.setOperation === 'union' ? `Elements in ${first} or ${second}`
          : relation.setOperation === 'intersection' ? `Elements in both ${first} and ${second}`
            : relation.setOperation === 'difference' ? `Elements in ${first} and outside ${second}`
              : relation.setOperation === 'complement' ? `Elements of the carrier outside ${first}` : 'Combine the operands using the stated set operation';
        return ['apply', `Form the ${relation.setOperation ?? relation.label}`, `${description}. No membership region is assumed nonempty.`];
      }
      case 'metric-region': return ['apply', `Construct the ${relation.label}`, 'Use the specified center, radius, and metric to read this region; no numerical values are chosen.'];
      case 'distance': return ['apply', 'Read the distance', 'Follow the distance expression between these two objects in the specified metric.'];
      case 'equality': case 'inequality': return ['compare', `Compare the expressions with ${relation.label}`, `Read the ${relation.label} relation between the two expressions within this logical context.`];
      case 'membership': return ['condition', 'Read the membership condition', `The condition places ${short(label(port(relation, 'element')), 60)} in ${short(label(port(relation, 'set')), 90)} within this logical context.`];
      case 'subset': return ['condition', 'Read the inclusion condition', `The condition requires every element of ${short(label(port(relation, 'subset')), 60)} to belong to ${short(label(port(relation, 'superset')), 70)} within this logical context.`];
      case 'function-property': return ['condition', `Read the ${relation.label} condition`, `Read the stated property of ${short(label(port(relation, 'function')), 90)} within this logical context; it has not been proved.`];
      case 'graph-adjacency': return ['condition', 'Read the edge condition', `Read adjacency between ${short(label(port(relation, 'left vertex')), 40)} and ${short(label(port(relation, 'right vertex')), 40)} in ${short(label(port(relation, 'graph')), 50)} within this logical context.`];
      case 'graph-colorable': return ['condition', 'Read the coloring requirement', `A coloring of ${short(label(port(relation, 'graph')), 60)} using at most the stated bound is required; adjacent vertices must receive different colors.`];
      case 'graph-coloring': return ['apply', 'Follow the coloring', 'Read the color assignment and the different-color constraint on every edge. No concrete coloring is chosen.'];
      case 'graph-map': return ['apply', 'Follow the graph map', 'Read how this map transports vertices and the adjacency constraints supplied by its exact type.'];
      default: return ['condition', `Read ${short(relation.label, 85)}`, 'Read this relation at its place in the statement; its truth has not been established.'];
    }
  };

  const visitClause = (region: Extract<ReadingRegion, { kind: 'clause' }>): void => {
    const node = region.node;
    const panel = node.panelId ? panels.get(node.panelId) : undefined;
    const drafts: { draft: Draft; groupObjects: readonly string[] }[] = [];
    const seen = new Set<string>();
    const rootIds = new Set(panel?.rootRelationIds ?? []);
    const clauseRoots = [...rootIds].flatMap(id => relations.has(id) ? [relations.get(id)!] : []);
    const wrapped = clauseRoots.some(relation => relation.kind === 'predicate' || relation.fidelity === 'structural');
    const base = common(node, region.id, region.sourceNodeIds, node.scopeId, panel);
    const queueClause = () => drafts.push({ draft: { ...base, id: `cue:${node.id}:clause`, intent: 'condition', title: 'Read the complete clause', detail: short(node.phrase || node.lean, 220), focusObjectIds: unique(clauseRoots.flatMap(r => r.ports.map(p => p.objectId))), focusRelationIds: clauseRoots.map(r => r.id), stage: { kind: 'clause', index: 1, count: 1 } }, groupObjects: panel?.groups.find(group => group.role === 'clause')?.objectIds ?? [] });
    // A wrapper's condition is introduced before inspecting its contents. Children must
    // never stand in for the unknown or higher-order proposition around them.
    if (wrapped || !clauseRoots.length) { queueClause(); clauseRoots.forEach(root => seen.add(root.id)); }

    for (const group of panel?.groups ?? []) {
      const groupRelations = group.relationIds.flatMap(id => relations.has(id) ? [relations.get(id)!] : []);
      const producers = new Map<string, SemanticRelation>();
      for (const relation of groupRelations) for (const p of relation.ports) if (producedRoles.has(p.role) && !producers.has(p.objectId)) producers.set(p.objectId, relation);
      const active = new Set<string>();
      const stageRelation = (relation: SemanticRelation, contained: boolean): void => {
        if (seen.has(relation.id)) return;
        if (active.has(relation.id)) {
          const message = `Cyclic construction dependencies in ${node.id} were retained symbolically.`;
          if (!diagnostics.includes(message)) diagnostics.push(message);
          return;
        }
        active.add(relation.id);
        for (const p of relation.ports) {
          if (producedRoles.has(p.role)) continue;
          const producer = producers.get(p.objectId);
          if (producer && producer.id !== relation.id) stageRelation(producer, contained);
        }
        active.delete(relation.id);
        if (seen.has(relation.id)) return;
        seen.add(relation.id);
        const [intent, title, detail] = relationText(relation);
        const relationBase = common(node, region.id, region.sourceNodeIds, group.scopeId, panel);
        const isContained = contained || group.role === 'local-expression';
        drafts.push({ draft: { ...relationBase, id: `cue:${node.id}:relation:${relation.id}`, intent,
          role: isContained ? 'contained' : relationBase.role, roles: isContained ? [...relationBase.roles, 'contained'] : relationBase.roles,
          title: isContained ? `Inside the expression: ${title.toLowerCase()}` : title,
          detail: isContained ? `A contained expression part, not a separate assertion. ${detail}` : detail,
          focusObjectIds: unique(relation.ports.map(p => p.objectId)), focusRelationIds: [relation.id],
          stage: { kind: isContained ? 'contained' : rootIds.has(relation.id) ? 'clause' : 'construction', index: 1, count: 1, relationId: relation.id, relationKind: relation.kind } }, groupObjects: group.objectIds });
      };
      if (!wrapped && group.role === 'clause') for (const id of group.rootRelationIds) {
        const relation = relations.get(id); if (relation) stageRelation(relation, false);
      }
      // Remaining relations are expression parts, including every local binder scope.
      for (const relation of groupRelations) stageRelation(relation, true);
    }
    if (!drafts.length) queueClause();
    drafts.forEach(({ draft, groupObjects }, index) => emit({ ...draft, stage: { ...draft.stage, index: index + 1, count: drafts.length } }, groupObjects));
  };

  const visit = (region: ReadingRegion): void => {
    if (region.kind === 'clause') { visitClause(region); return; }
    if (region.kind === 'binders') {
      const node = region.binders.at(-1)!;
      const binders = region.binders.map(node => node.binder!);
      const role = roleOfBinder(binders[0]!);
      const base = common(node, region.id, region.sourceNodeIds);
      const names = short(binders.map(binder => binder.name).join(', '), 90);
      const title = role === 'arbitrary' ? `For every ${names}` : role === 'witness' ? `${binders.length === 1 ? 'There exists' : 'There exist'} ${names}` : `Parameters: ${names}`;
      const dependencies = unique(binders.flatMap(binder => binder.dependsOn)).map(id => label(id));
      const detail = role === 'witness' ? binders.length > 1 ? 'Read these witnesses in binder order; each may use only its listed earlier choices. Their existence is part of the enclosed condition.'
        : dependencies.length ? `This witness may depend on ${short(dependencies.join(', '), 120)}. Its existence is part of the enclosed condition.` : 'This witness is introduced before later choices. Its existence is part of the enclosed condition.'
        : role === 'arbitrary' ? 'Read these objects as arbitrary choices of their stated types, in the displayed binder order.' : 'These are typed parameters of this context; they do not assert a universally quantified proposition.';
      emit({ ...base, id: `cue:${region.id}:introduce`, intent: 'introduce', role, roles: [...base.roles, role], title, detail, binders,
        focusObjectIds: binders.flatMap(binder => binder.objectId ? [binder.objectId] : []), focusRelationIds: document.relations.filter(relation => region.sourceNodeIds.includes(relation.nodeId) && relation.provenance.expressionPath === 'binder.type').map(relation => relation.id), stage: { kind: 'introduction', index: 1, count: 1 } });
      if (region.body) visit(region.body);
      return;
    }
    const [title, detail] = logicText(region.node.kind);
    emit({ ...common(region.node, region.id, region.sourceNodeIds), id: `cue:${region.id}:logic`, intent: 'logic', title, detail, focusObjectIds: [], focusRelationIds: [], stage: { kind: 'logic', index: 1, count: 1 } });
    if (region.kind === 'implication') { region.assumptions.forEach(visit); visit(region.conclusion); }
    else if (region.kind === 'negation') visit(region.body);
    else region.children.forEach(visit);
  };
  visit(presentation.root);
  const omittedCueCount = totalCueCount - cues.length;
  if (omittedCueCount) diagnostics.push(`${omittedCueCount} reading cues exceed the display limit; the complete statement remains in the atlas.`);
  return { schemaVersion: READING_CUE_VERSION, cues, totalCueCount, truncated: omittedCueCount > 0, omittedCueCount, omittedNodeIds: [...omittedNodeIds], diagnostics };
}
