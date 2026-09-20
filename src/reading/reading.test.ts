import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from '../semantic';
import type { SemanticDocument } from '../semantic/types';
import { compileReading } from './index';

const constant = (name: string): Expr => ({ kind: 'const', name });
const literal = (value: number): Expr => ({ kind: 'literal', value });
const bind = (id: string, role: Binder['role'] = 'universal', name = id, dependsOn: string[] = []): Binder => ({ id, name, role, type: 'ℝ', domain: 'real', dependsOn });
const variable = (binder: Binder): Expr => ({ kind: 'var', id: binder.id, name: binder.name, type: binder.type, typeDescriptor: binder.typeDescriptor });
const app = (name: string, args: Expr[], extra: Partial<Extract<Expr, { kind: 'app' }>> = {}): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value'), ...extra });
const leaf = (id: string, expression: Expr = constant('Unknown.proposition')): StatementNode => ({ id, kind: 'predicate', label: id, lean: `${id} : Prop`, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binder?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder });
const semantic = (tree: StatementNode) => compileSemanticDocument({ source: 'test source', tree, expression: tree.expression });
const read = (tree: StatementNode, selectedNodeId?: string) => compileReading(semantic(tree), { selectedNodeId });
const sourceNodes = (tree: StatementNode): StatementNode[] => [tree, ...tree.children.flatMap(sourceNodes)];

describe('whole-statement logical reading', () => {
  it('retains every AST node in preorder and every leaf as a clause panel', () => {
    const tree = node('all', 'forall', [node('both', 'and', [node('if', 'implies', [leaf('assume'), leaf('conclude')]), node('not', 'not', [leaf('negated')])])], bind('x'));
    const doc = read(tree);
    expect(doc.nodes.map(node => node.id)).toEqual(sourceNodes(tree).map(node => node.id));
    expect(doc.nodes.map(node => node.kind)).toEqual(sourceNodes(tree).map(node => node.kind));
    expect(doc.panels.map(panel => panel.nodeId)).toEqual(['assume', 'conclude', 'negated']);
    expect(doc.panels.every(panel => panel.coverage === 'structural')).toBe(true);
    expect(doc.nodes.filter(node => !node.children.length).every(node => node.panelId)).toBe(true);
  });

  it('retains unknown clauses and their exact Lean content with no semantic relations', () => {
    const unknown = leaf('opaque', { kind: 'opaque', text: 'opaque expression' });
    unknown.lean = 'A completely uninterpreted condition';
    const doc = read(unknown);
    expect(doc.root.phrase).toBe(unknown.lean);
    expect(doc.panels).toHaveLength(1);
    expect(doc.panels[0]!.relationIds).toEqual([]);
    expect(doc.panels[0]!.opaqueRegionIds).toHaveLength(1);
  });

  it('makes implication direction explicit without asserting its premise', () => {
    const doc = read(node('root', 'implies', [leaf('p'), leaf('q')], bind('h', 'assumption')));
    expect(doc.root.children[0]!.edgeFromParent).toEqual({ role: 'assumption', label: 'If', index: 0 });
    expect(doc.root.children[1]!.edgeFromParent).toEqual({ role: 'conclusion', label: 'Then', index: 1 });
    expect(doc.root.children[0]!.assumptionNodeIds).toEqual([]);
    expect(doc.root.children[1]!.assumptionNodeIds).toEqual(['p']);
    expect(doc.root.phrase).toContain('If');
  });

  it('represents iff as two oppositely directed implications', () => {
    const doc = read(node('root', 'iff', [leaf('a'), leaf('b')]));
    expect(doc.root.directions?.map(direction => [direction.assumptionNodeId, direction.conclusionNodeId])).toEqual([['a', 'b'], ['b', 'a']]);
    expect(doc.root.children.map(child => child.edgeFromParent?.role)).toEqual(['equivalence-left', 'equivalence-right']);
    expect(doc.root.phrase).toBe('Each condition implies the other');
  });

  it('distinguishes conjunction from alternatives even when their leaves are identical', () => {
    const and = read(node('root', 'and', [leaf('a'), leaf('b')]));
    const or = read(node('root', 'or', [leaf('a'), leaf('b')]));
    expect(and.root.children.map(child => child.edgeFromParent?.role)).toEqual(['conjunct', 'conjunct']);
    expect(or.root.children.map(child => child.edgeFromParent?.role)).toEqual(['alternative', 'alternative']);
    expect(and.root.phrase).not.toBe(or.root.phrase);
    expect(or.root.phrase).toContain('At least one');
  });

  it('keeps negation wrapped around quantified statements and geometry', () => {
    const ball = app('Metric.ball', [literal(0), literal(1)], { metric: 'real', dimension: 1 });
    const doc = read(node('not', 'not', [node('exists', 'exists', [leaf('p', app('Set.Mem', [ball, variable(bind('x'))]))], bind('x', 'existential'))]));
    expect(doc.root.kind).toBe('not');
    expect(doc.root.children[0]!.edgeFromParent?.role).toBe('negated');
    expect(doc.quantifierGroups[0]!.branchPath).toEqual([{ nodeId: 'not', edge: { role: 'negated', label: 'Not', index: 0 } }]);
    expect(doc.panels[0]!.sceneIds).toHaveLength(1);
    expect(doc.nodes.find(node => node.id === 'p')!.context).toContain('Inside a negation');
  });
});

describe('quantifier order and lexical placement', () => {
  it('preserves forall-exists versus exists-forall as different readings', () => {
    const forward = read(node('first', 'forall', [node('second', 'exists', [leaf('p')], bind('y', 'existential', 'y', ['x']))], bind('x')));
    const reverse = read(node('first', 'exists', [node('second', 'forall', [leaf('p')], bind('x'))], bind('y', 'existential')));
    expect(forward.quantifierGroups.map(group => group.kind)).toEqual(['forall', 'exists']);
    expect(reverse.quantifierGroups.map(group => group.kind)).toEqual(['exists', 'forall']);
    expect(forward.quantifierGroups[1]!.binders[0]!.dependsOn).toEqual([forward.quantifierGroups[0]!.binders[0]!.objectId]);
    expect(reverse.quantifierGroups[0]!.binders[0]!.dependsOn).toEqual([]);
  });

  it('groups only contiguous binders of the same role', () => {
    const doc = read(node('x', 'forall', [node('y', 'forall', [node('z', 'exists', [node('w', 'forall', [leaf('p')], bind('w'))], bind('z', 'existential'))], bind('y'))], bind('x')));
    expect(doc.quantifierGroups.map(group => group.nodeIds)).toEqual([['x', 'y'], ['z'], ['w']]);
    expect(doc.quantifierGroups.map(group => group.bodyNodeId)).toEqual(['z', 'w', 'p']);
    expect(doc.nodes.filter(node => node.kind === 'forall')).toHaveLength(3);
  });

  it('never groups binders from separate logical branches', () => {
    const doc = read(node('or', 'or', [node('left', 'forall', [leaf('p')], bind('x')), node('right', 'forall', [leaf('q')], bind('y'))]));
    expect(doc.quantifierGroups.map(group => group.nodeIds)).toEqual([['left'], ['right']]);
    expect(doc.quantifierGroups.map(group => group.branchPath[0]!.edge.index)).toEqual([0, 1]);
    expect(doc.quantifierGroups.every(group => group.branchPath[0]!.edge.role === 'alternative')).toBe(true);
  });

  it('never moves a quantifier across an implication assumption', () => {
    const doc = read(node('x', 'forall', [node('imp', 'implies', [leaf('p'), node('y', 'forall', [leaf('q')], bind('y'))])], bind('x')));
    expect(doc.quantifierGroups.map(group => group.nodeIds)).toEqual([['x'], ['y']]);
    expect(doc.quantifierGroups[1]!.branchPath.map(position => position.edge.role)).toEqual(['body', 'conclusion']);
    expect(doc.nodes.find(node => node.id === 'y')!.assumptionNodeIds).toEqual(['p']);
  });

  it('distinguishes function parameters from propositional forall binders', () => {
    const doc = read(node('parameter', 'parameter', [node('all', 'forall', [leaf('p')], bind('x'))], bind('f', 'parameter')));
    expect(doc.quantifierGroups.map(group => group.kind)).toEqual(['parameter', 'forall']);
    expect(doc.root.binder!.role).toBe('parameter');
    expect(doc.root.children[0]!.edgeFromParent?.role).toBe('result');
    expect(doc.root.phrase).toContain('With parameter');
    expect(doc.root.children[0]!.phrase).toContain('For every');
  });

  it('does not let binder names determine grouping, order, or dependencies', () => {
    const build = (names: [string, string]) => {
      const x = bind('x', 'universal', names[0]);
      const y = bind('y', 'existential', names[1], ['x']);
      return read(node('xnode', 'forall', [node('ynode', 'exists', [leaf('eq', app('Eq', [variable(x), variable(y)]))], y)], x));
    };
    const original = build(['x', 'y']), renamed = build(['A', 'radius']);
    expect(original.nodes.map(node => [node.id, node.kind, node.edgeFromParent])).toEqual(renamed.nodes.map(node => [node.id, node.kind, node.edgeFromParent]));
    expect(original.quantifierGroups.map(group => [group.kind, group.binders.map(binder => [binder.objectId, binder.dependsOn])])).toEqual(renamed.quantifierGroups.map(group => [group.kind, group.binders.map(binder => [binder.objectId, binder.dependsOn])]));
    expect(original.root.phrase).not.toBe(renamed.root.phrase);
  });
});

describe('composition within atomic clauses', () => {
  it('connects the image of a set to a containing membership relation in one panel', () => {
    const image = app('Set.image', [constant('f'), constant('S')]);
    const source = leaf('member', app('Set.Mem', [image, constant('y')]));
    const document = semantic(source), reading = compileReading(document);
    const panel = reading.panels[0]!;
    const imageRelation = document.relations.find(relation => relation.kind === 'image')!;
    const membership = document.relations.find(relation => relation.kind === 'membership')!;
    expect(panel.rootRelationIds).toEqual([membership.id]);
    expect(panel.groups).toHaveLength(1);
    expect(panel.groups[0]!.connections).toContainEqual({ objectId: imageRelation.ports.find(port => port.role === 'result')!.objectId, fromRelationId: imageRelation.id, toRelationId: membership.id, kind: 'feeds' });
    expect(panel.phrase).toContain('belongs to');
  });

  it('keeps premise and conclusion relations in distinct panels even when they share objects', () => {
    const x = bind('x');
    const left = leaf('left', app('Eq', [variable(x), literal(1)]));
    const right = leaf('right', app('Eq', [variable(x), literal(2)]));
    const doc = read(node('forall', 'forall', [node('imp', 'implies', [left, right])], x));
    expect(doc.panels.map(panel => panel.nodeId)).toEqual(['left', 'right']);
    expect(doc.panels.every(panel => panel.relationIds.length === 1 && panel.groups[0]!.connections.length === 0)).toBe(true);
  });

  it('keeps lambda body relations in a separate expression scope', () => {
    const x = bind('x', 'lambda');
    const lambda: Expr = { kind: 'lambda', binder: x, body: app('Eq', [variable(x), literal(0)]) };
    const doc = read(leaf('predicate', app('Unknown.P', [lambda])));
    expect(doc.panels).toHaveLength(1);
    expect(doc.panels[0]!.groups.map(group => group.role)).toEqual(['clause', 'local-expression']);
    expect(doc.panels[0]!.groups.every(group => group.connections.every(connection => group.relationIds.includes(connection.fromRelationId) && group.relationIds.includes(connection.toRelationId)))).toBe(true);
    expect(doc.panels[0]!.groups[1]!.context).toContain('Within a function body');
  });

  it('keeps an uninterpreted parent above a recognized metric construction', () => {
    const ball = app('Metric.ball', [literal(0), literal(1)], { metric: 'real', dimension: 1 });
    const document = semantic(leaf('unknown', app('Unknown.P', [ball])));
    const doc = compileReading(document);
    expect(doc.panels[0]!.coverage).toBe('partial');
    const root = document.relations.find(relation => doc.panels[0]!.rootRelationIds.includes(relation.id))!;
    expect(root.fidelity).toBe('structural');
    expect(doc.root.phrase).toBe(document.tree.lean);
    expect(doc.panels[0]!.relationIds).toHaveLength(2);
  });

  it('does not omit a clause just because its semantic coverage record is missing', () => {
    const document = semantic(node('both', 'and', [leaf('a'), leaf('b')]));
    const incomplete: SemanticDocument = { ...document, coverage: document.coverage.slice(0, 1) };
    const reading = compileReading(incomplete);
    expect(reading.panels.map(panel => panel.nodeId)).toEqual(['a', 'b']);
    expect(reading.panels[1]!.coverage).toBe('structural');
  });
});

describe('selection and complete context', () => {
  it('offers a complete ordered sequence with an explicit logical envelope on every step', () => {
    const doc = read(node('not', 'not', [node('exists', 'exists', [node('or', 'or', [leaf('left'), leaf('right')])], bind('x', 'existential'))]));
    expect(doc.sequence.map(step => [step.nodeId, step.kind, step.ordinal])).toEqual([
      ['not', 'connective', 1], ['exists', 'binder', 2], ['or', 'connective', 3], ['left', 'clause', 4], ['right', 'clause', 5],
    ]);
    const left = doc.sequence[3]!, right = doc.sequence[4]!;
    expect(left.ancestorNodeIds).toEqual(['not', 'exists', 'or']);
    expect(left.branchPath.map(position => position.edge.role)).toEqual(['negated', 'body', 'alternative']);
    expect(right.branchPath.at(-1)!.edge.index).toBe(1);
    expect(left.branchPath.at(-1)!.edge.index).toBe(0);
    expect(doc.sequence.every(step => doc.nodes.some(node => node.id === step.nodeId))).toBe(true);
  });

  it('keeps the whole statement while marking the focused clause and its inherited scope', () => {
    const x = bind('x'), h = bind('h', 'assumption');
    const tree = node('all', 'forall', [node('both', 'and', [node('imp', 'implies', [leaf('premise'), leaf('conclusion')], h), leaf('sibling')])], x);
    const whole = read(tree), selected = read(tree, 'conclusion');
    expect(selected.root).toEqual(whole.root);
    expect(selected.nodes).toEqual(whole.nodes);
    expect(selected.panels).toEqual(whole.panels);
    expect(selected.selection.ancestorNodeIds).toEqual(['all', 'both', 'imp']);
    expect(selected.selection.descendantNodeIds).toEqual(['conclusion']);
    expect(selected.selection.assumptionNodeIds).toEqual(['premise']);
    expect(selected.selection.panelIds).toEqual(['reading-panel:conclusion']);
    expect(selected.selection.scopeObjectIds).toHaveLength(2);
    expect(read(tree, 'sibling').selection.assumptionNodeIds).toEqual([]);
  });

  it('selects an entire logical branch without merging sibling panels', () => {
    const doc = read(node('or', 'or', [node('left', 'and', [leaf('a'), leaf('b')]), leaf('c')]), 'left');
    expect(doc.selection.descendantNodeIds).toEqual(['left', 'a', 'b']);
    expect(doc.selection.panelIds).toEqual(['reading-panel:a', 'reading-panel:b']);
    expect(doc.panels).toHaveLength(3);
  });

  it('retains leaf identity and coverage across equivalent conjunction association', () => {
    const a = leaf('a'), b = leaf('b'), c = leaf('c');
    const left = read(node('root', 'and', [node('ab', 'and', [a, b]), c]));
    const right = read(node('root', 'and', [a, node('bc', 'and', [b, c])]));
    expect(left.panels).toEqual(right.panels);
    expect(left.nodes.map(node => node.id)).not.toEqual(right.nodes.map(node => node.id));
  });

  it('rejects unknown selection and duplicate source IDs instead of inventing correspondence', () => {
    expect(() => read(leaf('root'), 'missing')).toThrow('Unknown reading selection');
    const document = semantic(leaf('root'));
    expect(() => compileReading({ ...document, tree: node('root', 'and', [leaf('duplicate'), leaf('duplicate')]) })).toThrow('Duplicate statement node id');
  });
});
