import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { compileReading } from './compiler';
import { compileScopedStatementGraph } from './scoped-graph';
import { ScopedStatementGraph } from '../visual/ScopedStatementGraph';
import { call, constant, fixture, frame, leaf, scopedFixture, variable } from './scoped-graph.test-fixtures';

const html = (value: ReturnType<typeof scopedFixture>) => renderToStaticMarkup(createElement(ScopedStatementGraph, { ...value, focusedNodeId: value.model.clauses.at(-1)!.node.id }));

describe('source-scoped operation composition', () => {
  it('joins the supplied ball and application outputs through the exact subset ports', () => {
    const value = scopedFixture(), graph = value.model.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    const ball = graph.nodes.find(node => node.relation?.kind === 'metric-region')!.relation!;
    const application = graph.nodes.find(node => node.relation?.kind === 'application')!.relation!;
    const subset = graph.nodes.find(node => node.relation?.kind === 'subset')!.relation!;
    const port = (relation: typeof ball, role: string) => relation.ports.find(port => port.role === role)!.objectId;
    expect(port(ball, 'region')).toBe(port(subset, 'subset'));
    expect(port(application, 'output')).toBe(port(subset, 'superset'));
    expect(graph.edges.filter(edge => edge.kind === 'result').map(edge => edge.objectId)).toEqual([port(ball, 'region'), port(application, 'output')]);
    expect(graph.edges.find(edge => edge.relationId === ball.id && edge.role === 'center')!.objectId).toBe(value.document.objects.find(object => object.expression.kind === 'var' && object.expression.id === 'point')!.id);
    expect(graph.edges.find(edge => edge.relationId === ball.id && edge.role === 'radius')!.objectId).toBe(value.document.objects.find(object => object.expression.kind === 'var' && object.expression.id === 'radius')!.id);
    expect(graph.edges.some(edge => edge.from === 'object:object:point' && edge.to === 'object:object:index')).toBe(false);
    expect(graph.nodes.filter(node => node.kind === 'object')).toHaveLength(6);
  });

  it('keeps positivity outside the universal frame and membership before the conditional existential', () => {
    const rendered = html(scopedFixture());
    const order = ['data-frame-node="exists-radius"', 'data-clause-node="positive"', 'data-frame-node="forall-point"', 'data-clause-node="membership"', 'data-frame-node="exists-index"', 'data-clause-node="inclusion"'];
    expect(order.map(text => rendered.indexOf(text))).toEqual([...order.map(text => rendered.indexOf(text))].sort((a, b) => a - b));
    expect(rendered).toContain('THEN · conditional conclusion');
    expect(rendered).toContain('Required together · condition 1');
    expect(rendered).toContain('data-binder-id="radius"');
    expect(rendered).toContain('data-binder-id="point"');
    expect(rendered).toContain('Exact source and supplied relations');
  });

  it('preserves graph topology under unfamiliar labels and exposes changed guards, ports and quantifier order', () => {
    const first = scopedFixture(), renamed = scopedFixture({ radius: 'uniformAllowance', point: 'candidatePoint', index: 'labelChoice', family: 'localDomains', set: 'admissibleInputs' });
    const signature = (value: typeof first) => value.model.clauses.map(clause => clause.graphs.map(graph => graph.edges.map(edge => [edge.role, edge.kind])));
    expect(signature(renamed)).toEqual(signature(first));
    const without = fixture({ ...first.nodes.tree, children: [frame('changed', 'forall', [frame('exists-radius', 'exists', [first.nodes.inclusion], first.binders.radius)], first.binders.point)] });
    const withoutHtml = renderToStaticMarkup(createElement(ScopedStatementGraph, {...without, focusedNodeId: 'inclusion'}));
    expect(withoutHtml).not.toContain('data-clause-node="positive"');
    expect(withoutHtml).not.toContain('data-clause-node="membership"');
    expect(withoutHtml.indexOf('data-frame-node="changed"')).toBeLessThan(withoutHtml.indexOf('data-frame-node="exists-radius"'));
    const subset = first.document.relations.find(relation => relation.nodeId === 'inclusion' && relation.kind === 'subset')!;
    const changed = { ...first.document, relations: first.document.relations.map(relation => relation.id === subset.id ? { ...relation, ports: relation.ports.map((port, index) => ({ ...port, objectId: relation.ports[1 - index].objectId })) } : relation) };
    const graph = compileScopedStatementGraph(changed, compileReading(changed))!.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    expect(graph.edges.find(edge => edge.relationId === subset.id && edge.role === 'subset')!.objectId).toBe(subset.ports[1].objectId);
  });

  it('keeps negation, antecedent existentials and equivalence branches explicit', () => {
    const source = scopedFixture();
    for (const tree of [frame('negative', 'not', [source.nodes.body]), frame('conditional', 'implies', [source.nodes.body, leaf('q', 'Q', constant('Q'))]), frame('equivalent', 'iff', [leaf('unknown', 'OpaqueProperty', constant('OpaqueProperty')), source.nodes.body])]) {
      const value = fixture(tree), rendered = renderToStaticMarkup(createElement(ScopedStatementGraph, { ...value, focusedNodeId: 'inclusion' }));
      expect(rendered).toContain(`data-logic-kind="${tree.kind}"`);
      expect(rendered).toContain('data-frame-node="exists-radius"');
      if (tree.kind === 'implies') expect(rendered.indexOf('data-logic-edge="assumption"')).toBeLessThan(rendered.indexOf('data-frame-node="exists-radius"'));
      if (tree.kind === 'iff') { expect(rendered).toContain('First condition'); expect(rendered).toContain('Second condition'); expect(rendered).toContain('OpaqueProperty'); }
    }
  });

  it('retains distinct port occurrences when an object is reused and does not invent predicate outputs', () => {
    const source = scopedFixture(), x = variable(source.binders.point);
    const fx = { kind: 'app' as const, fn: variable(source.binders.family), args: [x, x] };
    const value = fixture(leaf('repeat', 'f x x = f x x', call('Eq', [fx, fx])));
    const graph = value.model.clauses[0].graphs[0];
    const pointId = value.document.objects.find(object => object.expression.kind === 'var' && object.expression.id === 'point')!.id;
    const repeated = graph.edges.filter(edge => edge.objectId === pointId);
    expect(repeated.map(edge => edge.role)).toEqual(['input 1', 'input 2']);
    expect(new Set(repeated.map(edge => edge.id)).size).toBe(2);
    expect(graph.edges.filter(edge => edge.role === 'left' || edge.role === 'right')).toHaveLength(2);
    const unknown = { ...value.document, relations: value.document.relations.map(relation => relation.kind === 'equality' ? { ...relation, kind: 'predicate' as const, fidelity: 'structural' as const, ports: [...relation.ports, { role: 'output', objectId: relation.ports[0].objectId }] } : relation) };
    expect(compileScopedStatementGraph(unknown, compileReading(unknown))!.clauses[0].graphs[0].edges.find(edge => edge.role === 'output' && edge.relationId === unknown.relations[0].id)?.kind).toBe('argument');
  });

  it('uses relation occurrence scope rather than the object first-created scope, and isolates lambda-local groups', () => {
    const value = scopedFixture();
    const changed = { ...value.document, objects: value.document.objects.map(object => ({ ...object, scopeId: 'first-occurrence-elsewhere' })) };
    expect(compileScopedStatementGraph(changed, compileReading(changed))!.clauses.map(clause => clause.graphs.map(graph => graph.scopeId))).toEqual(value.model.clauses.map(clause => clause.graphs.map(graph => graph.scopeId)));
    const local = { ...value.binders.point, id: 'local-point', name: 'x', role: 'lambda' as const };
    const lambda = { kind: 'lambda' as const, binder: local, body: { kind: 'app' as const, fn: variable(value.binders.family), args: [variable(local)] } };
    const expression = call('Opaque.wrapper', [call('Metric.ball', [variable(value.binders.point), variable(value.binders.radius)]), lambda]);
    const nested = fixture(leaf('nested', 'Opaque.wrapper (ball x δ) (fun x => c x)', expression));
    expect(nested.model.clauses[0].graphs.some(graph => graph.groupRole === 'local-expression')).toBe(true);
    for (const graph of nested.model.clauses[0].graphs) expect(graph.nodes.filter(node => node.kind === 'relation').every(node => node.relation!.scopeId === graph.scopeId)).toBe(true);
    expect(renderToStaticMarkup(createElement(ScopedStatementGraph, {...nested, focusedNodeId: 'nested'}))).toContain('Inside a local expression scope');
  });

  it('names shadowed declarations and retains lambda binder kind, type, and local scope', () => {
    const source = scopedFixture(), outer = { ...source.binders.point, id: 'outer-x', name: 'x' }, inner = { ...source.binders.point, id: 'inner-x', name: 'x' };
    const expression = call('Eq', [{ kind:'app', fn:variable(source.binders.family), args:[variable(outer),variable(inner)] }, variable(outer)]);
    const value = fixture(frame('outer', 'forall', [frame('inner', 'forall', [leaf('shadow', 'uses both x declarations', expression)], inner)], outer));
    const graph = value.model.clauses[0].graphs[0];
    const variables = graph.nodes.filter(node => node.object?.expression.kind === 'var' && node.object.expression.name === 'x');
    expect(variables).toHaveLength(2);
    expect(variables.map(node=>node.referenceNote)).toEqual(['from ∀ x [declaration 1]', 'from ∀ x [declaration 2]']);
    const rendered = renderToStaticMarkup(createElement(ScopedStatementGraph, {...value, focusedNodeId:'shadow'}));
    for (const note of variables.map(node=>node.referenceNote!)) expect(rendered).toContain(note);
    expect(rendered).toContain('∀ x [declaration 1]'); expect(rendered).toContain('∀ x [declaration 2]');
    const local = { ...inner, id:'lambda-local', role:'lambda' as const };
    const nested = fixture(leaf('lambda', 'nested function', call('Opaque.wrapper', [call('Metric.ball',[variable(outer),variable(source.binders.radius)]), {kind:'lambda',binder:local,body:{kind:'app',fn:variable(source.binders.family),args:[variable(local)]}}])));
    const localGraph = nested.model.clauses[0].graphs.find(graph=>graph.groupRole==='local-expression')!;
    expect(localGraph.localBindings).toEqual([{id:'lambda-local',role:'lambda',name:'x',type:'X'}]);
    expect(renderToStaticMarkup(createElement(ScopedStatementGraph, {...nested, focusedNodeId:'lambda'}))).toContain('λ x : X');
  });

  it('requires a deliberate clause choice when the authoritative selection is not a leaf', () => {
    const value = scopedFixture();
    const rendered = renderToStaticMarkup(createElement(ScopedStatementGraph,value));
    expect(rendered).toContain('Choose a clause to draw');
    expect(rendered).not.toContain('data-graph-node');
  });

  it('keeps foreign constructors symbolic and refuses the separate positional lane', () => {
    const value = scopedFixture();
    expect(compileScopedStatementGraph({ ...value.document, presentation: { kind: 'component', target: 'term' } }, value.reading)).toBeUndefined();
    const expression = call('Set.Subset', [call('Metric.ball', [variable(value.binders.point), variable(value.binders.radius)], { fn: constant('Metric.ball', false) }), { kind: 'app', fn: variable(value.binders.family), args: [variable(value.binders.index)] }]);
    const foreign = fixture(leaf('foreign', 'foreign Metric.ball x δ ⊆ c i', expression));
    expect(foreign.model.clauses[0].graphs[0].nodes.some(node => node.relation?.kind === 'metric-region')).toBe(false);
    expect(foreign.model.clauses[0].graphs[0].nodes.some(node => node.relation?.kind === 'predicate')).toBe(true);
  });

  it('reports a complete-group bound instead of silently dropping ports', () => {
    const value = scopedFixture();
    const relation = value.document.relations.find(relation => relation.nodeId === 'inclusion' && relation.kind === 'application')!;
    const inflated = { ...value.document, relations: [...value.document.relations, ...Array.from({ length: 21 }, (_, index) => ({ ...relation, id: `${relation.id}:${index}` }))] };
    const model = compileScopedStatementGraph(inflated, compileReading(inflated));
    // A second valid composition keeps this view eligible while the large group
    // remains an explicit source-backed boundary.
    const other = { ...relation, id: 'other', nodeId: 'positive', scopeId: 'scope:positive' };
    const shown = { ...inflated, relations: [...inflated.relations, other] };
    const graph = compileScopedStatementGraph(shown, compileReading(shown))!.clauses.find(clause => clause.node.id === 'inclusion')!.graphs[0];
    expect(model).toBeUndefined();
    expect(graph.reason).toContain('exceeds the diagram bound');
    expect(graph.nodes).toEqual([]);
    expect(graph.edges).toEqual([]);
    expect(graph.relationIds.length).toBeGreaterThan(20);
  });
});
