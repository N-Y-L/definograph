import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode, TypeDescriptor } from '../core/types';
import { compileReading } from '../reading';
import { compileSemanticDocument, expressionKey } from '../semantic';
import { TypedConstructionFigure } from './TypedConstructionFigure';
import { compileTypedConstruction, isUsefulConstruction } from './model';

const typeSort: Expr = { kind: 'sort', name: '1' };
const propSort: Expr = { kind: 'sort', name: '0' };
const constant = (name: string): Expr => ({ kind: 'const', name });
const variable = (id: string, name = id, type = 'Type'): Expr => ({ kind: 'var', id, name, type });
const unknown = (lean: string): TypeDescriptor => ({ kind: 'unknown', lean });
const arrow = (id: string, domain: Expr, body: Expr, name = 'a'): Expr => ({ kind: 'forall', binder: { id, name, type: 'input type', role: 'universal', dependsOn: [] }, binderType: domain, body });
interface Binding { id: string; name?: string; type: string; expression?: Expr; descriptor?: TypeDescriptor; role?: Binder['role'] }
const carrier = (id: string, name = id): Binding => ({ id, name, type: 'Type', expression: typeSort, descriptor: { kind: 'type', lean: 'Type' } });
const map = (id: string, from: Expr, to: Expr, type = 'A → B'): Binding => ({ id, type, expression: arrow(`${id}.arg`, from, to), descriptor: { kind: 'map', lean: type } });
const leaf: StatementNode = { id: 'condition', kind: 'predicate', label: 'True', lean: 'True', expression: constant('True'), children: [] };
function introduction(binding: Binding, child: StatementNode, previous: string[] = []): StatementNode {
  const binder: Binder = { id: binding.id, name: binding.name ?? binding.id, type: binding.type, role: binding.role ?? 'universal', dependsOn: previous, typeDescriptor: binding.descriptor };
  const lambda: Expr = { kind: binder.role === 'parameter' || binder.role === 'existential' ? 'lambda' : 'forall', binder, binderType: binding.expression, body: child.expression };
  return { id: `node:${binding.id}`, kind: binder.role === 'existential' ? 'exists' : binder.role === 'parameter' ? 'parameter' : 'forall', label: binder.name, lean: binder.type, binder, expression: binder.role === 'existential' ? { kind: 'app', fn: constant('Exists'), args: [binding.expression ?? constant('Unknown.type'), lambda] } : lambda, children: [child] };
}
function compile(bindings: Binding[]) {
  const tree = bindings.reduceRight((child, binding, index) => introduction(binding, child, bindings.slice(0, index).map(b => b.id)), leaf);
  const document = compileSemanticDocument({ source: 'typed fixture', tree, expression: tree.expression });
  const reading = compileReading(document);
  const binders = reading.quantifierGroups[0].binders;
  return { document, reading, binders, model: compileTypedConstruction(document, binders) };
}
function rendered(bindings: Binding[]) {
  const result = compile(bindings);
  return { ...result, html: renderToStaticMarkup(createElement(TypedConstructionFigure, { document: result.document, binders: result.binders, onObjectSelect: () => undefined })) };
}

describe('typed construction grammar', () => {
  it('shares exact carrier endpoints in an abstract map chain and attaches an element to its type', () => {
    const { model, document } = compile([carrier('A'), carrier('B'), carrier('C'), map('f', variable('A'), variable('B')), map('g', variable('B'), variable('C'), 'B → C'), { id: 'x', type: 'A', expression: variable('A'), descriptor: unknown('A') }]);
    expect(model.status).toBe('ready');
    expect(model.types.map(t => t.label)).toEqual(['A', 'B', 'C']);
    expect(model.maps).toHaveLength(2);
    expect(model.maps[0].codomainId).toBe(model.maps[1].domainId);
    expect(model.members[0].typeId).toBe(model.maps[0].domainId);
    expect(model.objects.map(o => o.binderId)).toEqual(['A', 'B', 'C', 'f', 'g', 'x']);
    expect(document.scenes).toHaveLength(0);
  });

  it('keeps similarly named types distinct even when their pretty-printed descriptors agree', () => {
    const f = map('f', variable('A1', 'A'), variable('A2', 'A'), 'A → A');
    f.descriptor = { kind: 'map', lean: 'A → A', domain: unknown('A'), codomain: unknown('A') };
    const { model } = compile([carrier('A1', 'A'), carrier('A2', 'A'), f]);
    expect(model.types).toHaveLength(2);
    expect(model.types.map(t => t.label)).toEqual(['A', 'A']);
    expect(model.maps[0].domainId).not.toBe(model.maps[0].codomainId);
  });

  it('keeps distinct universe instantiations of the same type constructor separate', () => {
    const lifted = (level: string): Expr => ({ kind: 'app', fn: { kind: 'const', name: 'ULift', levels: [level, '0'] }, args: [constant('Nat')], argumentKinds: ['type'] });
    const domain = lifted('1'), codomain = lifted('2');
    expect(expressionKey(domain)).not.toBe(expressionKey(codomain));
    expect(expressionKey({ kind: 'const', name: 'Real', levels: [] })).toBe(expressionKey(constant('Real')));
    const { model } = compile([map('f', domain, codomain, 'ULift Nat → ULift Nat')]);
    expect(model.types).toHaveLength(2);
    expect(model.maps[0].domainId).not.toBe(model.maps[0].codomainId);
  });

  it('does not reinterpret a curried function as independent maps between its input types', () => {
    const { model } = compile([carrier('A'), carrier('B'), carrier('C'), map('h', variable('A'), arrow('h.arg2', variable('B'), variable('C'), 'b'), 'A → B → C')]);
    expect(model.maps).toHaveLength(0);
    expect(model.signatures[0]).toMatchObject({ kind: 'multi-input-map', inputs: [{ type: 'A' }, { type: 'B' }], result: 'C', resultDependsOn: [] });
  });

  it('shows a relation as ordered inputs yielding a proposition rather than an asserted edge', () => {
    const { model, html } = rendered([carrier('A'), carrier('B'), map('R', variable('A'), arrow('R.arg2', variable('B'), propSort), 'A → B → Prop')]);
    expect(model.maps).toHaveLength(0);
    expect(model.signatures[0]).toMatchObject({ kind: 'relation', inputs: [{ type: 'A' }, { type: 'B' }], result: 'Prop' });
    expect(html).toContain('no truth value is asserted here');
  });

  it('retains dependent result types and their exact input dependency', () => {
    const family = map('B', variable('A'), typeSort, 'A → Type');
    const result: Expr = { kind: 'app', fn: variable('B', 'B', 'A → Type'), args: [variable('f.arg', 'a', 'A')], argumentKinds: ['value'] };
    const { model } = compile([carrier('A'), family, map('f', variable('A'), result, '(a : A) → B a')]);
    expect(model.maps).toHaveLength(0);
    expect(model.signatures[0]).toMatchObject({ kind: 'family', result: 'Type' });
    expect(model.signatures[1]).toMatchObject({ kind: 'dependent-map', inputs: [{ name: 'a', type: 'A' }], result: 'B(a)', resultDependsOn: [0] });
  });

  it('preserves dependencies of later input types, not just the final result', () => {
    const later: Expr = { kind: 'app', fn: variable('B', 'B', 'A → Type'), args: [variable('h.arg', 'a', 'A')], argumentKinds: ['value'] };
    const { model } = compile([carrier('A'), map('B', variable('A'), typeSort, 'A → Type'), map('h', variable('A'), arrow('h.arg2', later, constant('Nat'), 'b'))]);
    expect(model.signatures[1]).toMatchObject({ kind: 'dependent-map', inputs: [{ dependsOn: [] }, { dependsOn: [0] }], resultDependsOn: [] });
  });

  it('labels a set of A without asserting membership of an arbitrary x : A', () => {
    const { model, html } = rendered([carrier('A'), { id: 's', type: 'Set A', expression: { kind: 'app', fn: constant('Set'), args: [variable('A')] }, descriptor: { kind: 'set', lean: 'Set A', element: unknown('A') } }, { id: 'x', type: 'A', expression: variable('A') }]);
    expect(model.members.map(m => [m.name, m.kind])).toEqual([['s', 'set'], ['x', 'element']]);
    expect(new Set(model.members.map(m => m.typeId)).size).toBe(1);
    expect(html).toContain('set of A');
    expect(html).not.toContain('∈');
  });

  it('rejects groups assembled from different branches even when their roles match', () => {
    const left = introduction(carrier('A'), { ...leaf, id: 'left' });
    const right = introduction(carrier('B'), { ...leaf, id: 'right' });
    const tree: StatementNode = { id: 'or', kind: 'or', label: 'Either', lean: 'or', expression: constant('Or'), children: [left, right] };
    const document = compileSemanticDocument({ source: 'branches', tree, expression: tree.expression });
    const reading = compileReading(document);
    const result = compileTypedConstruction(document, reading.quantifierGroups.flatMap(group => group.binders));
    expect(result.status).toBe('invalid-scope');
    expect(result.objects).toHaveLength(0);
  });

  it('keeps an existential construction separate and references only previously available carriers', () => {
    const { document, reading } = compile([carrier('A'), { id: 'x', type: 'A', expression: variable('A'), role: 'existential' }, carrier('Later')]);
    const group = reading.quantifierGroups.find(g => g.kind === 'exists')!;
    const model = compileTypedConstruction(document, group.binders);
    expect(model.role).toBe('existential');
    expect(model.objects.map(o => o.name)).toEqual(['x']);
    expect(model.types.map(t => t.label)).toEqual(['A']);
    expect(model.types[0].introduced).toBe(false);
    const html = renderToStaticMarkup(createElement(TypedConstructionFigure, { document, binders: group.binders }));
    expect(html).toContain('data-construction-role="existential"');
    expect(html).toContain('There exists');
    expect(html).not.toContain('Later');
  });

  it('never guesses a map from the pretty-printed type when typed expression data is missing', () => {
    const { model } = compile([carrier('A'), { id: 'looksLikeMap', type: 'A → B', descriptor: { kind: 'map', lean: 'A → B' } }]);
    expect(model.maps).toHaveLength(0);
    expect(model.signatures).toHaveLength(0);
    expect(model.unknowns[0].name).toBe('looksLikeMap');
  });

  it('does not create a type identity from two identical opaque pretty-printed strings', () => {
    const { model } = compile([carrier('A'), { id: 'x', type: 'mystery', expression: { kind: 'opaque', text: 'same' } }, { id: 'y', type: 'mystery', expression: { kind: 'opaque', text: 'same' } }]);
    expect(model.types).toHaveLength(1);
    expect(model.members).toHaveLength(0);
    expect(model.unknowns).toHaveLength(2);
  });

  it('suppresses repetitive scalar-only introductions and does not infer cardinality from Fin', () => {
    const scalars = rendered([{ id: 'r', type: 'ℝ', expression: constant('Real'), descriptor: { kind: 'real', lean: 'ℝ' } }]);
    expect(isUsefulConstruction(scalars.model)).toBe(false);
    expect(scalars.html).toBe('');
    const { model } = compile([carrier('A'), { id: 'x', type: 'Fin 0', expression: { kind: 'app', fn: constant('Fin'), args: [{ kind: 'literal', value: 0 }] }, descriptor: { kind: 'finite', lean: 'Fin 0', cardinality: 0 } }]);
    expect(model.members[0].kind).toBe('element');
    expect(model.types.find(t => t.label === 'Fin 0')).toBeDefined();
  });

  it('preserves parameter roles and exposes selection targets without sample controls', () => {
    const { html, model } = rendered([{ ...carrier('A'), role: 'parameter' }, { ...map('f', variable('A'), variable('A'), 'A → A'), role: 'parameter' }]);
    expect(html).toContain('data-construction-role="parameter"');
    expect(html).toContain('Parameter f : A → A');
    expect(html).toContain(`data-reading-object="${model.maps[0].objectId}"`);
    expect(html).toContain('role="button"');
    expect(html).not.toContain('type="range"');
    expect(html).not.toContain('type="number"');
  });

  it('routes adjacent maps on a straight baseline and a longer map above them', () => {
    const { html } = rendered([carrier('A'), carrier('B'), carrier('C'), map('f', variable('A'), variable('B')), map('g', variable('B'), variable('C')), map('h', variable('A'), variable('C'))]);
    const paths = [...html.matchAll(/class="tc-map-arrow" d="([^"]+)"/g)].map(match => match[1]);
    expect(paths).toHaveLength(3);
    expect(paths[0]).toMatch(/^M[\d.]+ 111 Q[\d.]+ 111,[\d.]+ 111$/);
    expect(paths[1]).toMatch(/^M[\d.]+ 111 Q[\d.]+ 111,[\d.]+ 111$/);
    expect(paths[2]).toMatch(/^M[\d.]+ 111 Q[\d.]+ 15,[\d.]+ 111$/);
  });
});
