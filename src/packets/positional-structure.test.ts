import { describe, expect, it } from 'vitest';
import { readFileSync } from 'node:fs';
import { createExactJsonTools, type JsonValue } from './packet';
import {
  buildPositionalStructuralDrawing, readPositionalStructuralDrawing, buildStructuralDrawing, readStructuralDrawing,
  type PositionalStructuralInput, type PositionalStructuralDrawing, type PositionalStructuralDeclaration,
  type StructuralNode, type StructuralName, type StructurePath, type StructureResult, type StructureLimits,
} from './structure';
import { validateSourceSnapshot } from '../editor/source-snapshot';
import { validateSourceOccurrence } from '../editor/source-occurrence';

const name = (text = 'same'): StructuralName => ['str', ['anonymous'], text];
const natural = (value: number | string): JsonValue => ['nat', String(value)];
const bvar = (index: number): JsonValue => ['bvar', natural(index)];
const constant = (text: string): JsonValue => ['const', name(text), []];
const sort: JsonValue = ['sort', ['succ', ['zero']]];
const port = (previous: JsonValue, type: JsonValue, info = 'default'): JsonValue => ['port', previous, { name: name(), info }, type];
const letEntry = (previous: JsonValue, type: JsonValue, value: JsonValue, nondep: boolean): JsonValue => ['letE', previous, name(), nondep, type, value];
const { canonical } = createExactJsonTools();
const exact = (value: unknown) => canonical(value as JsonValue);
function ok<T>(result: StructureResult<T>): T {
  if (!result.ok) throw new Error(JSON.stringify(result.error)); return result.value;
}
function refused(result: StructureResult<unknown>, code?: string) {
  expect(result.ok).toBe(false);
  if (!result.ok) {
    if (code) expect(result.error.code).toBe(code);
    expect(result.error.message).not.toBe(''); expect(Array.isArray(result.error.path)).toBe(true);
  }
}
function mixed(): PositionalStructuralInput {
  // A, x, y := x, h := y. All four printed names intentionally coincide.
  const A = port(['nil'], sort, 'implicit');
  const x = port(A, bvar(0));
  const y = letEntry(x, bvar(1), bvar(0), false);
  const h = letEntry(y, bvar(2), bvar(0), true);
  return { home: { arity: 4, telescope: h },
    term: ['lam', name(), bvar(3), ['app', bvar(0), bvar(1)], 'default'],
    type: ['forallE', name(), bvar(3), bvar(4), 'default'] };
}
function build(input = mixed(), sourceIdentity = 'positional-control', sourcePath?: StructurePath) {
  return ok(buildPositionalStructuralDrawing(input, { sourceIdentity, sourcePath }));
}
function nodeAt(drawing: PositionalStructuralDrawing, path: StructurePath): StructuralNode {
  const matches = drawing.nodes.filter(node => exact(node.sourcePath) === exact(path));
  expect(matches).toHaveLength(1); return matches[0];
}
function context(drawing: PositionalStructuralDrawing): PositionalStructuralDeclaration[] {
  return drawing.contextDeclarationIds.map(id => {
    const declaration = drawing.declarations.find(value => value.id === id);
    if (declaration?.kind !== 'positional') throw new Error('missing positional declaration'); return declaration;
  });
}

/** This oracle walks the input constructors, not the drawing's proposed homes.
 * It checks each reference against oldest-first ambient and lexical identities. */
function checkScopes(input: PositionalStructuralInput, drawing: PositionalStructuralDrawing) {
  const expectedDeclarations: { value: JsonValue[]; path: StructurePath }[] = [];
  function telescope(value: JsonValue, path: StructurePath) {
    const entry = value as JsonValue[];
    if (entry[0] === 'nil') { expect(entry).toEqual(['nil']); return; }
    expect(['port', 'letE']).toContain(entry[0]);
    telescope(entry[1], [...path, 1]); expectedDeclarations.push({ value: entry, path });
  }
  telescope(input.home.telescope, [...drawing.sourcePath, 'home', 'telescope']);
  expect(drawing.arity).toBe(input.home.arity);
  expect(expectedDeclarations).toHaveLength(input.home.arity);
  expect(drawing.contextDeclarationIds).toHaveLength(input.home.arity);
  const empty = drawing.homes.find(home => home.id === drawing.emptyHomeId)!;
  expect(empty).toEqual({ id: drawing.emptyHomeId, parentId: null, declarationId: null });
  const visited = new Set<string>();
  function expression(value: JsonValue, path: StructurePath, scope: string[], homeId: string): string {
    const source = value as JsonValue[], node = nodeAt(drawing, path);
    expect(visited.has(node.id)).toBe(false); visited.add(node.id);
    expect(node.kind).toBe(source[0]); expect(node.homeId).toBe(homeId);
    const walk = (position: number, nextScope = scope, nextHome = homeId) => expression(source[position], [...path, position], nextScope, nextHome);
    let roles: string[] = [], children: string[] = [];
    switch (node.kind) {
      case 'bvar': {
        const index = Number((source[1] as JsonValue[])[1]);
        expect(node.index).toBe(index); expect(node.declarationId).toBe(scope[scope.length - index - 1]); break;
      }
      case 'sort': expect(node.level).toEqual(source[1]); break;
      case 'const': expect(node.name).toEqual(source[1]); expect(node.levels).toEqual(source[2]); break;
      case 'lit': expect(node.literal).toEqual(source[1]); break;
      case 'proj':
        expect(node.owner).toEqual(source[1]); expect(node.field).toEqual(source[2]); roles = ['value']; children = [walk(3)]; break;
      case 'app': roles = ['function', 'argument']; children = [walk(1), walk(2)]; break;
      case 'lam': case 'forallE': case 'letE': {
        expect(node.name).toEqual(source[1]);
        const declaration = drawing.declarations.find(value => value.id === node.declarationId);
        if (!declaration || declaration.kind === 'positional') throw new Error('missing owned binder');
        expect(declaration.kind).toBe(node.kind === 'letE' ? 'let' : 'binder');
        expect(declaration.nodeId).toBe(node.id); expect(declaration.homeId).toBe(homeId);
        expect(drawing.homes.find(home => home.id === declaration.bodyHomeId)).toEqual({ id: declaration.bodyHomeId, parentId: homeId, declarationId: declaration.id });
        const extended = [...scope, declaration.id];
        if (node.kind === 'letE') {
          expect(node.nondep).toBe(source[5]); roles = ['type', 'value', 'body'];
          children = [walk(2), walk(3), walk(4, extended, declaration.bodyHomeId)];
        } else {
          expect(node.binderInfo).toBe(source[4]); roles = ['domain', 'body'];
          children = [walk(2), walk(3, extended, declaration.bodyHomeId)];
        }
        break;
      }
      default: throw new Error('non-Core reference entered the positional drawing');
    }
    expect(node.children.map(edge => edge.role)).toEqual(roles);
    expect(node.children.map(edge => edge.nodeId)).toEqual(children);
    return node.id;
  }
  let prefix = drawing.emptyHomeId;
  const scope: string[] = [], entries = context(drawing);
  expectedDeclarations.forEach(({ value, path }, i) => {
    const declaration = entries[i];
    expect(declaration.sourcePath).toEqual(path); expect(declaration.homeId).toBe(prefix);
    expect(declaration.constructor).toBe(value[0]);
    expect(drawing.homes.find(home => home.id === declaration.bodyHomeId)).toEqual({ id: declaration.bodyHomeId, parentId: prefix, declarationId: declaration.id });
    if (declaration.constructor === 'port') {
      const attributes = value[2] as { name: JsonValue; info: JsonValue };
      expect(declaration.name).toEqual(attributes.name); expect(declaration.binderInfo).toBe(attributes.info);
      expect(declaration.children).toEqual([{ role: 'type', nodeId: expression(value[3], [...path, 3], scope, prefix) }]);
    } else {
      expect(declaration.name).toEqual(value[2]); expect(declaration.nondep).toBe(value[3]);
      expect(declaration.children).toEqual([
        { role: 'type', nodeId: expression(value[4], [...path, 4], scope, prefix) },
        { role: 'definitionValue', nodeId: expression(value[5], [...path, 5], scope, prefix) },
      ]);
    }
    for (const key of ['fvarId', 'userName', 'index', 'localKind']) expect(Object.hasOwn(declaration, key)).toBe(false);
    scope.push(declaration.id); prefix = declaration.bodyHomeId;
  });
  expect(drawing.rootHomeId).toBe(prefix);
  expect(expression(input.term, [...drawing.sourcePath, 'term'], scope, prefix)).toBe(drawing.rootId);
  expect(expression(input.type, [...drawing.sourcePath, 'type'], scope, prefix)).toBe(drawing.typeRootId);
  expect(visited.size).toBe(drawing.nodes.length);
  expect(drawing.rootId).not.toBe(drawing.typeRootId);
  expect(new Set([...drawing.nodes, ...drawing.homes, ...drawing.declarations].map(value => value.id)).size)
    .toBe(drawing.nodes.length + drawing.homes.length + drawing.declarations.length);
  expect(Object.hasOwn(drawing, 'externalDeclarationIds')).toBe(false);
  expect(exact(ok(readPositionalStructuralDrawing(drawing)))).toBe(exact(input));
}

describe('independently scoped positional constructor drawings', () => {
  it('retains the mixed four-entry home and distinct term/type binders despite identical names', () => {
    const input = mixed(), drawing = build(input); checkScopes(input, drawing);
    expect(drawing.schema).toBe('definograph.structure.positional.v1');
    expect(drawing.sourcePath).toEqual(['selected']);
    const [A, x, y, h] = context(drawing);
    expect([A, x, y, h].map(declaration => declaration.sourcePath)).toEqual([
      ['selected', 'home', 'telescope', 1, 1, 1], ['selected', 'home', 'telescope', 1, 1],
      ['selected', 'home', 'telescope', 1], ['selected', 'home', 'telescope'],
    ]);
    const lambda = nodeAt(drawing, ['selected', 'term']), product = nodeAt(drawing, ['selected', 'type']);
    if (lambda.kind !== 'lam' || product.kind !== 'forallE') throw new Error('expected independent owned binders');
    expect(lambda.declarationId).not.toBe(product.declarationId);
    expect(nodeAt(drawing, ['selected', 'term', 3, 1])).toMatchObject({ kind: 'bvar', declarationId: lambda.declarationId });
    expect(nodeAt(drawing, ['selected', 'term', 3, 2])).toMatchObject({ kind: 'bvar', declarationId: h.id });
    expect(nodeAt(drawing, ['selected', 'type', 3])).toMatchObject({ kind: 'bvar', declarationId: A.id });
    expect(h.constructor === 'letE' && h.nondep).toBe(true);
    expect(h.children.map(edge => edge.role)).toEqual(['type', 'definitionValue']);
    expect(nodeAt(drawing, [...y.sourcePath, 5])).toMatchObject({ declarationId: x.id });
    expect(nodeAt(drawing, [...h.sourcePath, 5])).toMatchObject({ declarationId: y.id });
  });

  it.each([0, 1, 2, 3])('resolves root bvar %s through the complete newest-first ambient home', index => {
    const input = mixed(); input.term = bvar(index); const drawing = build(input); checkScopes(input, drawing);
    expect(nodeAt(drawing, ['selected', 'term'])).toMatchObject({ declarationId: drawing.contextDeclarationIds[3 - index] });
  });

  it('draws every Core constructor and exact large Name/Level/literal fields at nested positions', () => {
    const input = mixed(), big = '9007199254740993';
    const numeric: JsonValue = ['num', name('segment.with.dot'), natural(big)];
    const levels: JsonValue[] = [['zero'], ['succ', ['param', numeric]], ['max', ['zero'], ['param', name('u')]], ['imax', ['param', numeric], ['succ', ['zero']]]];
    input.term = ['lam', numeric, ['sort', levels[3]], ['letE', name(), bvar(0), ['lit', ['natVal', natural(big)]],
      ['app', ['proj', numeric, natural('9007199254740992'), bvar(0)], ['forallE', name(), bvar(1),
        ['app', ['const', numeric, levels], ['lit', ['strVal', 'é e\u0301 \u200b 🧭\n']]], 'strictImplicit']], true], 'instImplicit'];
    const drawing = build(input); checkScopes(input, drawing);
    expect(new Set(drawing.nodes.map(node => node.kind))).toEqual(new Set(['sort', 'bvar', 'lam', 'letE', 'lit', 'app', 'proj', 'forallE', 'const']));
  });

  it('retains unused context entries and separates capture/path identity without aliasing source data', () => {
    const input = mixed(); input.term = constant('True'); input.type = ['sort', ['zero']];
    const expected = structuredClone(input), sourcePath = ['checking', 'selected'];
    const first = build(input, 'capture-one:path-root', sourcePath), second = build(input, 'capture-two:path-argument', sourcePath);
    checkScopes(expected, first); checkScopes(expected, second);
    expect(first.contextDeclarationIds).toHaveLength(4);
    expect(first.nodes.some(node => second.nodes.some(other => other.id === node.id))).toBe(false);
    (input.home.telescope as JsonValue[])[2] = name('changed'); input.term = constant('False'); sourcePath.push('changed');
    expect(exact(ok(readPositionalStructuralDrawing(first)))).toBe(exact(expected));
    expect(first.sourcePath).toEqual(['checking', 'selected']);
  });

  it('keeps lexical binders inside contextual types and values distinct from the ambient entry they precede', () => {
    const input: PositionalStructuralInput = { home: { arity: 2, telescope: letEntry(port(['nil'], sort),
      ['forallE', name(), bvar(0), bvar(1), 'default'], ['lam', name(), bvar(0), bvar(0), 'default'], false) }, term: bvar(0), type: bvar(1) };
    const drawing = build(input); checkScopes(input, drawing);
    const [A, definition] = context(drawing);
    const typeBody = nodeAt(drawing, [...definition.sourcePath, 4, 3]);
    const valueBody = nodeAt(drawing, [...definition.sourcePath, 5, 3]);
    expect(typeBody).toMatchObject({ declarationId: A.id });
    if (valueBody.kind !== 'bvar') throw new Error('expected a bound value');
    expect(valueBody.declarationId).not.toBe(A.id); expect(valueBody.declarationId).not.toBe(definition.id);
  });

  it('uses independent graph occurrences when term and type share the same input object', () => {
    const input = mixed(); input.type = input.term;
    const drawing = build(input); checkScopes(input, drawing);
    const term = nodeAt(drawing, ['selected', 'term']), type = nodeAt(drawing, ['selected', 'type']);
    if (term.kind !== 'lam' || type.kind !== 'lam') throw new Error('expected lambdas');
    expect(term.declarationId).not.toBe(type.declarationId);
  });
});

describe('positional refusal and independent readback', () => {
  it('reads a hand-authored graph with no builder-produced source and follows a coherent changed reference', () => {
    const drawing: PositionalStructuralDrawing = {
      schema: 'definograph.structure.positional.v1', sourceIdentity: 'hand-authored', sourcePath: ['selected'],
      rootId: 'term', typeRootId: 'type', rootHomeId: 'after-h', emptyHomeId: 'empty', arity: 2,
      contextDeclarationIds: ['A', 'h'],
      homes: [{ id: 'empty', parentId: null, declarationId: null }, { id: 'after-A', parentId: 'empty', declarationId: 'A' }, { id: 'after-h', parentId: 'after-A', declarationId: 'h' }],
      declarations: [
        { kind: 'positional', constructor: 'port', id: 'A', homeId: 'empty', bodyHomeId: 'after-A', sourcePath: ['selected', 'home', 'telescope', 1], name: name(), binderInfo: 'implicit', children: [{ role: 'type', nodeId: 'A-type' }] },
        { kind: 'positional', constructor: 'letE', id: 'h', homeId: 'after-A', bodyHomeId: 'after-h', sourcePath: ['selected', 'home', 'telescope'], name: name(), nondep: true, children: [{ role: 'type', nodeId: 'h-type' }, { role: 'definitionValue', nodeId: 'h-value' }] },
      ],
      nodes: [
        { kind: 'sort', id: 'A-type', sourcePath: ['selected', 'home', 'telescope', 1, 3], homeId: 'empty', level: ['succ', ['zero']], children: [] },
        { kind: 'bvar', id: 'h-type', sourcePath: ['selected', 'home', 'telescope', 4], homeId: 'after-A', index: 0, declarationId: 'A', children: [] },
        { kind: 'bvar', id: 'h-value', sourcePath: ['selected', 'home', 'telescope', 5], homeId: 'after-A', index: 0, declarationId: 'A', children: [] },
        { kind: 'bvar', id: 'term', sourcePath: ['selected', 'term'], homeId: 'after-h', index: 0, declarationId: 'h', children: [] },
        { kind: 'bvar', id: 'type', sourcePath: ['selected', 'type'], homeId: 'after-h', index: 1, declarationId: 'A', children: [] },
      ],
    };
    const expected: PositionalStructuralInput = { home: { arity: 2, telescope: letEntry(port(['nil'], sort, 'implicit'), bvar(0), bvar(0), true) }, term: bvar(0), type: bvar(1) };
    checkScopes(expected, drawing);
    const term = drawing.nodes.find(node => node.id === 'term')!;
    if (term.kind !== 'bvar') throw new Error('expected term reference');
    term.index = 1; term.declarationId = 'A';
    expect(exact(ok(readPositionalStructuralDrawing(drawing)))).toBe(exact({ ...expected, term: bvar(1) }));
  });
  it.each(['self', 'future', 'ambient overflow', 'fvar', 'mvar', 'metadata', 'universe mvar', 'arity', 'legacy natural', 'unknown CTel'])(
    'rejects invalid positional input: %s', mutation => {
      const input = mixed();
      const h = input.home.telescope as JsonValue[], y = h[1] as JsonValue[], x = y[1] as JsonValue[], A = x[1] as JsonValue[];
      switch (mutation) {
        case 'self': A[3] = bvar(0); break;
        case 'future': x[3] = bvar(1); break;
        case 'ambient overflow': input.term = bvar(4); break;
        case 'fvar': input.term = ['fvar', name()]; break;
        case 'mvar': input.term = ['mvar', name()]; break;
        case 'metadata': input.term = ['mdata', ['mdataEntries', []], constant('True')]; break;
        case 'universe mvar': input.type = ['sort', ['mvar', name()]]; break;
        case 'arity': input.home.arity = 3; break;
        case 'legacy natural': input.term = ['bvar', 0]; break;
        case 'unknown CTel': h[0] = 'external'; break;
      }
      refused(buildPositionalStructuralDrawing(input, { sourceIdentity: 'invalid-control' }));
    });

  it.each(['target', 'index', 'lexical target', 'context order', 'duplicate context', 'dropped context', 'arity',
    'wrong home', 'root home', 'scope cycle', 'missing role', 'role order', 'role name', 'shared node', 'expression cycle',
    'wrong path', 'wrong base path', 'shared root', 'orphan node', 'orphan home', 'orphan declaration', 'duplicate identity',
    'missing declaration', 'wrong owner', 'external impersonation', 'saved telescope'])(
    'rejects incoherent drawing mutation: %s', mutation => {
      const drawing = build(), [A, x, y, h] = context(drawing), root = nodeAt(drawing, ['selected', 'term']);
      const yValue = nodeAt(drawing, [...y.sourcePath, 5]), bodyFunction = nodeAt(drawing, ['selected', 'term', 3, 1]);
      switch (mutation) {
        case 'target': if (yValue.kind === 'bvar') yValue.declarationId = A.id; break;
        case 'index': if (yValue.kind === 'bvar') yValue.index = 1; break;
        case 'lexical target': if (bodyFunction.kind === 'bvar') bodyFunction.declarationId = h.id; break;
        case 'context order': drawing.contextDeclarationIds.reverse(); break;
        case 'duplicate context': drawing.contextDeclarationIds[1] = A.id; break;
        case 'dropped context': drawing.contextDeclarationIds.pop(); break;
        case 'arity': drawing.arity = 3; break;
        case 'wrong home': yValue.homeId = y.bodyHomeId; break;
        case 'root home': drawing.rootHomeId = drawing.emptyHomeId; break;
        case 'scope cycle': drawing.homes.find(home => home.id === y.bodyHomeId)!.parentId = y.bodyHomeId; break;
        case 'missing role': h.children.pop(); break;
        case 'role order': h.children.reverse(); break;
        case 'role name': h.children[1].role = 'storedValue'; break;
        case 'shared node': h.children[1].nodeId = y.children[1].nodeId; break;
        case 'expression cycle': root.children[0].nodeId = root.id; break;
        case 'wrong path': yValue.sourcePath = [...x.sourcePath, 3]; break;
        case 'wrong base path': drawing.sourcePath = ['other']; break;
        case 'shared root': drawing.typeRootId = drawing.rootId; break;
        case 'orphan node': drawing.nodes.push({ ...drawing.nodes[0], id: 'orphan-node' }); break;
        case 'orphan home': drawing.homes.push({ id: 'orphan-home', parentId: null, declarationId: null }); break;
        case 'orphan declaration': drawing.declarations.push({ ...A, id: 'orphan-declaration' }); break;
        case 'duplicate identity': drawing.nodes[0].id = A.id; break;
        case 'missing declaration': drawing.declarations = drawing.declarations.filter(declaration => declaration.id !== y.id); break;
        case 'wrong owner': drawing.declarations.find(declaration => declaration.kind === 'binder')!.homeId = drawing.emptyHomeId; break;
        case 'external impersonation': Object.assign(h, { kind: 'external', fvarId: name() }); break;
        case 'saved telescope': Object.assign(drawing, { telescope: mixed().home.telescope }); break;
      }
      refused(readPositionalStructuralDrawing(drawing), 'malformed');
    });

  it.each(['name', 'binderInfo', 'nondep'])('reads valid changed %s fields as changed source, never from a saved input', mutation => {
    const expected = mixed(), drawing = build(expected), declarations = context(drawing);
    const h = expected.home.telescope as JsonValue[], A = ((h[1] as JsonValue[])[1] as JsonValue[])[1] as JsonValue[];
    if (mutation === 'name') { declarations[0].name = name('renamed'); (A[2] as { name: JsonValue }).name = name('renamed'); }
    else if (mutation === 'binderInfo') {
      if (declarations[0].constructor !== 'port') throw new Error('expected port');
      declarations[0].binderInfo = 'strictImplicit'; (A[2] as { info: JsonValue }).info = 'strictImplicit';
    } else {
      if (declarations[3].constructor !== 'letE') throw new Error('expected let');
      declarations[3].nondep = false; h[3] = false;
    }
    const readback = ok(readPositionalStructuralDrawing(drawing));
    expect(exact(readback)).toBe(exact(expected)); expect(exact(readback)).not.toBe(exact(mixed()));
  });

  it('bounds context, depth, nodes and text independently in build and readback', () => {
    const input = mixed(), drawing = build(input);
    for (const limits of [{ maxExternalDeclarations: 3 }, { maxDepth: 1 }, { maxNodes: 1 }, { maxText: 1 }]) {
      refused(buildPositionalStructuralDrawing(input, { sourceIdentity: 'bounded', limits }), 'limit');
      refused(readPositionalStructuralDrawing(drawing, limits), 'limit');
    }
    for (const limits of [{ maxNodes: 0 }, { maxDepth: -1 }, { maxText: Infinity }, { unknown: 1 }] as Partial<StructureLimits>[]) {
      refused(buildPositionalStructuralDrawing(input, { sourceIdentity: 'bounded', limits }), 'malformed');
      refused(readPositionalStructuralDrawing(drawing, limits), 'malformed');
    }
  });

  it('rejects sparse arrays, extra fields, unpaired surrogates and cyclic source data without guessing', () => {
    const sparse = mixed(); sparse.term = ['const', name(), Array(1)];
    refused(buildPositionalStructuralDrawing(sparse, { sourceIdentity: 'sparse' }));
    const extra = mixed(); Object.assign(extra.home, { registry: [] });
    refused(buildPositionalStructuralDrawing(extra, { sourceIdentity: 'extra' }));
    const unicode = mixed(); unicode.term = ['lit', ['strVal', '\ud800']];
    refused(buildPositionalStructuralDrawing(unicode, { sourceIdentity: 'unicode' }));
    const cycle = mixed(); (cycle.home.telescope as JsonValue[])[1] = cycle.home.telescope;
    refused(buildPositionalStructuralDrawing(cycle, { sourceIdentity: 'cycle' }));
    const graph = build(); graph.contextDeclarationIds = Array(4);
    refused(readPositionalStructuralDrawing(graph));
  });

  it.each(['null', 'number', 'array', 'accessor', 'hidden', 'symbol', 'prototype'])('refuses %s resource settings without executing accessors', mutation => {
    const input = mixed(), graph = build(); let reads = 0;
    let limits: unknown = {};
    if (mutation === 'null') limits = null;
    else if (mutation === 'number') limits = 1;
    else if (mutation === 'array') limits = [];
    else if (mutation === 'accessor') Object.defineProperty(limits, 'maxNodes', { enumerable: true, get() { reads++; throw new Error('must not execute'); } });
    else if (mutation === 'hidden') Object.defineProperty(limits, 'maxNodes', { value: 1, enumerable: false });
    else if (mutation === 'symbol') Object.defineProperty(limits, Symbol('maxNodes'), { value: 1, enumerable: true });
    else Object.setPrototypeOf(limits, { maxNodes: 1 });
    refused(buildPositionalStructuralDrawing(input, { sourceIdentity: 'limits', limits: limits as Partial<StructureLimits> }), 'malformed');
    refused(readPositionalStructuralDrawing(graph, limits as Partial<StructureLimits>), 'malformed');
    expect(reads).toBe(0);
  });

  it.each(['accessor', 'hidden', 'symbol', 'prototype', 'unsafe number'])('rejects %s data before interpreting either input or drawing', mutation => {
    const input = mixed(), graph = build(); let reads = 0;
    for (const value of [input, graph]) {
      if (mutation === 'accessor') Object.defineProperty(value, 'injected', { enumerable: true, get() { reads++; throw new Error('accessor must never execute'); } });
      else if (mutation === 'hidden') Object.defineProperty(value, 'injected', { value: 1, enumerable: false });
      else if (mutation === 'symbol') Object.defineProperty(value, Symbol('injected'), { value: 1, enumerable: true });
      else if (mutation === 'prototype') Object.setPrototypeOf(value, { inherited: true });
      else Object.assign(value, { injected: Number.MAX_SAFE_INTEGER + 1 });
    }
    refused(buildPositionalStructuralDrawing(input, { sourceIdentity: 'hostile-data' }), 'malformed');
    refused(readPositionalStructuralDrawing(graph), 'malformed');
    expect(reads).toBe(0);
  });

  it.each([1, 2] as const)('keeps named profile %s external registries separate from ambient positions', profile => {
    const index = (value: number): JsonValue => profile === 1 ? value : natural(value);
    const external = { constructor: 'cdecl' as const, index: profile === 1 ? 0 : ['nat', '0'] as ['nat', string],
      fvarId: name('identity'), userName: name(), type: constant('Nat'), binderInfo: 'default' as const, kind: 'default' as const };
    refused(buildStructuralDrawing(['bvar', index(0)], { sourceIdentity: 'named', profile, externalContext: [external] }));
    const drawing = ok(buildStructuralDrawing(['fvar', external.fvarId], { sourceIdentity: 'named', profile, externalContext: [external] }));
    expect(ok(readStructuralDrawing(drawing))).toEqual({ expression: ['fvar', external.fvarId], externalContext: [external] });
    expect(drawing.schema).toBe(`definograph.structure.v${profile}`);
  });

  it('keeps a named opaque stored value distinct from a positional assumption port', () => {
    const external = { constructor: 'ldecl' as const, index: ['nat', '0'] as ['nat', string], fvarId: name('opaque-id'), userName: name(),
      type: constant('Nat'), value: ['lit', ['natVal', natural('9007199254740993')]] as JsonValue, nondep: true, kind: 'default' as const };
    const named = ok(buildStructuralDrawing(['fvar', external.fvarId], { sourceIdentity: 'named-opaque', profile: 2, externalContext: [external] }));
    const declaration = named.declarations[0];
    expect(declaration.kind === 'external' && declaration.children.map(edge => edge.role)).toEqual(['type', 'storedValue']);
    const input = { home: { arity: 1, telescope: port(['nil'], constant('Nat')) }, term: bvar(0), type: constant('Nat') };
    const positional = build(input); checkScopes(input, positional);
    expect(context(positional)[0].children.map(edge => edge.role)).toEqual(['type']);
    expect(positional.nodes.some(node => node.kind === 'lit')).toBe(false);
  });
});

for (const [label, variable] of [
  ['native occurrence', 'DEFINOGRAPH_SOURCE_OCCURRENCE_FIXTURES'],
  ['independent occurrence challenge', 'DEFINOGRAPH_POSITIONAL_THEORY_FIXTURES'],
] as const) describe.runIf(!!process.env[variable])(`${label} positional readback`, () => {
  it('draws every available selected candidate without changing any source/root/selected outcome', () => {
    const captures = JSON.parse(readFileSync(process.env[variable]!, 'utf8'));
    expect(captures.length).toBeGreaterThan(0);
    let drawn = 0, retainedFailure = 0;
    for (const item of captures) {
      const response = item.response ?? item, before = exact(response);
      const snapshot = validateSourceSnapshot(response.sourceSnapshot ?? response.snapshot);
      const occurrence = validateSourceOccurrence(response.sourceOccurrence ?? response.occurrence, snapshot);
      if (occurrence.checking.status === 'captured' && occurrence.checking.selected) {
        const selected = occurrence.checking.selected;
        const drawing = build(selected, `${occurrence.captureId}:${JSON.stringify(occurrence.path)}`, ['checking', 'selected']);
        checkScopes(selected, drawing); drawn++;
        if (occurrence.checking.checks.some(check => check.outcome.tag !== 'accepted')) retainedFailure++;
      }
      expect(exact(response)).toBe(before);
    }
    expect(drawn).toBeGreaterThan(0);
    expect(retainedFailure).toBeGreaterThan(0);
  });
});
