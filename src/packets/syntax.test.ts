import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import type { JsonObject, JsonValue, PacketEnvelope, RecordPayload } from './packet';
import { formatExpr, levelText, nameText, PacketSyntax, PacketSyntaxError, validateExpr } from './syntax';
import { MAX_NATURAL_DIGITS } from './natural';

function name(...parts: (string | number)[]): JsonValue {
  return parts.reduce<JsonValue>((parent, part) => [typeof part === 'number' ? 'num' : 'str', parent, part], ['anonymous']);
}
function actuals(...items: JsonValue[]): JsonValue {
  return items.reduceRight<JsonValue>((tail, item) => ['cons', item, tail], ['nil']);
}
function use(offset: number, ...items: JsonValue[]): JsonValue { return ['use', offset, items.length, actuals(...items)]; }
function table(...rows: [number, JsonValue][]): JsonObject {
  return { homes: rows.map(([home]) => home).reverse(), rows: rows.map(([home, row]) => ({ home, row })) };
}
function attrs(label: string, info = 'default'): JsonObject { return { name: name(label), info }; }
const NAT: JsonValue = ['const', name('Nat'), []];
const ZERO: JsonValue = ['lit', ['natVal', 0]];

describe('exact raw expression validation and display', () => {
  it('distinguishes numeric, quoted, dotted, Unicode and anonymous Name components', () => {
    const names = [name('x', 1), name('x', '1'), name('x.1'), name('x', '#1'), name('x', '«1»'), name('x', '\\u00ab1»')];
    expect(new Set(names.map(nameText)).size).toBe(names.length);
    expect(names.slice(0, 3).map(nameText)).toEqual(['x.#1', 'x.«1»', '«x.1»']);
    expect(nameText(name('μB'))).toBe('μB');
    expect(nameText(name('forall'))).toBe('«forall»');
    expect(nameText(name('Sort'))).toBe('«Sort»');
    expect(nameText(['anonymous'])).not.toBe(nameText(name('<anonymous>')));
  });
  it('preserves universe order and variable constructor kinds', () => {
    const level: JsonValue = ['imax', ['param', name('u')], ['max', ['zero'], ['succ', ['zero']]]];
    expect(levelText(level)).toBe('imax(param(u), max(0, succ(0)))');
    expect(levelText(['param', name('u')])).not.toBe(levelText(['mvar', name('u')]));
    expect(formatExpr(['const', name('Eq'), [['succ', ['zero']], level]])).toBe('Eq.{succ(0), imax(param(u), max(0, succ(0)))}');
  });
  it('distinguishes duplicate binder identities and globals with the same spelling', () => {
    const expression: JsonValue = ['lam', name('x'), NAT,
      ['lam', name('x'), ['const', name('x'), []], ['app', ['bvar', 1], ['bvar', 0]], 'default'], 'default'];
    expect(formatExpr(expression)).toBe('(fun (x : Nat) => (fun (x@2 : global(x)) => (x x@2)))');
    expect(formatExpr(['lam', name('x'), NAT, ['const', name('x'), []], 'default'])).toBe('(fun (x : Nat) => global(x))');
    expect(formatExpr(['lam', name('x'), NAT, ['bvar', 0], 'default'])).toBe('(fun (x : Nat) => x)');
    expect(formatExpr(['const', name('x'), [['zero']]], ['x'])).toBe('global(x.{0})');
    expect(formatExpr(['bvar', 1], ['inner', 'outer'])).toBe('outer');
    expect(formatExpr(['fvar', name('x')], ['x'])).toBe('fvar(x)');
    expect(formatExpr(['mvar', name('x')], ['x'])).toBe('mvar(x)');
  });
  it('preserves all binder annotations and genuine let flags', () => {
    for (const [info, binder] of [['default', '(x : Nat)'], ['implicit', '{x : Nat}'],
      ['strictImplicit', '⦃x : Nat⦄'], ['instImplicit', '[x : Nat]']]) {
      expect(formatExpr(['forallE', name('x'), NAT, ['bvar', 0], info])).toBe('(∀ ' + binder + ', x)');
    }
    for (const nondep of [false, true]) {
      expect(formatExpr(['letE', name('x'), NAT, ['lit', ['natVal', 7]], ['bvar', 0], nondep]))
        .toBe('(let[nondep=' + nondep + '] x : Nat := 7; x)');
    }
  });
  it('retains projections, strings, and literal constructor distinctions', () => {
    expect(formatExpr(['lit', ['strVal', '<tag> "quoted"']])).toBe(JSON.stringify('<tag> "quoted"'));
    expect(formatExpr(['proj', name('Pair'), 1, ['fvar', name('x')]])).toBe('proj[Pair#1](fvar(x))');
    expect(formatExpr(['sort', ['zero']])).not.toBe(formatExpr(['app', ['const', name('Sort'), []], ZERO]));
  });
  it('does not modify exact raw constructors during validation or formatting', () => {
    const expression: JsonValue = ['letE', name('x', 3), ['sort', ['succ', ['zero']]], NAT,
      ['forallE', name('x', '3'), ['bvar', 0], ['proj', name('Pair'), 1, ['bvar', 1]], 'strictImplicit'], true];
    const before = JSON.stringify(expression);
    validateExpr(expression); formatExpr(expression);
    expect(JSON.stringify(expression)).toBe(before);
  });
  it('never truncates deep expressions into a common semantic value', () => {
    let left: JsonValue = ['const', name('left'), []], right: JsonValue = ['const', name('right'), []];
    for (let index = 0; index < 70; index++) { left = ['app', NAT, left]; right = ['app', NAT, right]; }
    const a = formatExpr(left), b = formatExpr(right);
    expect(a).not.toBe(b); expect(a).not.toContain('…'); expect(a).toContain('left'); expect(b).toContain('right');
  });
});

describe('contextual DAG decoding', () => {
  it('uses each row storage prefix, preserving application structure and later rows', () => {
    const reader = new PacketSyntax(table([0, NAT], [0, ['const', name('zero'), []]],
      [0, ['app', use(1), use(0)]], [0, ['const', name('later'), []]]));
    expect(reader.occ(use(1), 0)).toEqual(['app', NAT, ['const', name('zero'), []]]);
    expect(formatExpr(reader.occ(use(0), 0))).toBe('later');
  });
  it('shifts ambient actuals under a new binder, avoiding capture', () => {
    const reader = new PacketSyntax(table([1, ['lam', attrs('x'), ['var', 0], ['var', 1]]]));
    const result = reader.occ(use(0, ['var', 0]), 1);
    expect(result).toEqual(['lam', name('x'), ['bvar', 0], ['bvar', 1], 'default']);
    expect(formatExpr(result, ['x'])).toBe('(fun (x@2 : x) => x)');
  });
  it('substitutes a home vector simultaneously rather than cascading replacements', () => {
    const reader = new PacketSyntax(table([2, ['app', ['var', 0], ['var', 1]]]));
    expect(reader.occ(use(0, ['var', 1], ['var', 0]), 2)).toEqual(['app', ['bvar', 1], ['bvar', 0]]);
  });
  it('instantiates its own explicit actuals within the enclosing occurrence', () => {
    const reader = new PacketSyntax(table([0, NAT], [1, ['lam', attrs('x'), use(0), ['var', 1]]],
      [0, ['const', name('a'), []]], [0, ['inst', 1, use(1, ['var', 0]), actuals(use(0))]]));
    expect(reader.occ(use(0), 0)).toEqual(['lam', name('x'), NAT, ['const', name('a'), []], 'default']);
  });
  it('allows nested actuals to refer to rows newer than the callee', () => {
    const constant: JsonValue = ['const', name('f'), [['succ', ['zero']]]];
    const reader = new PacketSyntax(table([1, ['var', 0]], [0, constant]));
    expect(reader.occ(use(1, use(0)), 0)).toEqual(constant);
    expect(reader.args(actuals(use(1, use(0)), use(0)), 0)).toEqual([constant, constant]);
  });
  it('keeps an inserted actual’s local binders unchanged', () => {
    const reader = new PacketSyntax(table([0, NAT], [1, ['lam', attrs('x'), use(0), ['var', 1]]],
      [0, ['lam', attrs('x'), use(1), ['var', 0]]]));
    expect(reader.occ(use(1, use(0)), 0)).toEqual(['lam', name('x'), NAT,
      ['lam', name('x'), NAT, ['bvar', 0], 'default'], 'default']);
  });
  it('preserves let types, values, body scope, and both nondep flags under substitution', () => {
    for (const nondep of [false, true]) {
      const reader = new PacketSyntax(table([1, ['letE', name('x'), nondep, ['var', 0], ['var', 0], ['var', 1]]]));
      const expr = reader.occ(use(0, ['var', 0]), 1);
      expect(expr).toEqual(['letE', name('x'), ['bvar', 0], ['bvar', 0], ['bvar', 1], nondep]);
      expect(formatExpr(expr, ['x'])).toBe('(let[nondep=' + nondep + '] x@2 : x := x; x)');
    }
  });
  it('preserves pi annotations and exact projection metadata', () => {
    const reader = new PacketSyntax(table([0, NAT],
      [1, ['proj', name('Record', 7), 2, ['var', 0]]],
      [0, ['pi', attrs('x', 'strictImplicit'), use(1), use(0, ['var', 0])]]));
    expect(reader.occ(use(0), 0)).toEqual(['forallE', name('x'), NAT,
      ['proj', name('Record', 7), 2, ['bvar', 0]], 'strictImplicit']);
  });
  it('retains separate constructors and values even when repeated rows resolve equally', () => {
    const reader = new PacketSyntax(table([0, NAT], [0, NAT],
      [0, ['const', name('Nat'), [['zero']]]], [0, ['const', name('Nat'), [['succ', ['zero']]]]],
      [0, ['lit', ['natVal', 1]]], [0, ['lit', ['natVal', 2]]]));
    expect(reader.occ(use(5), 0)).toEqual(reader.occ(use(4), 0));
    expect(reader.occ(use(3), 0)).not.toEqual(reader.occ(use(2), 0));
    expect(reader.occ(use(1), 0)).not.toEqual(reader.occ(use(0), 0));
    expect(reader.occ(use(5), 0)).not.toBe(reader.occ(use(4), 0));
  });
  it('copies source tables and every public result, including nested names and duplicate actuals', () => {
    const input = table([0, ['const', name('Nat'), []]]);
    const reader = new PacketSyntax(input);
    ((input.rows as JsonObject[])[0].row as JsonValue[])[1] = name('changed');
    const first = reader.occ(use(0), 0) as JsonValue[];
    (first[1] as JsonValue[])[2] = 'mutated';
    expect(reader.occ(use(0), 0)).toEqual(NAT);
    const duplicate = reader.args(actuals(use(0), use(0)), 0) as JsonValue[][];
    (duplicate[0][1] as JsonValue[])[2] = 'again';
    expect(duplicate[1]).toEqual(NAT); expect(reader.occ(use(0), 0)).toEqual(NAT);
  });
});

describe('owner context', () => {
  it('returns chronological, scoped declarations and retains let values', () => {
    const reader = new PacketSyntax(table([0, NAT], [0, ZERO]));
    const first: JsonValue = ['port', ['nil'], attrs('x', 'implicit'), use(1)];
    const second: JsonValue = ['port', first, attrs('x'), ['var', 0]];
    const owner: JsonValue = ['letE', second, name('x'), false, use(1), ['var', 1]];
    const rows = reader.owner(owner);
    expect(rows).toEqual([{ name: name('x'), info: 'implicit', type: NAT },
      { name: name('x'), info: 'default', type: ['bvar', 0] },
      { name: name('x'), info: 'default', type: NAT, value: ['bvar', 1], nondep: false }]);
    expect(rows[0]).not.toHaveProperty('value');
    (rows[0].name as JsonValue[])[2] = 'changed';
    expect(reader.owner(owner)[0].name).toEqual(name('x'));
  });
  it('never makes the current owner binder available in its own type or value', () => {
    const reader = new PacketSyntax(table([0, NAT]));
    expect(() => reader.owner(['port', ['nil'], attrs('x'), ['var', 0]])).toThrow(PacketSyntaxError);
    expect(() => reader.owner(['letE', ['nil'], name('x'), true, use(0), ['var', 0]])).toThrow(PacketSyntaxError);
  });
});

describe('explicit syntax boundaries', () => {
  it('rejects malformed offsets, homes, vectors and scope arities', () => {
    const reader = new PacketSyntax(table([0, NAT]));
    for (const value of [use(1), ['use', 0, 1, actuals(['var', 0])], ['var', 0],
      ['use', true, 0, ['nil']], ['use', 0, 0, actuals(use(0))], ['use', -1, 0, ['nil']],
      ['use', 0, 0, ['nil', 1]], ['use', 0, 0], ['unknown']]) {
      expect(() => reader.occ(value as JsonValue, 0)).toThrow(PacketSyntaxError);
    }
    expect(() => reader.occ(use(0), -1)).toThrow(PacketSyntaxError);
    expect(() => reader.occ(use(0), 0.5)).toThrow(PacketSyntaxError);
    expect(() => reader.args(['cons', use(0)], 0)).toThrow(PacketSyntaxError);
    expect(() => new PacketSyntax({ homes: [1], rows: [{ home: 0, row: NAT }] })).toThrow(PacketSyntaxError);
    expect(() => new PacketSyntax({ homes: [0], rows: [{ home: 0, row: NAT, extra: null }] })).toThrow(PacketSyntaxError);
    expect(() => new PacketSyntax(table([0, ['app', use(0), use(0)]])).occ(use(0), 0)).toThrow(/earlier table prefix/);
  });
  it('rejects unsupported rows and raw constructors without inventing a replacement', () => {
    const reader = new PacketSyntax(table([0, ['unique', {}, NAT, NAT, NAT, NAT, NAT]], [0, NAT]));
    expect(reader.occ(use(0), 0)).toEqual(NAT);
    expect(() => reader.occ(use(1), 0)).toThrow(/unsupported contextual expression constructor: unique/);
    for (const value of [[{}], ['mdata', {}, NAT], ['unknown'], ['bvar', 0], ['letE', name('x'), NAT, ZERO, ['bvar', 0], 0],
      ['lam', name('x'), NAT, ['bvar', 0], 'unknown'], ['const', name('x'), [['bogus']]],
      ['sort', ['zero', 0]], ['lit', ['natVal', 1.5]], ['lit', ['natVal', Number.MAX_SAFE_INTEGER + 1]],
      ['fvar', ['str', ['anonymous'], 12]]]) {
      expect(() => validateExpr(value as JsonValue)).toThrow(PacketSyntaxError);
      expect(() => formatExpr(value as JsonValue)).toThrow(PacketSyntaxError);
    }
    expect(() => formatExpr(NAT, ['x', 'x'])).toThrow(PacketSyntaxError);
    expect(() => new PacketSyntax(table([0, [{}]])).occ(use(0), 0)).toThrow(PacketSyntaxError);
  });
  it('fails at explicit resource limits and recovers for a later operation', () => {
    let expression: JsonValue = NAT;
    for (let index = 0; index < 300; index++) expression = ['app', NAT, expression];
    expect(() => formatExpr(expression)).toThrow(/node or depth limit/);
    expect(() => nameText(name('x'.repeat(2_000_001)))).toThrow(/text limit/);
    const reader = new PacketSyntax(table([0, NAT]));
    const cycle: JsonValue[] = ['port', null, attrs('x'), use(0)]; cycle[1] = cycle;
    expect(() => reader.owner(cycle)).toThrow(/node or depth limit/);
    expect(reader.occ(use(0), 0)).toEqual(NAT);
    const cyclicTable = table([0, NAT]); cyclicTable.extra = cyclicTable;
    expect(() => new PacketSyntax(cyclicTable)).toThrow(PacketSyntaxError);
  });
  it('bounds the aggregate output size when a DAG duplicates a large literal', () => {
    const reader = new PacketSyntax(table([0, NAT], [0, ['lit', ['strVal', 'x'.repeat(1_100_000)]]],
      [0, ['app', use(0), use(0)]]));
    expect(() => reader.occ(use(0), 0)).toThrow(/text limit/);
    expect(() => reader.args(actuals(use(1), use(1)), 0)).toThrow(/text limit/);
    expect(reader.occ(use(2), 0)).toEqual(NAT);
  });
});

describe('version 2 exact semantic naturals', () => {
  const big = '9007199254740992', adjacent = '9007199254740993';
  const exact = (digits: string): JsonValue => ['nat', digits];
  const numericName = (digits: string): JsonValue => ['num', name('component'), exact(digits)];

  it('formats adjacent large numeric names, string names, levels and literals distinctly', () => {
    const names = [numericName(big), numericName(adjacent), name('component', big)];
    expect(new Set(names.map(nameText)).size).toBe(3);
    expect(names.map(nameText)).toEqual([`component.#${big}`, `component.#${adjacent}`, `component.«${big}»`]);
    const level: JsonValue = ['imax', ['param', numericName(big)], ['max', ['zero'], ['succ', ['zero']]]];
    expect(levelText(level)).toContain(big);
    const expression: JsonValue = ['proj', numericName(adjacent), exact(big),
      ['app', ['const', numericName(big), [level]], ['lit', ['natVal', exact(adjacent)]]]];
    validateExpr(expression, 0, 2);
    expect(formatExpr(expression, [], 2)).toContain(`proj[component.#${adjacent}#${big}]`);
    expect(formatExpr(expression, [], 2)).toContain(adjacent);
    expect(() => validateExpr(expression)).toThrow(PacketSyntaxError);
  });

  it('tags decoded DAG variables and preserves capture-avoiding simultaneous substitution', () => {
    const reader = new PacketSyntax(table([2, ['lam', { name: numericName(big), info: 'implicit' },
      ['var', 0], ['var', 2]]]), 2);
    const decoded = reader.occ(use(0, ['var', 1], ['var', 0]), 2);
    expect(decoded).toEqual(['lam', numericName(big), ['bvar', exact('1')], ['bvar', exact('1')], 'implicit']);
    validateExpr(decoded, 2, 2);
    expect(formatExpr(decoded, ['newest', 'oldest'], 2)).toBe(`(fun {component.#${big} : oldest} => newest)`);
    const swap = new PacketSyntax(table([2, ['app', ['var', 0], ['var', 1]]]), 2);
    expect(swap.occ(use(0, ['var', 1], ['var', 0]), 2)).toEqual(['app', ['bvar', exact('1')], ['bvar', exact('0')]]);
  });

  it('preserves tagged pi/projection fields and genuine owner and nested let definitions', () => {
    const literal: JsonValue = ['lit', ['natVal', exact(big)]];
    const reader = new PacketSyntax(table([0, NAT], [0, literal],
      [1, ['letE', numericName(big), true, use(1), use(0), ['var', 1]]],
      [1, ['proj', numericName(adjacent), exact(big), ['var', 0]]],
      [0, ['pi', { name: numericName(big), info: 'strictImplicit' }, use(3), use(0, ['var', 0])]]), 2);
    expect(reader.occ(use(0), 0)).toEqual(['forallE', numericName(big), NAT,
      ['proj', numericName(adjacent), exact(big), ['bvar', exact('0')]], 'strictImplicit']);
    expect(reader.occ(use(2, ['var', 0]), 1)).toEqual(['letE', numericName(big), NAT, literal, ['bvar', exact('1')], true]);
    const owner: JsonValue = ['letE', ['port', ['nil'], { name: numericName(big), info: 'default' }, use(4)],
      numericName(adjacent), false, use(4), ['var', 0]];
    expect(reader.owner(owner)).toEqual([
      { name: numericName(big), info: 'default', type: NAT },
      { name: numericName(adjacent), info: 'default', type: NAT, value: ['bvar', exact('0')], nondep: false },
    ]);
  });

  it('keeps tagged results isolated from the table, cache and other returned arguments', () => {
    const input = table([0, ['lit', ['natVal', exact(big)]]]);
    const reader = new PacketSyntax(input, 2);
    const result = reader.args(actuals(use(0), use(0)), 0) as JsonValue[][];
    (((result[0][1] as JsonValue[])[1]) as JsonValue[])[1] = adjacent;
    expect(result[1]).toEqual(['lit', ['natVal', exact(big)]]);
    expect(reader.occ(use(0), 0)).toEqual(['lit', ['natVal', exact(big)]]);
  });

  it('rejects mixed semantic encodings and tagged operational indices', () => {
    for (const raw of [
      ['lit', ['natVal', 0]], ['const', ['num', name('x'), 0], []],
      ['sort', ['param', ['num', name('u'), 0]]], ['proj', name('Pair'), 0, NAT], ['bvar', 0],
    ] as JsonValue[]) {
      expect(() => validateExpr(raw, 1, 2)).toThrow(PacketSyntaxError);
      expect(() => formatExpr(raw, ['x'], 2)).toThrow(PacketSyntaxError);
    }
    for (const raw of [['lit', ['natVal', exact('0')]], ['bvar', exact('0')]] as JsonValue[])
      expect(() => validateExpr(raw, 1, 1)).toThrow(PacketSyntaxError);
    const reader = new PacketSyntax(table([0, NAT]), 2);
    for (const occurrence of [['var', exact('0')], ['use', exact('0'), 0, ['nil']], ['use', 0, exact('0'), ['nil']]] as JsonValue[])
      expect(() => reader.occ(occurrence, 1)).toThrow(PacketSyntaxError);
    expect(() => new PacketSyntax(table([0, ['lit', ['natVal', 0]]]), 2).occ(use(0), 0)).toThrow(PacketSyntaxError);
  });

  it('bounds tagged references before indexing and enforces decimal and profile limits', () => {
    expect(() => validateExpr(['bvar', exact(adjacent)], 2, 2)).toThrow(PacketSyntaxError);
    expect(() => formatExpr(['bvar', exact(big)], ['x'], 2)).toThrow(PacketSyntaxError);
    const limit = '9'.repeat(MAX_NATURAL_DIGITS);
    expect(formatExpr(['lit', ['natVal', exact(limit)]], [], 2)).toBe(limit);
    expect(() => validateExpr(['lit', ['natVal', exact(limit + '9')]], 0, 2)).toThrow(/digit/);
    for (const digits of ['00', '01', '-1', '+1', '1e3', ' 1', '١'])
      expect(() => validateExpr(['lit', ['natVal', exact(digits)]], 0, 2)).toThrow(PacketSyntaxError);
    expect(() => validateExpr(NAT, 0, 3 as 2)).toThrow(/profile/);
    expect(() => new PacketSyntax(table([0, NAT]), 3 as 2)).toThrow(/profile/);
  });
});

// Primary producer packets are supplied by the local acceptance run. They are not
// distributed fixtures, and the portable suite must not depend on a private path.
const fixtureRoot = process.env.DEFINOGRAPH_PACKET_FIXTURES;
const modes = ['certified-route-universe', 'let-context', 'missing', 'incoherent', 'refused', 'timeout'];
function fixture(mode: string): PacketEnvelope {
  return JSON.parse(readFileSync(join(fixtureRoot!, 'worker-packets', mode + '.packet.json'), 'utf8')) as PacketEnvelope;
}
function records(packet: PacketEnvelope): RecordPayload[] {
  return packet.payload.results.flatMap(result => [result.records.retained, result.records.derived])
    .filter((record): record is RecordPayload => record !== null);
}
describe.skipIf(!fixtureRoot)('retained real producer packets', () => {
  it.each(modes)('decodes every contextual table row and captured declaration in %s', mode => {
    const packet = fixture(mode);
    for (const record of records(packet)) {
      const syntax = new PacketSyntax(record.table);
      const owner = syntax.owner(record.owner);
      expect(owner).toHaveLength(record.n as number);
      validateExpr(syntax.occ(record.nodeTy, owner.length), owner.length);
      validateExpr(syntax.occ(record.sup, owner.length), owner.length);
      const rows = (record.table as JsonObject).rows as JsonObject[];
      rows.forEach((row, index) => {
        const arity = row.home as number;
        const identity = Array.from({ length: arity }, (_, slot) => ['var', slot] as JsonValue);
        const decoded = syntax.occ(use(rows.length - 1 - index, ...identity), arity);
        validateExpr(decoded, arity);
      });
      for (const member of record.uses) {
        const entry = member.entry;
        const selected = entry.use as JsonObject;
        const arity = owner.length + (entry.e as number);
        validateExpr(syntax.occ(selected.src, arity), arity);
        validateExpr(syntax.occ(selected.view, arity), arity);
        for (const actual of syntax.args(selected.acts, arity)) validateExpr(actual, arity);
      }
    }
    for (const check of packet.payload.checks) {
      validateExpr(check.declaration.type);
      if (check.declaration.value !== null) validateExpr(check.declaration.value);
    }
  });
  it('retains the owner seed as a genuine definition even when unused', () => {
    for (const record of records(fixture('let-context'))) {
      const owner = new PacketSyntax(record.table).owner(record.owner);
      expect(owner).toEqual([{ name: name('seed'), info: 'default', type: NAT, value: ZERO, nondep: false }]);
    }
  });
  it('preserves chosen and source occurrences and explicit nested certificate actuals', () => {
    const record = fixture('certified-route-universe').payload.results[0].records.retained!;
    const syntax = new PacketSyntax(record.table);
    const member = record.uses[0], selected = member.entry.use as JsonObject;
    const arity = (record.n as number) + (member.entry.e as number);
    expect(syntax.occ(selected.src, arity)).toEqual(['const', name('DefinographFixtures', 'addAlias'), []]);
    expect(syntax.occ(selected.view, arity)).toEqual(['const', name('DefinographFixtures', 'addOp'), []]);
    expect(member.sourceLevels).toEqual({ tag: 'available', values: [['succ', ['zero']]] });
    expect(member.viewLevels).toEqual({ tag: 'notApplicable' });
    const certificate = selected.srcCert as JsonValue[];
    expect(certificate[0]).toBe('classB'); expect(certificate[1]).toEqual(name('DefinographFixtures', 'genericRefl'));
    const certArgs = syntax.args(certificate[3], arity);
    expect(certArgs).toEqual([['const', name('DefinographFixtures', 'Operation'), []], ['const', name('DefinographFixtures', 'addOp'), []]]);
  });
});
