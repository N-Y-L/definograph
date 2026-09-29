import { describe, expect, it } from 'vitest';
import type { JsonValue } from '../packets/packet';
import { replayDefinitionHead, type HeadExposureDefinition } from './head-exposure-replay';
const name = (s: string): JsonValue => ['str', ['anonymous'], s];
const c = (s: string, levels: JsonValue[] = []): JsonValue => ['const', name(s), levels];
const n = (v: number | string): JsonValue => ['nat', String(v)];
const b = (i: number): JsonValue => ['bvar', n(i)];
const app = (fn: JsonValue, ...args: JsonValue[]): JsonValue => args.reduce<JsonValue>((f, a) => ['app', f, a], fn);
const lam = (body: JsonValue, type = c('Nat')): JsonValue => ['lam', name('same'), type, body, 'default'];
const lit = (v: number | string): JsonValue => ['lit', ['natVal', n(v)]];
const definition = (value: JsonValue, levelParams: JsonValue[] = []): HeadExposureDefinition => ({ name: name('Unfamiliar'), levelParams, type: c('Nat'), value, hints: ['abbrev'], safety: 'safe' });
const run = (body: JsonValue, args: JsonValue[] = [], arity = 0) => replayDefinitionHead(app(c('Unfamiliar'), ...args), definition(body), arity);

describe('independent original-lambda-spine exposure replay', () => {
  it('consumes ordered original arguments and preserves unfamiliar composition topology', () => {
    const value = lam(lam(lam(app(b(1), app(b(2), b(0))))));
    const result = run(value, [c('f'), c('g'), c('x')]);
    expect(result.term).toEqual(app(c('g'), app(c('f'), c('x'))));
    expect(result.arguments).toEqual([c('f'), c('g'), c('x')]); expect(result.betaApplications).toBe(3);
  });
  it('lifts ambient actuals under remaining owned binders and preserves dependent domains', () => {
    expect(run(lam(lam(b(1))), [b(0)], 1).term).toEqual(lam(b(1)));
    const dependent = lam(lam(b(0), b(0)), ['sort', ['succ', ['zero']]]);
    expect(run(dependent, [b(0)], 1).term).toEqual(lam(b(0), b(0)));
    const argument = lam(app(b(1), b(0)));
    expect(run(lam(lam(b(1))), [argument], 1).term).toEqual(lam(lam(app(b(2), b(0)))));
  });
  it('leaves a newly created head redex and additional definition calls folded', () => {
    const identity = lam(b(0));
    const out = run(identity, [identity, lit(3)]);
    expect(out.term).toEqual(app(identity, lit(3))); expect(out.betaApplications).toBe(1);
    expect(run(c('SecondDefinition'), [lit(3)]).term).toEqual(app(c('SecondDefinition'), lit(3)));
    expect(run(lam(app(c('Unfamiliar'), b(0))), [lit(3)]).term).toEqual(app(c('Unfamiliar'), lit(3)));
  });
  it.each([false, true])('does not cross or normalize a source let boundary, nondep=%s', nondep => {
    const value: JsonValue = ['letE', name('z'), c('Nat'), lit(2), lam(b(0)), nondep];
    expect(run(value, [lit(3)]).term).toEqual(app(value, lit(3)));
    expect(run(lam(value), [lit(4)]).term).toEqual(value);
    const projection: JsonValue = ['proj', name('Pair'), n('9007199254740993'), c('pair')];
    expect(run(projection).term).toEqual(projection);
  });
  it('substitutes universes simultaneously without simplifying max/imax or replacing inserted levels', () => {
    const u = name('u'), v = name('v'), pu: JsonValue = ['param', u], pv: JsonValue = ['param', v];
    const body: JsonValue = ['sort', ['max', pu, ['imax', pv, pu]]];
    const result = replayDefinitionHead(c('Unfamiliar', [pv, ['zero']]), definition(body, [u, v]), 0);
    expect(result.term).toEqual(['sort', ['max', pv, ['imax', ['zero'], pv]]]);
    expect(result.actualLevels).toEqual([pv, ['zero']]);
  });
  it('distinguishes exact structured universe names and adjacent large natural payloads', () => {
    const numericName: JsonValue = ['num', name('u'), n('9007199254740993')];
    const body: JsonValue = ['const', ['num', name('large'), n('9007199254740992')], [['param', numericName]]];
    const out = replayDefinitionHead(c('Unfamiliar', [['zero']]), definition(body, [numericName]), 0);
    expect(out.term).toEqual(['const', ['num', name('large'), n('9007199254740992')], [['zero']]]);
    expect(run(lit('9007199254740993')).term).toEqual(lit('9007199254740993'));
  });
  it.each(['abbrev', 'opaque', 'regular'])('accepts exact safe defnInfo hints %s without treating them as attributes', tag => {
    const d = definition(lit(1)); d.hints = tag === 'regular' ? [tag, 0xffffffff] : [tag];
    expect(replayDefinitionHead(c('Unfamiliar'), d, 0).term).toEqual(lit(1));
  });
  it.each(['head', 'name', 'unsafe', 'arity', 'parameter', 'duplicate', 'bvar', 'fvar', 'mvar', 'metadata', 'sorry', 'hint', 'natural'])('refuses malformed or unsupported %s traces', mutation => {
    const d = definition(lit(1)); let before = c('Unfamiliar');
    switch (mutation) {
      case 'head': before = b(0); break;
      case 'name': d.name = name('Other'); break;
      case 'unsafe': (d as { safety: string }).safety = 'unsafe'; break;
      case 'arity': d.levelParams = [name('u')]; break;
      case 'parameter': d.value = ['sort', ['param', name('missing')]]; break;
      case 'duplicate': d.levelParams = [name('u'), name('u')]; break;
      case 'bvar': d.value = b(0); break;
      case 'fvar': d.value = ['fvar', name('x')]; break;
      case 'mvar': d.value = ['sort', ['mvar', name('u')]]; break;
      case 'metadata': d.value = ['mdata', ['mdataEntries', []], lit(1)]; break;
      case 'sorry': d.value = c('sorryAx'); break;
      case 'hint': d.hints = ['regular', n(3)]; break;
      case 'natural': d.value = ['lit', ['natVal', n('01')]]; break;
    }
    expect(() => replayDefinitionHead(before, d, 1)).toThrow();
  });
  it('charges Expr-plus-Level depth, repeated UTF-8 text and expanded output before unbounded duplication', () => {
    let level: JsonValue = ['zero']; for (let i = 0; i < 95; i++) level = ['succ', level];
    expect(run(['sort', level]).term).toEqual(['sort', level]);
    expect(() => run(['sort', ['succ', level]])).toThrow(/depth/);
    expect(() => run(['lit', ['strVal', 'é'.repeat(65_537)]])).toThrow(/text/);
    let body = b(0); for (let i = 0; i < 12; i++) body = app(body, body);
    let actual = lit(0); for (let i = 0; i < 4; i++) actual = app(actual, actual);
    expect(() => run(lam(body), [actual])).toThrow(/node/);
    let oversized = b(0); for (let i = 0; i < 14; i++) oversized = app(oversized, oversized);
    expect(() => run(lam(oversized))).toThrow(/node/);
  });
  it('refuses hostile JS data without invoking source getters', () => {
    let called = false; const d = definition(lit(1));
    Object.defineProperty(d, 'value', { enumerable: true, get() { called = true; return lit(2); } });
    expect(() => replayDefinitionHead(c('Unfamiliar'), d, 0)).toThrow(/data/); expect(called).toBe(false);
  });
  it('charges inserted universe depth and repeated parameter payloads before returning a substituted body', () => {
    const u = name('u'); let parameter: JsonValue = ['param', u], actual: JsonValue = ['zero'];
    for (let i = 0; i < 90; i++) parameter = ['succ', parameter];
    for (let i = 0; i < 10; i++) actual = ['succ', actual];
    expect(() => replayDefinitionHead(c('Unfamiliar', [actual]), definition(['sort', parameter], [u]), 0)).toThrow(/depth/);
    let repeated: JsonValue = ['param', u]; for (let i = 0; i < 7; i++) repeated = ['max', repeated, repeated];
    const make = (length: number) => replayDefinitionHead(c('Unfamiliar', [['param', name('x'.repeat(length))]]), definition(['sort', repeated], [u]), 0);
    expect((make(1024).term as JsonValue[])[0]).toBe('sort');
    expect(() => make(1025)).toThrow(/text/);
  });
});
