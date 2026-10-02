import { describe, expect, it } from 'vitest';
import type { JsonValue } from '../packets/packet';
import { positionalResultPath } from './source-decomposition-reading';
import { validateSourceHeadExposure } from './source-head-exposure';
import { validateDecompositionHistory, type DecompositionHistory } from './source-decomposition';
import { headExposureFixture } from './source-decomposition.test-fixtures';
import { o, a, name, c, n, b, app, clone, close, firstFocus, append, checking, replaceDeclaration, errorStop } from './source-decomposition-chain.test-fixtures';
import { definitionOccurrences, definitionOccurrenceFocus, scopedExpressionLabel, type DefinitionOccurrenceSource } from './definition-occurrences';

const nat = c('Nat');
const lit = (value: number): JsonValue => ['lit', ['natVal', n(value)]];
const lam = (label: string, type: JsonValue, body: JsonValue): JsonValue => ['lam', name(label), type, body, 'default'];
/** Synthetic parser fixtures only. They establish no Lean typing verdict. The
 * test expectations below are independent paths, argument order and homes. */
function sourceFor(term: JsonValue): DefinitionOccurrenceSource {
  const fixture = headExposureFixture(), value = fixture.value;
  const exposure = o(checking(value).exposure), result = o(exposure.result);
  result.term = term;
  o(exposure.definition).value = lam('f', ['forallE', name('x'), nat, nat, 'default'], lam('x', nat, term));
  const telescope = o(result.home).telescope;
  replaceDeclaration(value, 7, d => { d.value = close(telescope, term, 'lam'); });
  replaceDeclaration(value, 8, d => { d.type = close(telescope, app(c('Eq', [exposure.carrierSort]), result.type, exposure.before, term), 'forallE'); });
  const seed = validateSourceHeadExposure(value, fixture.snapshot, fixture.parent);
  const base = validateDecompositionHistory({ ...fixture.parent, seed: { snapshot: fixture.snapshot, record: seed }, attempts: [] });
  const history = append(base, firstFocus(base, 'empty'));
  return { history, record: history.attempts[0].record, stepIndex: 0 };
}
function available(source: DefinitionOccurrenceSource, limits?: Parameters<typeof definitionOccurrences>[1]) {
  const result = definitionOccurrences(source, limits);
  expect(result.status).toBe('available');
  if (result.status !== 'available') throw Error(result.reason);
  return result;
}
function find(source: DefinitionOccurrenceSource, head: string) {
  return available(source).occurrences.filter(value => value.headName === head);
}

describe('exact application occurrence choices', () => {
  it('keeps repeated unfamiliar heads separate and selects maximal application spines', () => {
    const first = app(c('Unfamiliar'), lit(0), lit(1)), second = app(c('Unfamiliar'), lit(2));
    const source = sourceFor(app(c('Combine'), first, second)), model = available(source);
    expect(model.totalCount).toBe(3);
    expect(model.occurrences.map(item => item.headName)).toEqual(['Combine', 'Unfamiliar', 'Unfamiliar']);
    const [left, right] = model.occurrences.slice(1);
    expect(left.focusPath).toEqual(['appFun', 'appArg']); expect(left.term).toEqual(first);
    expect(right.focusPath).toEqual(['appArg']); expect(right.term).toEqual(second);
    expect(left.id).not.toBe(right.id);
    expect(left.label).toBe('(Unfamiliar 0 1)'); expect(right.label).toBe('(Unfamiliar 2)');
    expect(left.sourcePath).toEqual(['checking', 'steps', 0, 'output', 'result', 'term', 1, 2]);
    expect(definitionOccurrenceFocus(source, left)).toEqual({ kind: 'focus', path: ['appFun', 'appArg'] });
  });
  it('preserves distinct binder homes despite identical head and local spelling', () => {
    const term = lam('same', nat, app(c('Combine'), app(c('Unfamiliar'), b(0)), lam('same', nat, app(c('Unfamiliar'), b(0)))));
    const source = sourceFor(term), [outer, inner] = find(source, 'Unfamiliar');
    expect(outer.home.arity).toBe(4); expect(inner.home.arity).toBe(5);
    expect(outer.scope.map(entry => entry.label)).toEqual(['same', 'same@2', 'same@3', 'same@4']);
    expect(inner.scope.map(entry => entry.label)).toEqual(['same', 'same@2', 'same@3', 'same@4', 'same@5']);
    expect(outer.label).toBe('(Unfamiliar same@4)'); expect(inner.label).toBe('(Unfamiliar same@5)');
    expect(outer.term).toEqual(inner.term); expect(outer.id).not.toBe(inner.id);
    expect(inner.focusPath).toEqual(['lamBody', 'appArg', 'lamBody']);
    expect(a(inner.home.telescope)[1]).toEqual(outer.home.telescope);
  });
  it.each([false, true])('retains dependent let types, values, scopes and nondep=%s', nondep => {
    const term: JsonValue = ['forallE', name('same'), app(c('Domain'), lit(0)),
      ['letE', name('same'), app(c('Family'), b(0)), app(c('Value'), b(0)), app(c('Body'), b(0), b(1)), nondep], 'implicit'];
    const source = sourceFor(term), model = available(source);
    expect(model.occurrences.map(item => [item.headName, item.focusPath, item.home.arity])).toEqual([
      ['Domain', ['piDomain'], 3], ['Family', ['piBody', 'letType'], 4],
      ['Value', ['piBody', 'letValue'], 4], ['Body', ['piBody', 'letBody'], 5],
    ]);
    const body = model.occurrences[3];
    expect(body.label).toBe('(Body same@5 same@4)');
    expect(body.scope[4]).toEqual({ position: 4, label: 'same@5', name: name('same'), type: app(c('Family'), b(0)), value: app(c('Value'), b(0)), nondep });
    expect(body.home.telescope).toEqual(['letE', model.occurrences[1].home.telescope, name('same'), nondep, app(c('Family'), b(0)), app(c('Value'), b(0))]);
  });
  it('finds binder-domain and projection-value applications without admitting nonexpression fields', () => {
    const term = lam('NeverAHead', app(c('Domain'), lit(0)), ['proj', name('NeverAnApplication'), n(0), app(c('Object'), b(0))]);
    const source = sourceFor(term), model = available(source);
    expect(model.occurrences.map(item => [item.headName, item.focusPath])).toEqual([
      ['Domain', ['lamDomain']], ['Object', ['lamBody', 'projValue']],
    ]);
    const pair = source.record.checking.status === 'captured' && source.record.checking.steps[0].output;
    if (!pair || pair.status !== 'candidate') throw Error('fixture');
    for (const item of model.occurrences) expect(positionalResultPath(pair.result, model.sourcePath, item.sourcePath)).toEqual(item.focusPath);
    for (const suffix of [['type'], ['home', 'telescope'], ['term', 1], ['term', 3, 1], ['term', 3, 2]])
      expect(positionalResultPath(pair.result, model.sourcePath, [...model.sourcePath, ...suffix])).toBeUndefined();
  });
  it('includes nullary constants but never treats universe constructors as occurrences', () => {
    const source = sourceFor(c('Unfamiliar', [['max', ['zero'], ['succ', ['zero']]]]));
    const model = available(source);
    expect(model.totalCount).toBe(1); expect(model.occurrences[0].headName).toBe('Unfamiliar');
    expect(model.occurrences[0].focusPath).toEqual([]);
    expect(model.occurrences[0].label).toBe('Unfamiliar.{max(0, succ(0))}');
  });
  it('counts omitted candidates exactly at count and depth limits', () => {
    const source = sourceFor(app(c('Combine'), app(c('Left'), lit(0)), app(c('Right'), lit(1))));
    expect(available(source, { maxCount: 1 })).toMatchObject({ totalCount: 3, omittedCount: 2, omissions: { countLimit: 2, depthLimit: 0, scopeLimit: 0 } });
    expect(available(source, { maxDepth: 0 })).toMatchObject({ totalCount: 3, omittedCount: 2, omissions: { countLimit: 0, depthLimit: 2, scopeLimit: 0 } });
    expect(available(source, { maxCount: 0, maxDepth: 0 })).toMatchObject({ totalCount: 3, omittedCount: 3, omissions: { countLimit: 1, depthLimit: 2, scopeLimit: 0 } });
    expect(definitionOccurrences(source, { maxDepth: 65 }).status).toBe('unavailable');
    expect(definitionOccurrences(source, { maxCount: -1 }).status).toBe('unavailable');
  });
  it('rejects replacement record identity and cloned or old action choices', () => {
    const source = sourceFor(app(c('Unfamiliar'), lit(0))), choice = available(source).occurrences[0];
    expect(definitionOccurrences({ ...source, record: clone(source.record) }).status).toBe('unavailable');
    const different = sourceFor(app(c('Unfamiliar'), lit(1)));
    expect(source.record.captureId).toBe(different.record.captureId); // Display IDs alone are insufficient.
    expect(definitionOccurrences({ ...source, history: different.history }).status).toBe('unavailable');
    expect(definitionOccurrenceFocus(different, choice)).toBeUndefined();
    expect(definitionOccurrenceFocus(source, clone(choice))).toBeUndefined();
    expect(definitionOccurrenceFocus({ ...source, stepIndex: 1 }, choice)).toBeUndefined();
    expect(Object.isFrozen(choice)).toBe(true); expect(Object.isFrozen(choice.focusPath)).toBe(true);
  });
  it('requires a completed eligible prefix but permits an earlier step after later failure', () => {
    const source = sourceFor(app(c('Unfamiliar'), lit(0)));
    const base: DecompositionHistory = validateDecompositionHistory({ ...source.history, attempts: [] });
    const value = firstFocus(base, 'empty'); errorStop(value, 1, 0);
    const history = append(base, value), record = history.attempts[0].record;
    expect(definitionOccurrences({ history, record, stepIndex: 1 }).status).toBe('unavailable');
    expect(available({ history, record, stepIndex: 0 }).occurrences[0].headName).toBe('Unfamiliar');
    expect(definitionOccurrences({ history, record, stepIndex: -1 }).status).toBe('unavailable');
    expect(definitionOccurrences({ history, record, stepIndex: 4 }).status).toBe('unavailable');
  });
  it('searches exact occurrences beyond the initial displayed hundred without changing their identity', () => {
    const join = (values: JsonValue[]): JsonValue => values.length === 1 ? values[0]
      : app(c('Combine'), join(values.slice(0, Math.floor(values.length / 2))), join(values.slice(Math.floor(values.length / 2))));
    const values = Array.from({ length: 131 }, (_, i) => app(c(i === 130 ? 'LaterDefinition' : 'Unfamiliar'), lit(i)));
    const source = sourceFor(join(values)), first = available(source);
    expect(first.occurrences.some(item => item.headName === 'LaterDefinition')).toBe(false);
    const filtered = available(source, { filter: 'LaterDefinition' });
    const chosen = filtered.occurrences.find(item => item.headName === 'LaterDefinition')!;
    expect(chosen).toBeDefined(); expect(chosen.label).toBe('(LaterDefinition 130)');
    expect(definitionOccurrenceFocus(source, chosen)).toEqual({ kind: 'focus', path: chosen.focusPath });
    expect(filtered.totalCount).toBe(first.totalCount);
    expect(filtered.filteredCount).toBeGreaterThan(0);
    expect(filtered.occurrences.length + filtered.omittedCount + filtered.filteredCount).toBe(filtered.totalCount);
    const repeated = available(source, { filter: 'laterdefinition' }).occurrences.find(item => item.headName === 'LaterDefinition')!;
    expect(repeated.id).toBe(chosen.id); expect(repeated.term).toEqual(chosen.term);
  });
  it('searches disambiguated scoped labels while keeping unmatched names out of the display count', () => {
    const source = sourceFor(lam('same', nat, app(c('Combine'), app(c('Unfamiliar'), b(0)), lam('same', nat, app(c('Unfamiliar'), b(0))))));
    const model = available(source, { filter: 'unfamiliar same@5' });
    const choice = model.occurrences.find(item => item.headName === 'Unfamiliar')!;
    expect(choice.label).toBe('(Unfamiliar same@5)'); expect(choice.home.arity).toBe(5);
    expect(model.occurrences.some(item => item.label === '(Unfamiliar same@4)')).toBe(false);
    expect(model.filteredCount).toBeGreaterThan(0);
    expect(definitionOccurrenceFocus(source, choice)?.path).toEqual(['lamBody', 'appArg', 'lamBody']);
  });
  it('reports unsearched labels explicitly and still finds later exact head names', () => {
    const join = (depth: number): JsonValue => depth === 0 ? c('Leaf') : app(c('Branch'), join(depth - 1), join(depth - 1));
    const source = sourceFor(app(c('Combine'), join(8), c('BeyondSearchBudget')));
    const noMatch = available(source, { filter: 'absent' });
    expect(noMatch.occurrences).toHaveLength(0);
    expect(noMatch.omissions.labelSearchLimit).toBeGreaterThan(0);
    expect(noMatch.omittedCount + noMatch.filteredCount).toBe(noMatch.totalCount);
    const model = available(source, { filter: 'BeyondSearchBudget' });
    expect(model.occurrences.some(item => item.headName === 'BeyondSearchBudget')).toBe(true);
  });
  it('retains an exact selectable application when long scoped names exceed label limits', () => {
    const join = (depth: number): JsonValue => depth === 0 ? b(0) : app(c('Branch'), join(depth - 1), join(depth - 1));
    const source = sourceFor(lam('x'.repeat(600), nat, join(8)));
    const model = available(source, { filter: 'Branch' }), first = model.occurrences[0];
    expect(first.headName).toBe('Branch'); expect(first.labelUnavailable).toContain('bounded readable-label');
    expect(first.label).toBe('Branch'); expect(first.home.arity).toBe(4);
    expect(definitionOccurrenceFocus(source, first)).toEqual({ kind: 'focus', path: ['lamBody'] });
  });
  it('formats result terms using the complete surrounding scope and preserves the exact term', () => {
    const source = sourceFor(app(c('Unfamiliar'), lit(0)));
    const choice = available(source).occurrences[0];
    const pair = { home: choice.home, term: app(c('Different'), b(0), b(1), b(2)), type: nat };
    expect(scopedExpressionLabel(pair)).toBe('(Different same@3 same@2 same)');
    expect(scopedExpressionLabel(pair, 'type')).toBe('Nat');
    expect(pair.term).toEqual(app(c('Different'), b(0), b(1), b(2)));
  });
});
