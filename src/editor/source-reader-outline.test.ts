import { readFileSync } from 'node:fs';
import { fileURLToPath } from 'node:url';
import path from 'node:path';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { SourceSnapshotOrigin } from './source-origin';
import { validateSourceDecomposition, type DecompositionHistory, type SourceDecompositionBundle } from './source-decomposition';
import { parseEditorMessage, retainedDecompositionHistory } from './host';
import { SourceDecompositionReading } from './SourceDecompositionReading';
import { SourceSnapshotReading, savedSourceSnapshot } from './SourceSnapshotReading';
import { OUTLINE_SECTIONS, outlineDestinations, outlineIds, outlineNamespace, outlineWording, type OutlineAttempt, type OutlineSection } from './SourceReaderOutline';
import { a, append, c, checking, errorStop, focus, id, initial, record, seedCheckpoint, truncate } from './source-decomposition-chain.test-fixtures';

const document = { uri: 'file:///control.lean', fileName: '/control.lean', version: 3,
  selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } };
const origin = (captureId: string): SourceSnapshotOrigin => ({ kind: 'local-editor-process-snapshot', captureId, sourceSha256: '0'.repeat(64),
  engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
  project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
  document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' });
/** The reader vocabulary controls of the provenance suite, applied to the outline's own wording. */
const FORBIDDEN = /witness|there exists|there is |holds|\bverified\b|checked now|not a proposition|\binvalid\b|proves|supplier|\bvalid\b/i;
const SECTION_START: Record<OutlineSection, string> = { step: '<section class="continuation-step"', provenance: '<section class="source-provenance"',
  supply: '<section class="source-supplier"', outcomes: '<details class="snapshot-exact" open=""><summary>Recorded outcomes in this attempt (' };

function argumentFocus(history: DecompositionHistory, attempt: number) {
  const result = seedCheckpoint(history).candidate.result;
  return record(history, { kind: 'focus', path: ['appArg'] }, focus({ home: result.home, term: a(result.term)[2], type: c('Nat') }), { id: attempt });
}
/** Bundles of the retained record objects themselves, as the host passes them with their history. */
const bundles = (history: DecompositionHistory): SourceDecompositionBundle[] =>
  history.attempts.map(entry => ({ snapshot: entry.snapshot, origin: origin(entry.record.captureId), record: entry.record }));
const render = (history: DecompositionHistory, withHistory = true, currentOrigin = true) => renderToStaticMarkup(createElement(SourceDecompositionReading,
  { attempts: bundles(history), ...(withHistory ? { history } : {}), currentOrigin, onContinue: () => { throw Error('no action may run during rendering'); } }));

/** Static markup only; no DOM is assumed. Each tag carrying `attribute`, in document order. */
function tagsWith(html: string, attribute: string) {
  return [...html.matchAll(new RegExp(`<([a-z]+)\\b[^>]*\\s${attribute}="([^"]*)"[^>]*>`, 'g'))].map(match => ({ tag: match[1], value: match[2], at: match.index!, token: match[0] }));
}
const attribute = (token: string, name: string) => token.match(new RegExp(`\\s${name}="([^"]*)"`))?.[1];
const visible = (html: string) => html.replace(/<[^>]+>/g, ' ').replace(/\s+/g, ' ').trim();
/** The outline and every landing of one rendered attempt, with the resolution of each link inside the given markup. */
function outlineOf(html: string) {
  const navs = tagsWith(html, 'data-reader-outline').filter(item => item.tag === 'nav');
  expect(navs.length).toBeLessThanOrEqual(1);
  if (!navs.length) return null;
  const nav = navs[0], namespace = nav.value, navEnd = html.indexOf('</nav>', nav.at) + 6, markup = html.slice(nav.at, navEnd);
  const links = tagsWith(markup, 'data-reader-outline-link').map(item => ({ section: item.value as OutlineSection, id: attribute(item.token, 'id')!, href: attribute(item.token, 'href')! }));
  const landings = tagsWith(html, 'data-reader-outline-landing').map(item => {
    const end = html.indexOf('</div>', item.at) + 6, block = html.slice(item.at, end), link = block.match(/<a id="([^"]*)" href="([^"]*)"[^>]*>([^<]*)<\/a>/)!;
    return { section: item.value as OutlineSection, namespace: attribute(item.token, 'data-reader-outline'), id: link[1], href: link[2], label: link[3], block, end };
  });
  return { namespace, markup, links, landings, title: attribute(nav.token, 'aria-labelledby')!, start: nav.at, end: navEnd };
}
/** Contract of one rendered attempt: the outline follows the step controls, each destination's landing
 * immediately precedes its existing section, and every link resolves to exactly one element of this outline. */
function expectPlaced(html: string, outline: NonNullable<ReturnType<typeof outlineOf>>) {
  const ids = [...html.matchAll(/\sid="([^"]*)"/g)].map(match => match[1]), count = (value: string) => ids.filter(item => item === value).length;
  expect(new Set(ids).size).toBe(ids.length);
  expect(outline.start).toBeGreaterThan(html.indexOf('aria-label="Ordered continuation steps"'));
  expect(html.slice(html.indexOf('aria-label="Ordered continuation steps"'), outline.start)).toMatch(/<\/ol>$/);
  expect(outline.links.map(link => link.section)).toEqual(outline.landings.map(landing => landing.section));
  for (const landing of outline.landings) {
    expect(landing.namespace).toBe(outline.namespace);
    expect(html.startsWith(SECTION_START[landing.section], landing.end), `${landing.section} landing precedes its section`).toBe(true);
    const link = outline.links.find(item => item.section === landing.section)!;
    expect(link.href).toBe(`#${landing.id}`); expect(landing.href).toBe(`#${link.id}`);
    expect(count(landing.id)).toBe(1); expect(count(link.id)).toBe(1);
  }
  // Every rendered section of the four kinds has its landing, and no landing stands before another element.
  for (const section of OUTLINE_SECTIONS) expect(outline.landings.some(landing => landing.section === section)).toBe(html.includes(SECTION_START[section]));
  expect(count(outline.title)).toBe(1);
  const own = outline.markup + outline.landings.map(landing => landing.block).join('');
  expect(own).not.toMatch(/role="tab|aria-current|aria-selected|data-source-result|data-provenance|data-supplier|<h[1-6]/);
  expect(visible(own)).not.toMatch(FORBIDDEN); expect(visible(own)).not.toMatch(/prefix outcomes/i);
}

describe('selected-attempt section outline wording and identity', () => {
  const attempt = (patch: Partial<OutlineAttempt>): OutlineAttempt => ({ current: true, attempt: 7, step: { number: 5, title: 'Check part · Product domain' }, outcomesAfterStep: false, ...patch });
  it('keeps attempt, selected step and current or earlier qualification in the outline and each return link', () => {
    expect(outlineWording.identity(attempt({}))).toBe('Current continuation · attempt 7 · step 5 · Check part · Product domain');
    expect(outlineWording.returnLabel(attempt({}))).toBe('Current continuation · attempt 7 · step 5 · section navigation');
    expect(outlineWording.identity(attempt({ current: false, attempt: 3, step: { number: 2, title: 'Inspect type' } }))).toBe('Earlier continuation · attempt 3 · step 2 · Inspect type');
    expect(outlineWording.returnLabel(attempt({ current: false, attempt: 3, step: { number: 2, title: 'Inspect type' } }))).toBe('Earlier continuation · attempt 3 · step 2 · section navigation');
    expect(outlineWording.identity(attempt({ step: null }))).toBe('Current continuation · attempt 7 · no recorded step');
    expect(outlineWording.returnLabel(attempt({ step: null }))).toBe('Current continuation · attempt 7 · no recorded step · section navigation');
    expect(Object.values(outlineWording.sections)).toEqual(['Step reading', 'Ordered provenance', 'Supply reading', 'Attempt outcomes']);
  });

  it('states that attempt outcomes are the whole attempt, including later steps when an earlier prefix is selected', () => {
    expect(outlineWording.outcomesScope(attempt({}))).toBe('All recorded outcomes of attempt 7, not only those of step 5.');
    expect(outlineWording.outcomesScope(attempt({ step: { number: 2, title: 'Check field 1' }, outcomesAfterStep: true })))
      .toBe('All recorded outcomes of attempt 7, including outcomes of steps after step 2, which are outside the selected prefix.');
    expect(outlineWording.outcomesScope(attempt({ step: null }))).toBe('All recorded outcomes of attempt 7.');
    const texts = [outlineWording.navigation, ...Object.values(outlineWording.sections), ...[true, false].flatMap(current => [null, { number: 1, title: 'Read logical structure' }].flatMap(step =>
      [true, false].flatMap(outcomesAfterStep => { const value = attempt({ current, step, outcomesAfterStep }); return [outlineWording.identity(value), outlineWording.returnLabel(value), outlineWording.outcomesScope(value)]; })))];
    for (const text of texts) { expect(text).not.toMatch(FORBIDDEN); expect(text).not.toMatch(/prefix outcomes|\bselected (object|section)|\bcurrent section/i); }
  });

  it('names four potential destinations in document order, each only when its section is rendered', () => {
    expect(OUTLINE_SECTIONS).toEqual(['step', 'provenance', 'supply', 'outcomes']); expect(Object.isFrozen(OUTLINE_SECTIONS)).toBe(true);
    expect(outlineDestinations({ step: true, provenance: true, supply: true, outcomes: true })).toEqual(['step', 'provenance', 'supply', 'outcomes']);
    expect(outlineDestinations({ step: false, provenance: true, supply: false, outcomes: true })).toEqual(['provenance', 'outcomes']);
    expect(outlineDestinations({ step: false, provenance: false, supply: false, outcomes: false })).toEqual([]);
  });

  it('namespaces every target by mounted instance, capture and selected step, with an explicit no-step key', () => {
    const capture = id(7), other = id(8);
    const spaces = [outlineNamespace('«r1»', capture, 4), outlineNamespace('«r2»', capture, 4), outlineNamespace('«r1»', other, 4), outlineNamespace('«r1»', capture, 3), outlineNamespace('«r1»', capture, null)];
    expect(new Set(spaces).size).toBe(spaces.length);
    expect(spaces[0]).toContain(capture); expect(spaces[0]).toMatch(/step-4$/); expect(spaces[4]).toMatch(/no-step$/);
    const ids = spaces.flatMap(space => { const set = outlineIds(space); return [set.title, ...OUTLINE_SECTIONS.flatMap(section => [set.link(section), set.landing(section)])]; });
    expect(new Set(ids).size).toBe(ids.length);
  });
});

describe('selected-attempt section outline in the attempt reader', () => {
  it('follows the step controls and puts a return landing immediately before each existing section', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1)), html = render(history);
    const outline = outlineOf(html)!;
    expect(outline.links.map(link => link.section)).toEqual(['step', 'provenance', 'supply', 'outcomes']);
    expectPlaced(html, outline);
    const heading = html.match(/<h4>Step 2 · ([^<]*)<\/h4>/)![1], captured = history.attempts[0].record;
    expect(visible(outline.markup)).toContain(`Section navigation · Current continuation · attempt 1 · step 2 · ${heading}`);
    expect(outline.namespace).toContain(captured.captureId); expect(outline.namespace).toMatch(/step-1$/);
    expect(outline.landings.map(landing => landing.label)).toEqual(Array(4).fill('Current continuation · attempt 1 · step 2 · section navigation'));
    // The outcome landing sits outside the user-collapsible list, which keeps its own default state, and states the whole-attempt scope.
    const outcomes = outline.landings.find(landing => landing.section === 'outcomes')!;
    expect(outcomes.block).not.toContain('<details'); expect(visible(outcomes.block)).toContain('All recorded outcomes of attempt 1, not only those of step 2.');
    expect(html.slice(outcomes.end)).toMatch(/^<details class="snapshot-exact" open=""><summary>Recorded outcomes in this attempt \(\d+\)<\/summary>/);
    // The provenance occurrence anchors keep their existing instance-capture-step prefix.
    expect(html).toMatch(new RegExp(`id="[^"]*-${captured.captureId}-1-[a-z]+-[^"]*-occurrence-\\d+"`));
  });

  it('gives no destination to an absent panel and keeps refused panels and zero-receipt steps navigable', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1));
    const absent = render(history, false), withoutHistory = outlineOf(absent)!;
    expect(withoutHistory.links.map(link => link.section)).toEqual(['step', 'outcomes']);
    expect(absent).toContain('data-provenance-absent'); expect(absent).toContain('data-supplier-state="no-history"');
    expectPlaced(absent, withoutHistory);
    // A stopped final step with no retained receipts: its refusal panels remain inspectable and the whole-attempt outcomes stay reachable.
    const raw = argumentFocus(initial().history, 1); errorStop(raw, 1, 0);
    const stopped = append(initial().history, raw), html = render(stopped), outline = outlineOf(html)!;
    expect(html).toContain('Stopped during operation-checking: callback failed'); expect(html).toContain('data-provenance-refused'); expect(html).toContain('data-supplier-state="refused"');
    expect(outline.links.map(link => link.section)).toEqual(['step', 'provenance', 'supply', 'outcomes']);
    expectPlaced(html, outline);
    expect(outline.start).toBeGreaterThan(html.indexOf('Stopped during operation-checking'));
  });

  it('names a captured attempt without steps explicitly and never invents a step reading', () => {
    const first = append(initial().history, argumentFocus(initial().history, 1)), raw = argumentFocus(first, 2), check = checking(raw);
    check.action = { status: 'error', reason: 'Constructed extraction error.' }; check.steps = []; check.selected = null; check.stop = null; truncate(raw, 2);
    const history = append(first, raw), html = render(history), outline = outlineOf(html)!;
    expect(history.attempts[1].record.checking.status === 'captured' && history.attempts[1].record.checking.steps.length).toBe(0);
    expect(html).toContain('Constructed extraction error.'); expect(html).not.toContain('<section class="continuation-step"');
    expect(visible(outline.markup)).toContain('Section navigation · Current continuation · attempt 2 · no recorded step');
    expect(outline.links.map(link => link.section)).not.toContain('step'); expect(outline.links.map(link => link.section)).toContain('outcomes');
    expect(outline.namespace).toMatch(/no-step$/); expect(visible(outline.markup + outline.landings.map(landing => landing.block).join(''))).not.toMatch(/step 1\b/i);
    expect(visible(outline.landings.find(landing => landing.section === 'outcomes')!.block)).toContain('All recorded outcomes of attempt 2.');
    expectPlaced(html, outline);
  });

  it('omits the outline when checking is unavailable', () => {
    const first = append(initial().history, argumentFocus(initial().history, 1)), raw = argumentFocus(first, 2);
    raw.checking = { status: 'unavailable', kind: 'error', phase: 'constructed-control', reason: 'Constructed unavailable checking.', attempted: true };
    const html = render(append(first, raw));
    expect(html).toContain('Continuation unavailable during constructed-control: Constructed unavailable checking.');
    expect(html).not.toContain('data-reader-outline'); expect(html).not.toContain('Section navigation');
  });

  it('marks a saved history like the live one without adding actions, and rendering leaves saved bytes unchanged', () => {
    const base = initial(), history = append(base.history, argumentFocus(base.history, 1)), live = bundles(history);
    const saved = render(history, true, false), outline = outlineOf(saved)!;
    expect(saved).toContain('This saved history has an unverified origin.'); expectPlaced(saved, outline);
    expect(outline.markup + outline.landings.map(landing => landing.block).join('')).not.toContain('<button');
    const before = JSON.stringify(savedSourceSnapshot(base.snapshot, undefined, history.occurrence, undefined, undefined, live));
    renderToStaticMarkup(createElement(SourceSnapshotReading, { snapshot: base.snapshot, occurrence: history.occurrence, decompositions: live }));
    const after = JSON.stringify(savedSourceSnapshot(base.snapshot, undefined, history.occurrence, undefined, undefined, live));
    expect(after).toBe(before); expect(after).not.toMatch(/reader-outline|Section navigation|section navigation/);
  });

  it('gives two mounted readers distinct targets that resolve inside their own reader', () => {
    const history = append(initial().history, argumentFocus(initial().history, 1));
    const html = renderToStaticMarkup(createElement('div', {}, ...['one', 'two'].map(instance => createElement('div', { key: instance, 'data-outline-instance': instance },
      createElement(SourceDecompositionReading, { attempts: bundles(history), history, currentOrigin: true, onContinue: () => { throw Error('no action'); } })))));
    const ids = [...html.matchAll(/\sid="([^"]*)"/g)].map(match => match[1]);
    expect(new Set(ids).size).toBe(ids.length);
    const mounted = ['one', 'two'].map(instance => { const start = html.indexOf(`data-outline-instance="${instance}"`); return html.slice(start, instance === 'one' ? html.indexOf('data-outline-instance="two"') : undefined); });
    const outlines = mounted.map(markup => outlineOf(markup)!);
    expect(outlines[0].namespace).not.toBe(outlines[1].namespace);
    outlines.forEach((outline, i) => { expectPlaced(mounted[i], outline); for (const link of outline.links) expect(mounted[1 - i]).not.toContain(link.href); });
  });

  it('adds no host path, automatic effect, URL change or sticky chrome', () => {
    const editor = path.dirname(fileURLToPath(import.meta.url)), source = readFileSync(path.join(editor, 'SourceReaderOutline.tsx'), 'utf8');
    expect(source).not.toMatch(/postMessage|acquireVsCodeApi|from '\.\/host'|useEffect|useLayoutEffect|pushState|replaceState|location\.hash|scrollBehavior/);
    expect(source).toContain('event.preventDefault()');
    expect(readFileSync(path.join(editor, 'source-reader-outline.css'), 'utf8').replace(/\/\*[\s\S]*?\*\//g, '')).not.toMatch(/sticky|fixed|z-index|scroll-margin|drawer/);
  });
});

/** Every retained real row, parsed through the host path: the outline appears exactly where
 * the attempt's sections render, with the attempt and step identity of the heading above it. */
const corpora = [['v3 logical corpus', process.env.DEFINOGRAPH_SOURCE_LOGICAL_FIXTURES], ['RC3 acceptance corpus', process.env.DEFINOGRAPH_ACCEPTANCE_FIXTURES]] as const;
for (const [name, location] of corpora) describe.skipIf(!location)(`section outline on every row of the ${name}`, () => {
  it('names only rendered destinations for the displayed attempt and selected step', () => {
    const rows = JSON.parse(readFileSync(location!, 'utf8')) as any[];
    expect(rows.length).toBeGreaterThan(0);
    for (const row of rows) {
      const recorded = row.parent.origin, rowDocument = { ...recorded.document, fileName: new URL(recorded.document.uri).pathname, selection: recorded.selection };
      const parsed = parseEditorMessage({ type: 'statementlens.error', requestId: '1', document: rowDocument, message: 'Independent guided export unavailable.',
        sourceSnapshot: row.parent.snapshot, sourceSnapshotOrigin: row.parent.origin, sourceOccurrence: row.parent.occurrence, ...(row.seed ? { headExposure: row.seed } : {}),
        decompositions: [...row.priorAttempts, { snapshot: row.response.sourceSnapshot, origin: row.response.sourceSnapshotOrigin, record: row.response.sourceDecomposition }] });
      if (!parsed || parsed.type === 'statementlens.status' || !parsed.decompositions) throw Error(`host path rejected ${row.label}`);
      const live = parsed.decompositions, history = retainedDecompositionHistory(live), last = live.at(-1)!.record;
      const html = renderToStaticMarkup(createElement(SourceDecompositionReading, { attempts: live, history, currentOrigin: true, onContinue: () => { throw Error('no action'); } }));
      const outline = outlineOf(html);
      if (last.checking.status !== 'captured') { expect(outline, row.label).toBeNull(); continue; }
      expect(outline, row.label).not.toBeNull(); expectPlaced(html, outline!);
      const step = last.checking.steps.at(-1), title = step ? html.match(/<h4>(Step \d+ · [^<]*)<\/h4>/)?.[1] : undefined;
      expect(visible(outline!.markup), row.label).toContain(`Current continuation · attempt ${live.length} · ${step ? `step ${step.index + 1} · ${title!.replace(/^Step \d+ · /, '')}` : 'no recorded step'}`);
      expect(outline!.links.some(link => link.section === 'outcomes'), row.label).toBe(true);
    }
  }, 240000);
});
