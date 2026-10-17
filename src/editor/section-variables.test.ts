import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { hasSectionVariableRecord, noteLineText, SectionVariableNote, sectionVariableLines, sectionVariableReport, type SectionVariableReport } from './section-variables';

const provenance = (sectionVariables: unknown, parentDeclaration: unknown = 't') => ({ assistant: 'lean', inputMode: 'editor', parentDeclaration, sectionVariables });
const h = { name: 'h', type: 'False', reason: 'not-taken' };
const undetermined = { ...h, reason: 'undetermined' };
const inst = { name: 'inst', type: 'Inhabited β' };
const lines = (report: SectionVariableReport, declaration?: string) => sectionVariableLines(report, declaration).map(noteLineText);
const read = (record: unknown) => sectionVariableReport(provenance(record))!;

describe('section variables left out of the editor reading', () => {
  it('reads the engine record and refuses one that claims more than its check supports', () => {
    expect(sectionVariableReport(provenance({ check: 'matched', omitted: [h], unconfirmed: [] }))).toEqual({ check: 'matched', omitted: [h], unconfirmed: [] });
    expect(sectionVariableReport(provenance({ check: 'none-in-scope', omitted: [], unconfirmed: [] }))).toEqual({ check: 'none-in-scope', omitted: [], unconfirmed: [] });
    expect(sectionVariableReport(provenance({ check: 'no-declaration', omitted: [], unconfirmed: [inst] }))).toEqual({ check: 'no-declaration', omitted: [], unconfirmed: [inst] });
    // An older engine, or a host that did not ask, sends no record, and nothing was left out.
    expect(sectionVariableReport({ assistant: 'lean' })).toBeUndefined();
    expect(hasSectionVariableRecord({ assistant: 'lean' })).toBe(false);
    expect(sectionVariableReport(undefined)).toBeUndefined();
    // "Not taken" needs the declaration's type to have been matched; "undetermined" and a drawn local in doubt need a
    // check that could not decide, and such a check always leaves something in doubt.
    for (const malformed of [{ check: 'no-declaration', omitted: [h], unconfirmed: [] }, { check: 'matched', omitted: [undetermined], unconfirmed: [] },
      { check: 'matched', omitted: [], unconfirmed: [inst] }, { check: 'mentioned', omitted: [], unconfirmed: [inst] }, { check: 'mismatch', omitted: [], unconfirmed: [] },
      { check: 'guessed', omitted: [], unconfirmed: [] }, { check: 'matched', omitted: [] }, { check: 'matched', unconfirmed: [] },
      { check: 'matched', omitted: [{ name: '', type: 'False', reason: 'not-taken' }], unconfirmed: [] }, { check: 'matched', omitted: [{ ...h, reason: 'unused' }], unconfirmed: [] },
      { check: 'matched', omitted: [{ ...h, type: 'x'.repeat(4097) }], unconfirmed: [] }, { check: 'no-declaration', omitted: [], unconfirmed: [{ name: 'inst' }] },
      { check: 'matched', omitted: Array.from({ length: 129 }, () => h), unconfirmed: [] }, []])
      expect(sectionVariableReport(provenance(malformed)), JSON.stringify(malformed).slice(0, 80)).toBeUndefined();
    // The engine cuts a long type to the reader's limit with an ellipsis, and such a type is read.
    expect(read({ check: 'matched', omitted: [{ ...h, type: `${'x'.repeat(4095)}…` }], unconfirmed: [] }).omitted[0]!.type).toHaveLength(4096);
  });

  it('says which section variables are not drawn and why, naming the declaration', () => {
    expect(lines(read({ check: 'matched', omitted: [h], unconfirmed: [] }), 't')).toEqual(['Not drawn here: h : False. It is declared with `variable`, and the type Lean records for t does not include it.']);
    expect(lines(read({ check: 'matched', omitted: [{ name: 'β', type: 'Type', reason: 'not-taken' }, h], unconfirmed: [] }), 't'))
      .toEqual(['Not drawn here: β : Type; h : False. They are declared with `variable`, and the type Lean records for t does not include them.']);
    // In doubt: the reason says why it was not decided, and that the declaration may still have it.
    expect(lines(read({ check: 'no-declaration', omitted: [undetermined], unconfirmed: [] }), '_example')).toEqual(['Not drawn here: h : False. It is declared with `variable` and the selection does not mention it. It may still be a hypothesis or parameter of this command: Lean added no declaration from this buffer to compare with, as for an `example`, a `#check` or a declaration that failed.']);
    expect(lines(read({ check: 'mismatch', omitted: [undetermined], unconfirmed: [] }), 'P')).toEqual(['Not drawn here: h : False. It is declared with `variable` and the selection does not mention it. It may still be a hypothesis or parameter of P: the type Lean records for P did not settle whether it includes it.']);
    expect(lines(read({ check: 'mismatch', omitted: [{ name: 'β', type: 'Type', reason: 'undetermined' }, undetermined], unconfirmed: [] }), 'P')).toEqual(['Not drawn here: β : Type; h : False. They are declared with `variable` and the selection does not mention them. They may still be hypotheses or parameters of P: the type Lean records for P did not settle whether it includes them.']);
    // More than ten in doubt: no type was compared, and the sentence does not say it was.
    const notChecked = lines(read({ check: 'not-checked', omitted: [undetermined], unconfirmed: [] }), 'P');
    expect(notChecked).toEqual(['Not drawn here: h : False. It is declared with `variable` and the selection does not mention it. It may still be a hypothesis or parameter of P: more than ten variables were in doubt, so the type Lean records for P was not compared.']);
    expect(notChecked[0]).not.toMatch(/determined from its type|did not settle/);
    // A drawn local in doubt is named, whatever else is said.
    expect(lines(read({ check: 'no-declaration', omitted: [], unconfirmed: [inst, { name: 'β', type: 'Type' }] }), '_example'))
      .toEqual(['Drawn, but not known to be taken by this command, since Lean added no declaration from this buffer to compare with: inst : Inhabited β; β : Type.']);
    expect(lines(read({ check: 'mismatch', omitted: [undetermined], unconfirmed: [inst] }), 't')[1]).toBe('Drawn, but not known to be included in the type Lean records for t: inst : Inhabited β.');
    for (const check of ['none-in-scope', 'mentioned', 'matched'] as const) expect(lines({ check, omitted: [], unconfirmed: [] }, 't')).toEqual([]);
    // Words a reader would not know are not used.
    for (const record of [{ check: 'matched', omitted: [h], unconfirmed: [] }, { check: 'no-declaration', omitted: [undetermined], unconfirmed: [inst] }])
      for (const line of lines(read(record), 't')) expect(line).not.toMatch(/\btakes? it\b|assumptions of|from a variable command|recorded no declaration/);
  });

  it('is shown after the description of the editor reading, with Lean keywords as code', () => {
    const html = renderToStaticMarkup(createElement(SectionVariableNote, { provenance: provenance({ check: 'matched', omitted: [h], unconfirmed: [] }) }));
    expect(html).toBe('<p data-section-variables="matched">Not drawn here: h : False. It is declared with <code>variable</code>, and the type Lean records for t does not include it.</p>');
    expect(renderToStaticMarkup(createElement(SectionVariableNote, { provenance: provenance({ check: 'mentioned', omitted: [], unconfirmed: [] }) }))).toBe('');
    expect(renderToStaticMarkup(createElement(SectionVariableNote, { provenance: { assistant: 'lean' } }))).toBe('');
    const app = readFileSync(new URL('../App.tsx', import.meta.url), 'utf8');
    expect(app).toContain("Reading a fragment does not assert a theorem.'):activeExample?.description??'Read the objects and relationships in their logical context.'}</p>{host&&<SectionVariableNote provenance={current?.provenance}/>}");
  });

  it('says that variables may be missing when the engine sent a record that cannot be read', () => {
    // The engine leaves variables out only when it sends a record, so an unreadable record must not leave the reader silent.
    for (const unreadable of [{ check: 'matched', omitted: [{ ...h, type: 'x'.repeat(4097) }], unconfirmed: [] }, 'garbled', null]) {
      const html = renderToStaticMarkup(createElement(SectionVariableNote, { provenance: provenance(unreadable) }));
      expect(html).toBe('<p data-section-variables="unreadable">Some variables declared with <code>variable</code> may be left out of this drawing: the record of which ones could not be read.</p>');
    }
  });
});
