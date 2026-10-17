/** Section variables that the editor's guided reading leaves out of the drawn context.
 *
 * Lean elaborates a declaration's header inside every `variable` of its section, but a theorem takes only the ones its
 * header mentions, the ones named by `include`, and instance variables over those (other declarations take the ones
 * their header or value mentions). The context engine (`lean/StatementLens/Context.lean`, `sectionVariables`) draws a
 * section variable only when it is mentioned or when the declaration's final type shows that it is taken, and reports
 * every other one here with its reason, together with the drawn locals whose taking it could not confirm. The engine
 * leaves variables out only for a host that asks for this record (`sectionVariableReport` in
 * `server/editor-context.ts`). This module reads that record and words it; it decides nothing itself. */
import { Fragment } from 'react';

/** How the engine decided which section variables are drawn. */
export type SectionVariableCheck = 'none-in-scope' | 'mentioned' | 'matched' | 'mismatch' | 'no-declaration' | 'not-checked';
export interface SectionVariableEntry { name: string; type: string }
export interface OmittedSectionVariable extends SectionVariableEntry {
  /** `not-taken`: the declaration's final type shows it is not taken. `undetermined`: the selection does not mention it
   * and the reader could not tell whether the enclosing declaration takes it. */
  reason: 'not-taken' | 'undetermined';
}
export interface SectionVariableReport {
  check: SectionVariableCheck;
  omitted: OmittedSectionVariable[];
  /** Drawn although nothing confirmed that the declaration takes them: an unnamed instance variable, or a section
   * variable only such a local mentions. */
  unconfirmed: SectionVariableEntry[];
}

const CHECKS: readonly SectionVariableCheck[] = ['none-in-scope', 'mentioned', 'matched', 'mismatch', 'no-declaration', 'not-checked'];
/** The checks after which the engine could not decide, and so may leave a variable out as undetermined. */
const UNDECIDED: readonly SectionVariableCheck[] = ['mismatch', 'no-declaration', 'not-checked'];
const text = (value: unknown, limit: number): value is string => typeof value === 'string' && value.length > 0 && [...value].length <= limit;
const entryOf = (entry: unknown): SectionVariableEntry | undefined => {
  if (!entry || typeof entry !== 'object' || Array.isArray(entry)) return undefined;
  const { name, type } = entry as Record<string, unknown>;
  return text(name, 512) && text(type, 4096) ? { name, type } : undefined;
};

/** Whether the engine sent a section-variable record at all, readable or not. */
export function hasSectionVariableRecord(provenance: unknown): boolean {
  return !!provenance && typeof provenance === 'object' && Object.hasOwn(provenance, 'sectionVariables');
}

/** The engine's record, or undefined when it is absent or malformed. An absent record (an older engine, or a host that
 * did not ask for it) means nothing was left out; a malformed one is not trusted. */
export function sectionVariableReport(provenance: unknown): SectionVariableReport | undefined {
  if (!hasSectionVariableRecord(provenance)) return undefined;
  const value = (provenance as Record<string, unknown>).sectionVariables;
  if (!value || typeof value !== 'object' || Array.isArray(value)) return undefined;
  const { check, omitted, unconfirmed } = value as Record<string, unknown>;
  if (!CHECKS.includes(check as SectionVariableCheck) || !Array.isArray(omitted) || omitted.length > 128
    || !Array.isArray(unconfirmed) || unconfirmed.length > 128) return undefined;
  const entries: OmittedSectionVariable[] = [], drawn: SectionVariableEntry[] = [];
  for (const entry of omitted) {
    const read = entryOf(entry), reason = read && (entry as Record<string, unknown>).reason;
    if (!read || (reason !== 'not-taken' && reason !== 'undetermined')) return undefined;
    entries.push({ ...read, reason });
  }
  for (const entry of unconfirmed) {
    const read = entryOf(entry);
    if (!read) return undefined;
    drawn.push(read);
  }
  const decided = check as SectionVariableCheck;
  // A variable left out because the declaration does not take it needs that declaration's type to say so; one in doubt
  // needs a check that could not decide, and such a check always leaves something in doubt.
  if (entries.some(entry => entry.reason === 'not-taken') && decided !== 'matched') return undefined;
  if ((entries.some(entry => entry.reason === 'undetermined') || drawn.length) && !UNDECIDED.includes(decided)) return undefined;
  if (UNDECIDED.includes(decided) && !entries.length && !drawn.length) return undefined;
  return { check: decided, omitted: entries, unconfirmed: drawn };
}

/** One sentence of the note: text, and the Lean keywords set as code. */
export type NoteLine = readonly (string | { code: string })[];
export const noteLineText = (line: NoteLine) => line.map(part => typeof part === 'string' ? part : `\`${part.code}\``).join('');
const variable = { code: 'variable' };

const listed = (entries: readonly SectionVariableEntry[]) => entries.map(entry => `${entry.name} : ${entry.type}`).join('; ');

/** The sentences shown under the reading's title: what is not drawn and why, and what is drawn without confirmation.
 * Empty when nothing was left out and nothing is in doubt. */
export function sectionVariableLines(report: SectionVariableReport, declaration?: string): NoteLine[] {
  // Lean names an `example` `_example` and a `#check` `_check`; neither is a declaration a reader can look up.
  const named = declaration && !declaration.startsWith('_') ? declaration : 'the enclosing declaration';
  const notTaken = report.omitted.filter(entry => entry.reason === 'not-taken');
  const undetermined = report.omitted.filter(entry => entry.reason === 'undetermined');
  const words = (count: number) => count === 1
    ? { it: 'it', is: 'It is', It: 'It', role: 'a hypothesis or parameter' }
    : { it: 'them', is: 'They are', It: 'They', role: 'hypotheses or parameters' };
  const lines: NoteLine[] = [];
  if (notTaken.length) {
    const w = words(notTaken.length);
    lines.push([`Not drawn here: ${listed(notTaken)}. ${w.is} declared with `, variable, `, and the type Lean records for ${named} does not include ${w.it}.`]);
  }
  if (undetermined.length) {
    const w = words(undetermined.length);
    const opening = [`Not drawn here: ${listed(undetermined)}. ${w.is} declared with `, variable, ` and the selection does not mention ${w.it}. `];
    if (report.check === 'no-declaration') lines.push([...opening, `${w.It} may still be ${w.role} of this command: Lean added no declaration from this buffer to compare with, as for an `,
      { code: 'example' }, ', a ', { code: '#check' }, ' or a declaration that failed.']);
    else if (report.check === 'not-checked') lines.push([...opening, `${w.It} may still be ${w.role} of ${named}: more than ten variables were in doubt, so the type Lean records for ${named} was not compared.`]);
    else lines.push([...opening, `${w.It} may still be ${w.role} of ${named}: the type Lean records for ${named} did not settle whether it includes ${w.it}.`]);
  }
  if (report.unconfirmed.length) {
    lines.push([report.check === 'no-declaration'
      ? `Drawn, but not known to be taken by this command, since Lean added no declaration from this buffer to compare with: ${listed(report.unconfirmed)}.`
      : `Drawn, but not known to be included in the type Lean records for ${named}: ${listed(report.unconfirmed)}.`]);
  }
  return lines;
}

/** Shown when the engine sent a record that this reader cannot read: it may have left variables out. */
export const unreadableSectionVariableLine: NoteLine = ['Some variables declared with ', variable, ' may be left out of this drawing: the record of which ones could not be read.'];

export function SectionVariableNote({ provenance }: { provenance: unknown }) {
  if (!hasSectionVariableRecord(provenance)) return null;
  const report = sectionVariableReport(provenance);
  const declaration = (provenance as { parentDeclaration?: unknown }).parentDeclaration;
  const lines = report ? sectionVariableLines(report, typeof declaration === 'string' ? declaration : undefined) : [unreadableSectionVariableLine];
  return lines.length ? <>{lines.map(line => <p key={noteLineText(line)} data-section-variables={report?.check ?? 'unreadable'}>
    {line.map((part, index) => <Fragment key={index}>{typeof part === 'string' ? part : <code>{part.code}</code>}</Fragment>)}
  </p>)}</> : null;
}
