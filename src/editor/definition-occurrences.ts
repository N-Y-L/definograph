/** Exact application choices within a retained result. These are syntax positions,
 * not claims that a head is a definition or that its meaning is interpreted. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import { recordedName } from '../packets/recorded-name';
import type { PositionalStructuralInput } from '../packets/structure';
import { formatExpr, nameText } from '../packets/syntax';
import { decompositionParent, decompositionPlan, isValidatedSourceDecomposition,
  type DecompositionHistory, type SourceDecomposition } from './source-decomposition';
import { sourceOccurrenceValidation, type SourceOccurrenceStep } from './source-occurrence';
import type { ClosureItem } from './source-snapshot';

export interface DefinitionOccurrenceSource {
  history: DecompositionHistory;
  record: SourceDecomposition;
  stepIndex: number;
}
export interface DefinitionOccurrenceScope {
  /** Oldest-first position, independent of the display label. */
  position: number;
  label: string;
  name: JsonValue;
  type: JsonValue;
  binderInfo?: JsonValue;
  value?: JsonValue;
  nondep?: boolean;
}
export interface DefinitionOccurrence {
  id: string;
  captureId: string;
  stepIndex: number;
  headName: string;
  label: string;
  labelUnavailable?: string;
  sourcePath: RawPath;
  focusPath: SourceOccurrenceStep[];
  term: JsonValue;
  home: PositionalStructuralInput['home'];
  scope: DefinitionOccurrenceScope[];
}
export type DefinitionOccurrences = {
  status: 'available'; captureId: string; stepIndex: number; sourcePath: RawPath;
  occurrences: DefinitionOccurrence[]; totalCount: number;
  /** Known nonmatches; omitted positions include unsearched bounded labels. */
  filteredCount: number; omittedCount: number;
  omissions: { countLimit: number; depthLimit: number; scopeLimit: number; labelSearchLimit: number };
} | { status: 'unavailable'; reason: string };
export interface DefinitionOccurrenceLimits {
  /** Search every eligible head before display limits, then bounded scoped labels. */
  filter?: string;
  /** Display at most this many candidates (0–200). Omitted candidates are counted. */
  maxCount?: number;
  /** Focus path depth (0–64), further bounded by the retained history's path budget. */
  maxDepth?: number;
}
const edges: Record<string, readonly (readonly [SourceOccurrenceStep, number])[]> = {
  app: [['appFun', 1], ['appArg', 2]], lam: [['lamDomain', 2], ['lamBody', 3]],
  forallE: [['piDomain', 2], ['piBody', 3]], letE: [['letType', 2], ['letValue', 3], ['letBody', 4]],
  proj: [['projValue', 3]],
};
const { freeze } = createExactJsonTools();
const MAX_LABEL_CHARS = 65_536;
const MAX_SEARCH_FORMATS = 256;
const MAX_SEARCH_CHARS = 2_000_000;
const owners = new WeakMap<DefinitionOccurrence, { record: SourceDecomposition; stepIndex: number }>();
const asNode = (value: JsonValue) => value as JsonValue[];
function closure(input: PositionalStructuralInput): ClosureItem[] {
  const result: ClosureItem[] = [];
  let tel = asNode(input.home.telescope);
  while (tel[0] !== 'nil') {
    if (tel[0] === 'port') {
      const attrs = tel[2] as JsonObject;
      result.push({ name: attrs.name, info: attrs.info, type: tel[3] });
    } else result.push({ name: tel[2], nondep: tel[3] as boolean, type: tel[4], value: tel[5] });
    tel = asNode(tel[1]);
  }
  return result.reverse();
}
function scopeFor(items: ClosureItem[]): DefinitionOccurrenceScope[] {
  const used = new Set<string>();
  return items.map((item, position) => {
    const base = recordedName(item.name, 'context entry');
    let label = base;
    for (let i = 2; used.has(label); i++) label = `${base}@${i}`;
    used.add(label);
    return { position, label, name: item.name, type: item.type,
      ...(item.info !== undefined ? { binderInfo: item.info } : {}),
      ...(item.value !== undefined ? { value: item.value, nondep: item.nondep } : {}) };
  });
}
/** Readable labels preserve bound references and distinguish shadowed names.
 * This formatter neither unfolds syntax nor attaches a native status. */
export function scopedExpressionLabel(input: PositionalStructuralInput, target: 'term' | 'type' = 'term'): string {
  const env = scopeFor(closure(input)).map(entry => entry.label).reverse();
  return formatExpr(input[target], env, 2);
}
/** Conservative display-cost bound, including long names substituted for bound
 * indices. This avoids expanding a small raw expression into an enormous label. */
function labelCost(term: JsonValue, scope: DefinitionOccurrenceScope[]): number {
  let boundReferences = 0, longestName = Math.max(0, ...scope.map(entry => entry.label.length));
  const pending = [term];
  while (pending.length) {
    const node = asNode(pending.pop()!);
    if (node[0] === 'bvar') boundReferences++;
    if (node[0] === 'lam' || node[0] === 'forallE' || node[0] === 'letE')
      longestName = Math.max(longestName, nameText(node[1]).length);
    for (const [, index] of edges[String(node[0])] ?? []) pending.push(node[index]);
  }
  return 2 * JSON.stringify(term).length + boundReferences * (longestName + 16);
}
function readableLabel(term: JsonValue, scope: DefinitionOccurrenceScope[], cost: number): { label?: string; reason?: string } {
  if (cost > MAX_LABEL_CHARS) return { reason: 'The scoped expression exceeds the bounded readable-label size; its exact syntax is retained.' };
  try { return { label: formatExpr(term, scope.map(entry => entry.label).reverse(), 2) }; }
  catch (error) { return { reason: error instanceof Error ? error.message : 'Readable expression unavailable.' }; }
}
function eligible(source: DefinitionOccurrenceSource) {
  const { history, record, stepIndex } = source;
  if (!isValidatedSourceDecomposition(record)
    || history.attempts.find(entry => entry.record.captureId === record.captureId)?.record !== record)
    throw new Error('The displayed record is not the exact retained record of this history.');
  if (record.checking.status !== 'captured' || record.checking.action.status !== 'completed')
    throw new Error('The retained continuation did not complete.');
  // These shared rules check the whole chosen prefix and the remaining action,
  // attempt, receipt and path budgets, independently of individual verdicts.
  const parent = decompositionParent(history, record.captureId, stepIndex, 3);
  decompositionPlan(history, record.captureId, stepIndex, { kind: 'focus', path: [] }, 3);
  return parent;
}
function limit(value: number | undefined, fallback: number, maximum: number): number {
  const result = value ?? fallback;
  if (!Number.isSafeInteger(result) || result < 0 || result > maximum) throw new Error('Invalid application occurrence display limit.');
  return result;
}
/** Enumerate each maximal constant-headed application once, also including bare
 * constants as zero-argument applications. Names filter choices; exact source
 * identities and paths determine their correspondence.
 * Only result.term edges are visited; types, names and universes in other fields
 * cannot become focus targets. The already validated expression bounds the full
 * traversal, so omitted candidate counts remain exact even beyond display limits. */
export function definitionOccurrences(source: DefinitionOccurrenceSource, limits: DefinitionOccurrenceLimits = {}): DefinitionOccurrences {
  try {
    const parent = eligible(source), input = parent.result, initialItems = closure(input);
    const maxCount = limit(limits.maxCount, 100, 200);
    if (limits.filter !== undefined && (typeof limits.filter !== 'string' || limits.filter.length > 4096)) throw new Error('Invalid application filter.');
    const filter = (limits.filter ?? '').trim().toLocaleLowerCase();
    const usedEdges = source.history.occurrence.path.length + parent.operations.reduce((n, op) => n + (op.kind === 'focus' ? op.path.length : 0), 0);
    const maxDepth = Math.min(limit(limits.maxDepth, 64, 64), 128 - usedEdges);
    const sourcePath: RawPath = ['checking', 'steps', source.stepIndex, 'output', 'result'];
    const occurrences: DefinitionOccurrence[] = [];
    const omissions = { countLimit: 0, depthLimit: 0, scopeLimit: 0, labelSearchLimit: 0 };
    let totalCount = 0, filteredCount = 0, searchFormats = 0, searchChars = 0;
    const pending: { term: JsonValue; path: SourceOccurrenceStep[]; rawPath: RawPath; functionChild: boolean; items: ClosureItem[] }[] = [
      { term: input.term, path: [], rawPath: [...sourcePath, 'term'], functionChild: false, items: initialItems },
    ];
    while (pending.length) {
      const current = pending.pop()!, node = asNode(current.term);
      if (!current.functionChild && (node[0] === 'app' || node[0] === 'const')) {
        let head = node;
        while (head[0] === 'app') head = asNode(head[1]);
        if (head[0] === 'const') {
          totalCount++;
          if (current.path.length > maxDepth) omissions.depthLimit++;
          else if (current.items.length > 128) omissions.scopeLimit++;
          else {
            const headName = nameText(head[1]);
            let scope: DefinitionOccurrenceScope[] | undefined;
            let text: ReturnType<typeof readableLabel> | undefined;
            let matches = true;
            if (filter && !headName.toLocaleLowerCase().includes(filter)) {
              if (searchFormats >= MAX_SEARCH_FORMATS || searchChars >= MAX_SEARCH_CHARS) {
                omissions.labelSearchLimit++; matches = false;
              } else {
                scope = scopeFor(current.items);
                const cost = labelCost(current.term, scope);
                searchFormats++;
                if (cost > MAX_SEARCH_CHARS - searchChars) {
                  omissions.labelSearchLimit++; matches = false;
                } else {
                  searchChars += cost; text = readableLabel(current.term, scope, cost);
                  if (text.label === undefined) { omissions.labelSearchLimit++; matches = false; }
                  else if (!text.label.toLocaleLowerCase().includes(filter)) { filteredCount++; matches = false; }
                }
              }
            }
            if (matches) {
              if (occurrences.length >= maxCount) omissions.countLimit++;
              else {
                const selected = sourceOccurrenceValidation.selectedAt(input.term, input.home.telescope, initialItems, current.path);
                if (!selected) throw new Error('The application path does not reconstruct its retained expression.');
                scope = scopeFor(selected.items);
                text ??= readableLabel(selected.term, scope, labelCost(selected.term, scope));
                const occurrence: DefinitionOccurrence = {
                  id: `${source.record.captureId}:${source.stepIndex}:${JSON.stringify(current.path)}`,
                  captureId: source.record.captureId, stepIndex: source.stepIndex, headName, label: text.label ?? headName,
                  ...(text.reason ? { labelUnavailable: text.reason } : {}),
                  sourcePath: current.rawPath, focusPath: current.path, term: selected.term,
                  home: { arity: selected.items.length, telescope: selected.telescope }, scope,
                };
                owners.set(occurrence, { record: source.record, stepIndex: source.stepIndex });
                occurrences.push(occurrence);
              }
            }
          }
        }
      }
      for (const [step, index] of [...(edges[String(node[0])] ?? [])].reverse()) {
        const items = step === 'lamBody' || step === 'piBody'
          ? [...current.items, { name: node[1], type: node[2], info: node[4] }]
          : step === 'letBody' ? [...current.items, { name: node[1], type: node[2], value: node[3], nondep: node[5] as boolean }] : current.items;
        pending.push({ term: node[index], path: [...current.path, step], rawPath: [...current.rawPath, index], functionChild: step === 'appFun', items });
      }
    }
    const result: DefinitionOccurrences = { status: 'available', captureId: source.record.captureId, stepIndex: source.stepIndex,
      sourcePath, occurrences, totalCount, filteredCount, omittedCount: totalCount - occurrences.length - filteredCount, omissions };
    freeze(result as unknown as JsonValue);
    return result;
  } catch (error) {
    return { status: 'unavailable', reason: error instanceof Error ? error.message : 'The retained application source is unavailable.' };
  }
}
/** Recheck an actual retained choice at the action boundary. A cloned choice or
 * an old record with reused display text cannot select a new expression. */
export function definitionOccurrenceFocus(source: DefinitionOccurrenceSource, occurrence: DefinitionOccurrence): { kind: 'focus'; path: SourceOccurrenceStep[] } | undefined {
  const owner = owners.get(occurrence);
  if (owner?.record !== source.record || owner.stepIndex !== source.stepIndex) return;
  try {
    eligible(source);
    const operation = { kind: 'focus' as const, path: [...occurrence.focusPath] };
    decompositionPlan(source.history, source.record.captureId, source.stepIndex, operation, 3);
    return operation;
  } catch { return; }
}
