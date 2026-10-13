/** Constructed parser controls only; no native execution or authority is implied. */
import type { JsonObject, JsonValue } from '../packets/packet';
import { validateSourceOccurrence, type SourceOccurrence } from './source-occurrence';
import { validateSourceSnapshot, type SnapshotOutcome, type SourceSnapshot } from './source-snapshot';

const name = (text: string): JsonValue => text.split('.').reduce<JsonValue>((parent, part) => ['str', parent, part], ['anonymous']);
const n = (value: number): JsonValue => ['nat', String(value)];
const constant = (text: string): JsonValue => ['const', name(text), []];
const prop: JsonValue = ['sort', ['zero']];
export const PROOF_CAPTURE = '770e8400-e29b-41d4-a716-446655440000';

export interface ProofSnapshotOptions {
  /** Axioms recorded by the audit of the accepted component declaration. */
  axioms?: string[];
  /** The outcome of the component receipt; an audit is available only for an accepted one. */
  outcome?: SnapshotOutcome;
  /** The capture stopped with this reason after its context receipt, before the term was checked. */
  stoppedAfterContext?: string;
  /** No checking record: the capture call did not begin, for this reason. */
  unchecked?: string;
  /** Neither frame is available. */
  unprepared?: boolean;
  /** The selected term, as a function of the two free-variable identities; the default is the hypothesis itself. */
  term?: (h: JsonValue, P: JsonValue) => JsonValue;
  /** The term of the original frame, where preparation changed it; the default is the prepared term. */
  originalTerm?: (h: JsonValue, P: JsonValue) => JsonValue;
  /** The elaborator's recorded expected type; the default is that none was recorded. */
  expected?: (h: JsonValue, P: JsonValue) => JsonValue;
}

/** The whole selection `h` in `example (P : Prop) (h : P) : P := h`: the term is the hypothesis, its inferred type the
 * statement `P`. Every declaration is written out here independently of the validator that reconstructs it. */
export function proofSnapshot(options: ProofSnapshotOptions = {}): SourceSnapshot {
  const P = name('_uniq.1'), h = name('_uniq.2');
  const sourceTerm = options.term ? options.term(['fvar', h], ['fvar', P]) : ['fvar', h], sourceType: JsonValue = ['fvar', P];
  const originals: JsonValue[] = [
    { constructor: 'cdecl', index: n(0), fvarId: P, userName: name('P'), type: prop, binderInfo: 'default', kind: 'default' },
    { constructor: 'cdecl', index: n(1), fvarId: h, userName: name('h'), type: ['fvar', P], binderInfo: 'default', kind: 'default' },
  ];
  const frame = { schema: 'definograph.raw-frame.v1', naturalProfile: 2, originalDeclarations: originals, sourceTerm, sourceType };
  const unavailable = { status: 'unavailable', kind: 'limit', phase: 'prepared-serialization', reason: 'raw JSON depth limit exceeded' };
  const base = { schema: 'definograph.source-snapshot.v1',
    selection: { startByte: 37, endByte: 38, requestedStartByte: 37, requestedEndByte: 38, parentDeclaration: null },
    policy: { id: 'named-source-v1', operation: 'editor-source', preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' },
    expectedType: options.expected ? { status: 'available', expression: options.expected(['fvar', h], ['fvar', P]) } : { status: 'absent' } };
  if (options.unprepared) return validateSourceSnapshot({ ...base, original: unavailable, prepared: unavailable,
    checking: { status: 'unavailable', kind: 'prerequisite', phase: 'checking-prerequisite', reason: 'The exact prepared frame is unavailable.', attempted: false } });
  const frames = { original: { status: 'available', typeOrigin: 'inferred', frame: options.originalTerm ? { ...frame, sourceTerm: options.originalTerm(['fvar', h], ['fvar', P]) } : frame },
    prepared: { status: 'available', typeOrigin: 'inferred-instantiated', frame, checkerUniverseParams: [] } };
  if (options.unchecked !== undefined) return validateSourceSnapshot({ ...base, ...frames,
    checking: { status: 'unavailable', kind: 'limit', phase: 'context-policy', reason: options.unchecked, attempted: false } });
  // Positional form: h is the most recent entry (index 0), P the one before it (index 1).
  const positional = (value: JsonValue): JsonValue => !Array.isArray(value) ? value
    : value[0] === 'fvar' ? ['bvar', n(JSON.stringify(value[1]) === JSON.stringify(h) ? 0 : 1)] : value.map(positional);
  const telescope: JsonValue = ['port', ['port', ['nil'], { name: name('P'), info: 'default' }, prop], { name: name('h'), info: 'default' }, ['bvar', n(0)]];
  const close = (tag: 'forallE' | 'lam', body: JsonValue): JsonValue => [tag, name('P'), prop, [tag, name('h'), ['bvar', n(0)], body, 'default'], 'default'];
  const prefix = name(`StatementLens.SourceSnapshot.${PROOF_CAPTURE}`);
  const declarations: JsonObject[] = [
    { kind: 'thmDecl', name: ['str', prefix, 'context'], levelParams: [], type: close('forallE', constant('True')), value: close('lam', constant('True.intro')), all: [['str', prefix, 'context']] },
    { kind: 'defnDecl', name: ['str', prefix, 'component'], levelParams: [], type: close('forallE', positional(sourceType)), value: close('lam', positional(sourceTerm)),
      all: [['str', prefix, 'component']], hints: ['abbrev'], safety: 'safe' },
  ];
  const outcomes: SnapshotOutcome[] = [{ tag: 'accepted' }, options.outcome ?? { tag: 'accepted' }];
  const count = options.stoppedAfterContext !== undefined ? 1 : 2;
  let environment = 0;
  const checks: JsonValue[] = [], audits: JsonValue[] = [];
  declarations.slice(0, count).forEach((declaration, index) => {
    const label = index === 0 ? 'context' : 'component', accepted = outcomes[index].tag === 'accepted', before = environment;
    if (accepted) environment++;
    checks.push({ id: index, pair: 'editor-source', label, displayLabel: label, declaration,
      subject: { attempt: PROOF_CAPTURE, pair: 'editor-source', sequence: index, target: label, declaration },
      envBefore: before, envAfter: environment, heartbeatBound: n(200000), outcome: outcomes[index] as unknown as JsonValue });
    audits.push({ checkId: index, subject: declaration, environment, category: 'declarationCheck',
      result: accepted ? { tag: 'available', axioms: index === 1 ? (options.axioms ?? []).map(name) : [] } : { tag: 'unavailable', reason: 'declaration was not installed' } });
  });
  return validateSourceSnapshot({ ...base, ...frames, checking: { status: 'captured',
    action: options.stoppedAfterContext !== undefined ? { status: 'error', reason: options.stoppedAfterContext } : { status: 'completed' },
    binding: { schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1', attempt: PROOF_CAPTURE, operation: 'editor-source', sourceKind: 'namedComponent',
      declarationPrefix: prefix, universeParams: [], initialEnvironment: 0,
      context: { arity: 2, telescope, registry: [h, P], registryOrder: 'mostRecentFirst', originalDeclarations: originals, originalDeclarationOrder: 'oldestFirst' },
      sourceTerm, sourceType, positionalTerm: positional(sourceTerm), positionalType: positional(sourceType) },
    checks, audits, environmentSnapshotCount: environment + 1 } });
}

/** The whole-term occurrence of that selection, checked in a fresh capture: six accepted receipts and the selected pair. */
export function proofOccurrence(snapshot: SourceSnapshot, captureId = '880e8400-e29b-41d4-a716-446655440000'): SourceOccurrence {
  if (snapshot.prepared.status !== 'available' || snapshot.checking.status !== 'captured') throw Error('test fixture requires a checked prepared frame');
  const frame = snapshot.prepared.frame, source = snapshot.checking.binding, prefix = name(`StatementLens.SourceOccurrence.${captureId}`);
  const context = snapshot.checking.checks[0].declaration, component = snapshot.checking.checks[1].declaration;
  const declarations = ['source', 'extraction.root', 'extraction.selected'].flatMap(part => ['context', 'component'].map((label): JsonObject => {
    const declarationName: JsonValue = ['str', part.split('.').reduce<JsonValue>((parent, piece) => ['str', parent, piece], prefix), label];
    return { ...(label === 'context' ? context : component), name: declarationName, all: [declarationName] };
  }));
  return validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1', parentCaptureId: PROOF_CAPTURE, captureId, path: [],
    policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: n(200000), retainedMetadata: 'definograph.raw.v1' },
    checking: { status: 'captured', action: { status: 'completed' },
      binding: { ...source, attempt: captureId, operation: 'editor-occurrence', sourceKind: 'namedExtraction', declarationPrefix: prefix, path: [] },
      selected: { home: { arity: frame.originalDeclarations.length, telescope: source.context.telescope }, term: source.positionalTerm, type: source.positionalType },
      checks: declarations.map((declaration, index) => { const label = index % 2 === 0 ? 'context' : 'component'; return { id: index, pair: 'editor-occurrence', label, displayLabel: label, declaration,
        subject: { attempt: captureId, pair: 'editor-occurrence', sequence: index, target: label, declaration }, envBefore: index, envAfter: index + 1, heartbeatBound: n(200000), outcome: { tag: 'accepted' } }; }),
      audits: declarations.map((declaration, index) => ({ checkId: index, subject: declaration, environment: index + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } })),
      environmentSnapshotCount: 7 } }, snapshot);
}
