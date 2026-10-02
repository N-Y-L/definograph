import { describe, expect, it } from 'vitest';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { DefinitionWorkspace } from './DefinitionWorkspace';
import { SOURCE_PRESENTATION_SCHEMA, SOURCE_PRESENTATION_NOTE } from './source-presentation';
import type { JsonObject, JsonValue } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { definitionOccurrences } from './definition-occurrences';
import { DefinitionWorkspaceController, sameDefinitionWorkspaceInput, type DefinitionWorkspaceAnchor } from './definition-workspace';
import { parseEditorMessage, type EditorCommand, type EditorMessage } from './host';
import { validateDecompositionHistory, type DecompositionHistory, type DecompositionOperation } from './source-decomposition';
import { headExposureFixture } from './source-decomposition.test-fixtures';
import { append, c, close, clone, id, n, name, o, app } from './source-decomposition-chain.test-fixtures';
import type { SourceActionRequest } from './source-action-navigation';
import type { SourceSnapshotOrigin } from './source-origin';

type Result = Extract<EditorMessage, { type: 'statementlens.analysis' }>;
type Status = Extract<EditorMessage, { type: 'statementlens.status' }>;
const document = { uri: 'file:///control.lean', fileName: '/control.lean', version: 3,
  selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 1 } } };
const origin = (captureId: string): SourceSnapshotOrigin => ({ kind: 'local-editor-process-snapshot', captureId, sourceSha256: '0'.repeat(64),
  engine: { contextSha256: '1'.repeat(64), buildFingerprint: '2'.repeat(64), packageSha256: '3'.repeat(64), leanSha256: '4'.repeat(64) },
  project: { root: '/control', toolchain: 'v4.28.0', libraryPaths: [], dependencyTracking: 'snapshot-paths-only' },
  document: { uri: document.uri, version: document.version }, selection: document.selection, policyId: 'named-source-v1' });
const analysis = { source: 'ForeignWrapper f k', pretty: 'ForeignWrapper f k', guidedContextContract: 'definograph.guided-context.v1',
  expression: { kind: 'constant', name: 'ForeignWrapper' }, tree: { id: 'root', children: [] } };
function parsed(value: unknown): Result {
  const result = parseEditorMessage(value);
  if (result?.type !== 'statementlens.analysis') throw Error('Invalid constructed host control.');
  return result;
}
/** Synthetic parser controls only. These independent declarations and receipts
 * exercise associations and scheduling, and do not claim actual Lean execution. */
function next(history: DecompositionHistory, operation: DecompositionOperation, exposure?: JsonObject, parentStepIndex?: number) {
  const original = history.occurrence.checking;
  if (original.status !== 'captured' || !original.selected) throw Error('Missing constructed occurrence.');
  const previous = history.attempts.at(-1)?.record;
  const checkpoints = previous?.checking.status === 'captured' ? previous.checking.steps.slice(0, parentStepIndex === undefined ? undefined : parentStepIndex + 1).map(step => {
    if (step.output.status !== 'candidate') throw Error('Missing constructed result.');
    const { checking: _checking, ...candidate } = step.output; void _checking;
    return { operation: step.operation, input: step.input, candidate };
  }) : [];
  const input = checkpoints.at(-1)?.candidate.result ?? original.selected;
  const output = exposure ?? { status: 'candidate', result: operation.kind === 'typeComponent'
    ? { home: input.home, term: input.type, type: ['sort', ['succ', ['zero']]] } : input, checking: { status: 'completed' } };
  const outputs = [...checkpoints.map(cp => ({ ...cp.candidate, checking: { status: 'completed' } })), output];
  const operations = [...checkpoints.map(cp => cp.operation), operation], attempt = id(history.attempts.length + 1);
  const prefix = name(attempt, name('SourceDecomposition', name('StatementLens'))), declarations: JsonObject[] = [], labels: string[] = [];
  function declaration(base: JsonValue, label: string, pair: PositionalStructuralInput, type: JsonValue, value: JsonValue) {
    const dn = name(label, base), component = label === 'component'; labels.push(label);
    declarations.push({ kind: component ? 'defnDecl' : 'thmDecl', name: dn, levelParams: [],
      type: close(pair.home.telescope, type, 'forallE'), value: close(pair.home.telescope, value, 'lam'), all: [dn],
      ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) });
  }
  function pairDeclarations(base: JsonValue, pair: PositionalStructuralInput) {
    declaration(base, 'context', pair, c('True'), ['const', name('intro', name('True')), []]);
    declaration(base, 'component', pair, pair.type, pair.term);
  }
  for (const base of [name('source', prefix), name('root', name('extraction', prefix)), name('selected', name('extraction', prefix))]) pairDeclarations(base, original.selected);
  let preceding = original.selected;
  const steps = outputs.map((raw, index) => {
    const out = o(raw), result = out.result as unknown as PositionalStructuralInput, op = operations[index];
    const stepPrefix = name(`step${index}`, prefix), receiptStart = declarations.length;
    pairDeclarations(name(op.kind === 'expose' ? 'result' : op.kind === 'typeComponent' ? 'typeComponent' : 'focus', stepPrefix), result);
    if (op.kind === 'expose') declaration(stepPrefix, 'conversion', result,
      app(c('Eq', [out.carrierSort]), result.type, out.before, result.term), app(['const', name('refl', name('Eq')), [out.carrierSort]], result.type, out.before));
    const step = { index, operation: op, input: preceding, output: out, receiptStart,
      receiptCount: declarations.length - receiptStart, replay: index < checkpoints.length ? 'matched' : 'new' };
    preceding = result; return step;
  });
  const pair = 'editor-decomposition-v3';
  const checking = { status: 'captured', action: { status: 'completed' }, selected: original.selected, steps, stop: null,
    binding: { ...clone(original.binding), operation: pair, sourceKind: 'namedDecomposition', attempt, declarationPrefix: prefix,
      expectedSelected: original.selected, operations, expectedHistory: checkpoints },
    checks: declarations.map((decl, index) => ({ id: index, pair, label: labels[index], displayLabel: labels[index], declaration: decl,
      subject: { attempt, pair, sequence: index, target: labels[index], declaration: decl }, envBefore: index, envAfter: index + 1,
      heartbeatBound: n(200000), outcome: { tag: 'accepted' } })),
    audits: declarations.map((subject, checkId) => ({ checkId, subject, environment: checkId + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } })),
    environmentSnapshotCount: declarations.length + 1 };
  return append(history, clone({ schema: 'definograph.source-decomposition.v3', parentCaptureId: history.occurrence.captureId,
    previousCaptureId: previous?.captureId ?? history.occurrence.captureId, parentStepIndex: checkpoints.length ? checkpoints.length - 1 : 0,
    captureId: attempt, path: history.occurrence.path, operations, policy: { id: 'bounded-decomposition-v3', operation: pair,
      preparation: 'Lean.instantiateMVars', universeSubstitution: 'structural', reduction: 'original-lambda-spine', heartbeatBound: n(200000),
      retainedMetadata: 'definograph.raw.v1', maxOperations: 8, maxChecks: 30, maxFields: 16, logicalInterpretation: 'lean-standard-core-v1' }, checking }) as unknown as JsonObject);
}
function fixture(proofType = false) {
  const f = headExposureFixture(), history = validateDecompositionHistory({ ...f.parent, seed: null, attempts: [] });
  const original = parsed({ type: 'statementlens.analysis', requestId: '0', document, analysis,
    sourceSnapshot: f.snapshot, sourceSnapshotOrigin: origin(history.occurrence.parentCaptureId) });
  const message = (h: DecompositionHistory, requestId: string): Result => parsed({ ...original, requestId,
    sourceSnapshotOrigin: origin(h.occurrence.captureId), sourceOccurrence: h.occurrence,
    ...(h.attempts.length ? { decompositions: h.attempts.map(({ snapshot, record }) => ({ snapshot, record, origin: origin(record.captureId) })) } : {}) });
  const anchor: DefinitionWorkspaceAnchor = { analysis: original.analysis, document, origin: original.sourceSnapshotOrigin!, clause: 'Selected clause', proofType };
  const posts: { request: SourceActionRequest; command: EditorCommand }[] = [];
  const controller = new DefinitionWorkspaceController((request, command) => posts.push({ request, command }), () => {});
  const status = (requestId: string, phase: Status['phase'] = 'analyzing'): Status => ({ type: 'statementlens.status', requestId, document, phase });
  const root = message(history, '1');
  return { f, history, original, root, message, anchor, controller, posts, status };
}
function prepare(proofType = false) {
  const f = fixture(proofType); f.controller.start(f.anchor, f.original);
  expect(f.controller.status(f.status('1'))).toBe(true); expect(f.controller.result(f.root)).toBe(true);
  const history = next(f.history, proofType ? { kind: 'typeComponent' } : { kind: 'focus', path: [] });
  const capture = f.message(history, '2');
  expect(f.controller.status(f.status('2'))).toBe(true); expect(f.controller.result(capture)).toBe(true);
  expect(f.controller.state?.phase).toBe('choosing');
  return { ...f, history, capture };
}

describe('definition workspace exact continuation', () => {
  it.each([false, true])('prepares the exact source with proofType=%s and preserves its original reading', proofType => {
    const f = prepare(proofType);
    expect(f.posts.map(post => post.command.type)).toEqual(['statementlens.checkOccurrence', proofType ? 'statementlens.inspectTypeComponent' : 'statementlens.focusExposedPart']);
    expect(f.controller.state?.anchor.analysis).toBe(f.anchor.analysis);
    expect(f.controller.state?.anchor.clause).toBe('Selected clause');
    expect(f.controller.state?.catalogue?.record).toBe(f.capture.decompositions![0].record);
    expect(f.posts[1].request).toMatchObject({ parentCaptureId: f.history.occurrence.captureId, previousCaptureId: f.history.occurrence.captureId, parentStepIndex: 0, attemptsBefore: 0 });
  });
  it.each([
    { proofType: false, returned: 'nested-focus' },
    { proofType: false, returned: 'type-component' },
    { proofType: true, returned: 'root-focus' },
  ] as const)('requires the exact initial operation for proofType=$proofType, rejecting $returned', ({ proofType, returned }) => {
    const f = fixture(proofType); f.controller.start(f.anchor); f.controller.status(f.status('1')); f.controller.result(f.root);
    const requested = proofType ? { type: 'statementlens.inspectTypeComponent' }
      : { type: 'statementlens.focusExposedPart', path: [] };
    expect(f.posts[1].command).toMatchObject(requested);
    const original = f.history.occurrence.checking;
    if (original.status !== 'captured' || !original.selected) throw Error('Missing constructed source.');
    const operation: DecompositionOperation = returned === 'type-component' ? { kind: 'typeComponent' }
      : { kind: 'focus', path: returned === 'nested-focus' ? ['appFun'] : [] };
    const output = returned === 'nested-focus' ? { status: 'candidate', result: { home: original.selected.home,
      term: (original.selected.term as JsonValue[])[1], type: ['forallE', name('x'), c('Nat'), c('Nat'), 'default'] },
      checking: { status: 'completed' } } as JsonObject : undefined;
    // This answer passes the full wire/history parser and has the same request,
    // parent capture and operation prefix. Its operation still differs from the post.
    const answer = f.message(next(f.history, operation, output), '2');
    f.controller.status(f.status('2'));
    expect(f.controller.result(answer)).toBe(true); expect(f.controller.state?.phase).toBe('unavailable'); expect(f.posts).toHaveLength(2);
    expect(f.controller.retainedCapture).toBe(f.root);
  });
  it('binds the first status, accepts its repeat, and rejects an unannounced or unrelated result', () => {
    for (const condition of ['no-status', 'wrong-request'] as const) {
      const f = fixture(); f.controller.start(f.anchor);
      if (condition === 'wrong-request') { expect(f.controller.status(f.status('1'))).toBe(true); expect(f.controller.status(f.status('1'))).toBe(true); }
      expect(f.controller.result({ ...f.root, requestId: condition === 'wrong-request' ? '9' : '1' })).toBe(false);
      expect(f.controller.state).toBeNull(); expect(f.posts).toHaveLength(1);
    }
  });
  it.each(['stale', 'superseded', 'document'] as const)('cancels a %s status without a later autochain', kind => {
    const f = fixture(); f.controller.start(f.anchor); f.controller.status(f.status('1'));
    const status = kind === 'stale' ? f.status('1', 'stale') : kind === 'superseded' ? f.status('2') : { ...f.status('1'), document: { ...document, version: 4 } };
    expect(f.controller.status(status)).toBe(false); expect(f.controller.result(f.root)).toBe(false);
    expect(f.controller.state).toBeNull(); expect(f.posts).toHaveLength(1);
  });
  const changes: [string, (result: Result) => void][] = [
    ['source', r => { r.analysis.source += ' changed'; }], ['expression', r => { o(r.analysis.expression).name = 'Different'; }],
    ['tree', r => { r.analysis.tree.id = 'other'; }], ['hash', r => { r.sourceSnapshotOrigin!.sourceSha256 = 'f'.repeat(64); }],
    ['version', r => { r.document.version++; r.sourceSnapshotOrigin!.document!.version++; }],
    ['selection', r => { r.document.selection.end.character++; r.sourceSnapshotOrigin!.selection = clone(r.document.selection); }],
    ['engine', r => { r.sourceSnapshotOrigin!.engine.buildFingerprint = 'f'.repeat(64); }],
    ['project', r => { r.sourceSnapshotOrigin!.project.libraryPaths.push('/different'); }],
  ];
  it.each(changes)('discards a changed %s association before continuing', (_label, change) => {
    const f = fixture(), altered = clone(f.root); change(altered); const accepted = parsed(altered);
    expect(sameDefinitionWorkspaceInput(f.anchor, accepted)).toBe(false);
    f.controller.start(f.anchor); f.controller.status(f.status('1'));
    expect(f.controller.result(accepted)).toBe(false); expect(f.posts).toHaveLength(1); expect(f.controller.state).toBeNull();
  });
  it.each([false, true])('reopens retained step zero for proofType=%s without another root command', proofType => {
    const f = prepare(proofType), history = next(f.history, { kind: 'focus', path: [] }), latest = f.message(history, '3');
    f.controller.cancel(); f.posts.length = 0;
    f.controller.start(f.anchor, latest);
    expect(f.posts).toHaveLength(0); expect(f.controller.state?.phase).toBe('choosing');
    expect(f.controller.state?.catalogue?.stepIndex).toBe(0);
    expect(f.controller.state?.catalogue?.record).toBe(latest.decompositions!.at(-1)!.record);
    const catalogue = f.controller.state!.catalogue!, model = definitionOccurrences(catalogue, { filter: proofType ? 'Nat' : 'ForeignWrapper' });
    if (model.status !== 'available') throw Error(model.reason);
    expect(model.occurrences).toHaveLength(1); f.controller.inspect(model.occurrences[0]);
    expect(f.posts[0].request).toMatchObject({ previousCaptureId: catalogue.record.captureId, parentStepIndex: 0, attemptsBefore: 2 });
    const branched = next(history, { kind: 'focus', path: [] }, undefined, 0);
    expect(f.controller.status(f.status('4'))).toBe(true);
    expect(f.controller.result(f.message(branched, '4'))).toBe(true);
    expect(f.controller.state?.phase).toBe('exposing');
    expect(f.posts).toHaveLength(2); expect(f.posts[1].command.type).toBe('statementlens.exposeFocusedHead');
  });
  it('refuses a cloned retained array and an established incompatible history without a root command', () => {
    const f = prepare(); f.posts.length = 0;
    f.controller.start(f.anchor, { ...f.capture, decompositions: [...f.capture.decompositions!] });
    expect(f.controller.state?.phase).toBe('unavailable'); expect(f.posts).toHaveLength(0);
    const other = next(fixture().history, { kind: 'expose', target: 'term' }, o(o(f.f.value.checking).exposure));
    f.controller.start(f.anchor, f.message(other, '3'));
    expect(f.controller.state?.phase).toBe('unavailable'); expect(f.controller.state?.message).toContain('Refresh'); expect(f.posts).toHaveLength(0);
  });
  it.each(['available', 'absent', 'stale', 'budget'] as const)('checks the branded application, retaining exact result with %s presentation', variant => {
    const f = prepare(), catalogue = f.controller.state!.catalogue!;
    const choices = definitionOccurrences(catalogue, { filter: 'ForeignWrapper' });
    if (choices.status !== 'available') throw Error(choices.reason);
    f.controller.inspect(choices.occurrences[0]); expect(f.controller.state?.phase).toBe('focusing');
    const focused = next(f.history, { kind: 'focus', path: [] });
    f.controller.status(f.status('3')); expect(f.controller.result(f.message(focused, '3'))).toBe(true);
    expect(f.controller.state?.phase).toBe('exposing'); expect(f.posts.at(-1)?.command.type).toBe('statementlens.exposeFocusedHead');
    const exposed = next(focused, { kind: 'expose', target: 'term' }, o(o(f.f.value.checking).exposure));
    const wire = clone(f.message(exposed, '4')), bundle = wire.decompositions!.at(-1)!, check = bundle.record.checking;
    if (check.status !== 'captured' || check.steps.at(-1)!.output.status !== 'candidate') throw Error('Missing fixture result.');
    if (variant !== 'absent') Object.assign(bundle, { presentation: { schema: SOURCE_PRESENTATION_SCHEMA,
      captureId: variant === 'stale' ? id(99) : bundle.record.captureId, status: 'available', stepIndex: 2, target: 'term',
      result: (check.steps.at(-1)!.output as { result: unknown }).result, text: variant === 'budget' ? 'x'.repeat(8193) : '<b>same same</b>' } });
    const final = parsed(wire), exact = JSON.stringify(bundle.record);
    f.controller.status(f.status('4')); expect(f.controller.result(final)).toBe(true);
    expect(f.controller.state?.phase).toBe('complete'); expect(f.controller.state?.result).toBe(final.decompositions!.at(-1)!.record);
    expect(f.controller.state?.anchor.analysis).toBe(f.anchor.analysis); expect(f.posts).toHaveLength(4);
    expect(JSON.stringify(f.controller.state?.result)).toBe(exact);
    expect(f.controller.state?.resultPresentation?.status).toBe(variant === 'available' ? 'available' : 'unavailable');
    const html = renderToStaticMarkup(createElement(DefinitionWorkspace, { state: f.controller.state!, onInspect() {}, onReturn() {}, onDetails() {} }));
    expect(html).toContain('Original clause'); expect(html).toContain('Selected clause'); expect(html).toContain('Definition check outcomes');
    expect(html).toContain('Exact result and surrounding scope'); expect(html).toContain('surrounding scope');
    if (variant === 'available') {
      expect(html).toContain('&lt;b&gt;same same&lt;/b&gt;'); expect(html).not.toContain('<b>same same</b>');
      expect(html).toContain(SOURCE_PRESENTATION_NOTE);
      expect(html.indexOf('Readable Lean result')).toBeLessThan(html.indexOf('<summary>Exact result and surrounding scope'));
    } else expect(html).toContain(variant === 'absent' ? 'not retained' : 'was rejected');
  });
  it('refuses a valid answer for a different focus path before exposing anything', () => {
    const f = prepare(), model = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (model.status !== 'available') throw Error(model.reason);
    const choice = model.occurrences[0]; f.controller.inspect(choice); f.controller.status(f.status('3'));
    const other = next(f.history, { kind: 'focus', path: ['appFun'] }, { status: 'candidate',
      result: { home: choice.home, term: (choice.term as JsonValue[])[1],
        type: ['forallE', name('x'), c('Nat'), c('Nat'), 'default'] }, checking: { status: 'completed' } });
    expect(f.controller.result(f.message(other, '3'))).toBe(true);
    expect(f.controller.state?.phase).toBe('unavailable'); expect(f.controller.state?.message).toContain('no longer matches');
    expect(f.posts).toHaveLength(3);
  });
  it('refuses a changed prior record even when its capture ID and chosen term and home are unchanged', () => {
    const f = prepare(), model = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (model.status !== 'available') throw Error(model.reason);
    const choice = model.occurrences[0]; f.controller.inspect(choice); f.controller.status(f.status('3'));
    const changedFirst = next(fixture().history, { kind: 'focus', path: [] }, { status: 'candidate',
      result: { home: choice.home, term: choice.term, type: c('ChangedType') }, checking: { status: 'completed' } });
    expect(changedFirst.attempts[0].record.captureId).toBe(f.history.attempts[0].record.captureId);
    expect(changedFirst.attempts[0].record).not.toEqual(f.history.attempts[0].record);
    const answer = f.message(next(changedFirst, { kind: 'focus', path: [] }), '3');
    expect(f.controller.result(answer)).toBe(true); expect(f.controller.state?.phase).toBe('unavailable');
    expect(f.controller.state?.message).toContain('previously retained'); expect(f.posts).toHaveLength(3);
    const safe = f.controller.retainedCapture; expect(safe).toBe(f.capture);
    // App can return and reopen using this exact accepted Result, even though a
    // different internally valid reply arrived while the operation was pending.
    f.controller.cancel(); f.controller.start(f.anchor, safe!);
    expect(f.controller.state?.phase).toBe('choosing'); expect(f.controller.retainedCapture).toBe(safe);
    expect(f.controller.state?.catalogue?.record).toBe(f.capture.decompositions![0].record);
  });
  it.each(['snapshot', 'occurrence', 'prior-snapshot', 'head-exposure'] as const)('refuses a changed retained %s attachment', kind => {
    const f = prepare(), model = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (model.status !== 'available') throw Error(model.reason);
    f.controller.inspect(model.occurrences[0]); f.controller.status(f.status('3'));
    const answer = clone(f.message(next(f.history, { kind: 'focus', path: [] }), '3'));
    if (kind === 'snapshot') o(answer.sourceSnapshot!.checking).reason = 'Changed retained snapshot report.';
    else if (kind === 'prior-snapshot') o(answer.decompositions![0].snapshot.checking).reason = 'Changed retained attempt snapshot report.';
    else if (kind === 'occurrence') answer.sourceOccurrence!.parentCaptureId = id(99);
    else o(answer).headExposure = { snapshot: f.f.snapshot as unknown as JsonValue,
      origin: origin(String(f.f.value.captureId)) as unknown as JsonValue, record: f.f.value };
    // The reply remains internally consistent. Cross-message retention is the
    // controller's responsibility, and cannot be inferred from capture IDs alone.
    expect(f.controller.result(parsed(answer))).toBe(true); expect(f.controller.state?.phase).toBe('unavailable');
    expect(f.controller.state?.message).toContain('previously retained'); expect(f.posts).toHaveLength(3);
  });
  it('gives independent input comparisons independent bounded work sessions', () => {
    const f = fixture(), large = clone(f.root);
    o(large.analysis.tree).lean = 'x'.repeat(1024 * 1024);
    const anchor = { ...f.anchor, analysis: clone(large.analysis) };
    for (let i = 0; i < 70; i++) expect(sameDefinitionWorkspaceInput(anchor, large)).toBe(true);
  });
  it('retains an explicit unavailable answer without scheduling another operation', () => {
    const f = prepare(), model = definitionOccurrences(f.controller.state!.catalogue!);
    if (model.status !== 'available') throw Error(model.reason);
    f.controller.inspect(model.occurrences[0]); f.controller.status(f.status('3'));
    const unavailable = parsed({ ...f.capture, requestId: '3', decompositionUnavailable: 'Operation unavailable in the current source.' });
    expect(f.controller.result(unavailable)).toBe(true); expect(f.controller.state?.phase).toBe('unavailable');
    expect(f.controller.state?.anchor.analysis).toBe(f.anchor.analysis); expect(f.posts).toHaveLength(3);
    expect(f.controller.retainedCapture).toBe(unavailable);
  });
  it('does not adopt unrequested extra records hidden behind an unavailable notice', () => {
    const f = prepare(), choices = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (choices.status !== 'available') throw Error(choices.reason);
    f.controller.inspect(choices.occurrences[0]); f.controller.status(f.status('3'));
    const extra = next(next(f.history, { kind: 'focus', path: [] }), { kind: 'typeComponent' });
    const reply = parsed({ ...f.message(extra, '3'), decompositionUnavailable: 'The requested record was not retained.' });
    expect(f.controller.result(reply)).toBe(true); expect(f.controller.state?.phase).toBe('unavailable');
    expect(f.controller.state?.message).toContain('unrequested'); expect(f.controller.retainedCapture).toBe(f.capture);
    expect(f.posts).toHaveLength(3);
  });
  // These capacity cases repeatedly validate the complete growing history through
  // three inspection/reopen cycles; allow shared CI runners time for all checks.
  it.each([1, 2])('reserves complete inspection pairs when reopening from %i retained attempts', initialAttempts => {
    const f = prepare(); let history = f.history, requestId = 4;
    if (initialAttempts === 2) {
      history = next(history, { kind: 'focus', path: [] }, undefined, 0);
      f.controller.cancel(); f.controller.start(f.anchor, f.message(history, '3'));
    }
    for (let cycle = 0; cycle < 3; cycle++) {
      expect(f.controller.state?.phase).toBe('choosing');
      const choices = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
      if (choices.status !== 'available') throw Error(choices.reason);
      f.controller.inspect(choices.occurrences[0]); expect(f.controller.state?.phase).toBe('focusing');
      history = next(history, { kind: 'focus', path: [] }, undefined, 0);
      const focused = f.message(history, String(requestId++)); f.controller.status(f.status(focused.requestId));
      expect(f.controller.result(focused)).toBe(true); expect(f.controller.state?.phase).toBe('exposing');
      history = next(history, { kind: 'expose', target: 'term' }, o(o(f.f.value.checking).exposure));
      const exposed = f.message(history, String(requestId++)); f.controller.status(f.status(exposed.requestId));
      expect(f.controller.result(exposed)).toBe(true); expect(f.controller.state?.phase).toBe('complete');
      expect(f.controller.retainedCapture).toBe(exposed);
      f.controller.cancel(); f.controller.start(f.anchor, exposed);
    }
    expect(history.attempts).toHaveLength(initialAttempts + 6);
    const posts = f.posts.length, safe = f.controller.retainedCapture;
    if (f.controller.state?.phase === 'choosing') {
      const choices = definitionOccurrences(f.controller.state.catalogue!, { filter: 'ForeignWrapper' });
      if (choices.status !== 'available') throw Error(choices.reason);
      f.controller.inspect(choices.occurrences[0]);
    }
    expect(f.controller.state?.phase).toBe('unavailable'); expect(f.controller.state?.message).toContain('Refresh');
    expect(f.posts).toHaveLength(posts); expect(f.controller.retainedCapture).toBe(safe);
    f.controller.cancel(); expect(f.controller.state).toBeNull();
  }, 20_000);
  it.each([false, true])('handles an associated host preflight refusal with changedAttachment=%s', changedAttachment => {
    const f = prepare(), choices = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (choices.status !== 'available') throw Error(choices.reason);
    f.controller.inspect(choices.occurrences[0]); f.controller.status(f.status('3'));
    const { analysis: _analysis, ...attachments } = clone(f.capture); void _analysis;
    if (changedAttachment) o(attachments.sourceSnapshot!.checking).reason = 'Different retained snapshot report.';
    const refused = parseEditorMessage({ ...attachments, type: 'statementlens.error', requestId: '3',
      message: 'Continuation refused.', decompositionUnavailable: 'The retained history has reached its limit. Refresh from the editor.' });
    if (refused?.type !== 'statementlens.error') throw Error('Invalid constructed refusal.');
    expect(f.controller.result(refused)).toBe(!changedAttachment); expect(f.posts).toHaveLength(3);
    if (changedAttachment) { expect(f.controller.state).toBeNull(); expect(f.controller.retainedCapture).toBeNull(); }
    else { expect(f.controller.state?.phase).toBe('unavailable'); expect(f.controller.state?.message).toContain('Refresh'); expect(f.controller.retainedCapture).toBe(f.capture); }
  });
  it('retains a properly associated stopped attempt for inspection', () => {
    const f = prepare(), choices = definitionOccurrences(f.controller.state!.catalogue!, { filter: 'ForeignWrapper' });
    if (choices.status !== 'available') throw Error(choices.reason);
    f.controller.inspect(choices.occurrences[0]); f.controller.status(f.status('3'));
    const answer = clone(f.message(next(f.history, { kind: 'focus', path: [] }), '3'));
    const check = answer.decompositions!.at(-1)!.record.checking;
    if (check.status !== 'captured') throw Error('Missing constructed checking.');
    const step = check.steps.at(-1)!;
    if (step.output.status !== 'candidate') throw Error('Missing constructed output.');
    step.output.checking = { status: 'error', reason: 'Checking interrupted.' }; step.replay = 'not-compared';
    check.stop = { status: 'unavailable', kind: 'error', phase: 'operation-checking', reason: 'Checking interrupted.' };
    const stopped = parsed(answer);
    expect(f.controller.result(stopped)).toBe(true); expect(f.controller.state?.phase).toBe('unavailable');
    expect(f.controller.retainedCapture).toBe(stopped); expect(f.posts).toHaveLength(3);
  });
  it('rejects cloned choices and cannot autochain after explicit pending cancellation', () => {
    const f = prepare(), model = definitionOccurrences(f.controller.state!.catalogue!);
    if (model.status !== 'available') throw Error(model.reason);
    f.controller.inspect(clone(model.occurrences[0])); expect(f.controller.state?.phase).toBe('unavailable'); expect(f.posts).toHaveLength(2);
    const pending = fixture(); pending.controller.start(pending.anchor); pending.controller.status(pending.status('1')); pending.controller.cancel();
    expect(pending.controller.result(pending.root)).toBe(false); expect(pending.posts).toHaveLength(1);
  });
});
