import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { chmod, mkdtemp, mkdir, readFile, realpath, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { analyzeEditorContext, positionOffset, resolveEditorProject, type EditorContextRequest } from './editor-context.js';
import { WorkerError } from './protocol.js';
import type { SourceSnapshotOrigin } from '../src/editor/source-origin.js';
import { validateSourceSnapshot, type SourceSnapshot } from '../src/editor/source-snapshot.js';
import { validateSourceOccurrence } from '../src/editor/source-occurrence.js';
import { validateSourceHeadExposure } from '../src/editor/source-head-exposure.js';
import { headExposureFixture } from '../src/editor/source-decomposition.test-fixtures.js';

test('editor coordinates use UTF-16, preserve CRLF and reject surrogate halves', () => {
  const source = 'α🧭\r\nπ = π\n';
  assert.equal(positionOffset(source, { line: 0, character: 3 }), 3);
  assert.equal(positionOffset(source, { line: 1, character: 4 }), 9);
  assert.throws(() => positionOffset(source, { line: 0, character: 2 }), /Unicode/);
  assert.throws(() => positionOffset(source, { line: 0, character: 4 }), /outside/);
  assert.throws(() => positionOffset(source, { line: 3, character: 0 }), /outside/);
});
test('trust refusal happens before source or engine filesystem access', async () => {
  await assert.rejects(analyzeEditorContext({ engineDirectory: '/nonexistent', fileName: '/nonexistent/Main.lean', source: 'True', selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } }, workspaceTrusted: false }), /Workspace Trust/);
});
test('project discovery reads standard and path dependency libraries without evaluating lakefile', async () => {
  const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-project-paths-'));
  try {
    const root = path.join(temporary, 'project');
    await mkdir(path.join(root, '.lake/build/lib/lean'), { recursive: true });
    await mkdir(path.join(temporary, 'dependency/.lake/build/lib/lean'), { recursive: true });
    await writeFile(path.join(root, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
    const lakefile = '-- This file must never be evaluated by project discovery.\n';
    await writeFile(path.join(root, 'lakefile.lean'), lakefile);
    await writeFile(path.join(root, 'lake-manifest.json'), JSON.stringify({ packages: [{ type: 'path', name: 'dependency', dir: '../dependency' }] }));
    const result = await resolveEditorProject(path.join(root, 'Main.lean'));
    assert.equal(result.libraries.length, 2);
    assert.ok(result.libraries[0]?.endsWith('/project/.lake/build/lib/lean'));
    assert.ok(result.libraries[1]?.endsWith('/dependency/.lake/build/lib/lean'));
    assert.equal(await readFile(path.join(root, 'lakefile.lean'), 'utf8'), lakefile);
    await writeFile(path.join(root, 'lean-toolchain'), 'leanprover/lean4:nightly\n');
    await assert.rejects(resolveEditorProject(path.join(root, 'Main.lean')), /requires leanprover\/lean4:v4.28.0/);
  } finally { await rm(temporary, { recursive: true, force: true }); }
});

const helperURL = new URL('../scripts/source-capture-dependency.mjs', import.meta.url).href;
const { buildFingerprint }: { buildFingerprint: (value: unknown) => string } = await import(helperURL);
const sha = (text: string) => createHash('sha256').update(text).digest('hex');

test('an incompatible guided response preserves independently validated raw captures', async () => {
  for (const marker of [undefined, 'unsupported']) {
    await syntheticContext(`response.ok = true; response.guidedContextContract = ${JSON.stringify(marker) ?? 'undefined'}; response.tree = {id:'old'}; response.expression = {};`, async request => {
      const result = await analyzeEditorContext(request);
      assert.equal(result.ok, false);
      assert.equal(result.code, 'EDITOR_COMPATIBILITY');
      assert.match(String(result.error), /Rebuild the matching checkout/);
      assert.equal(result.tree, undefined);
      assert.ok(result.sourceSnapshot);
      assert.ok(result.sourceSnapshotOrigin);
    });
  }
});

/** A controlled process tests host association only; it performs no Lean checks. */
async function syntheticContext(action: string, run: (request: EditorContextRequest, config: Record<string, unknown>) => Promise<void>, legacy = false, prepared = false) {
  const root = await realpath(await mkdtemp(path.join(os.tmpdir(), 'definograph-context-host-')));
  try {
    const project = path.join(root, 'project'), engine = path.join(root, 'engine');
    await mkdir(path.join(project, '.lake/build/lib/lean'), { recursive: true });
    await mkdir(path.join(engine, '.local'), { recursive: true });
    await writeFile(path.join(project, 'lean-toolchain'), 'leanprover/lean4:v4.28.0\n');
    const fileName = path.join(project, 'Main.lean');
    await writeFile(fileName, '-- Saved source must remain unchanged.\n');
    const configFile = path.join(engine, '.local/config.json');
    const executable = path.join(engine, '.local/statementlens-context');
    const body = `#!${process.execPath}
const fs = require('node:fs');
require('node:readline').createInterface({input:process.stdin}).once('line', line => {
  const input = JSON.parse(line);
  const unavailable = {status:'unavailable',kind:'prerequisite',phase:'test-process',reason:'No Lean checks run in this host control.'};
  const response = {ok:false,error:'Synthetic guided failure',diagnostics:[],sourceSnapshotOrigin:{forged:true},sourceSnapshot:{
    schema:'definograph.source-snapshot.v1',
    selection:{startByte:input.startByte,endByte:input.endByte,requestedStartByte:input.startByte,requestedEndByte:input.endByte,parentDeclaration:null},
    policy:{id:'named-source-v1',operation:'editor-source',preparation:'Lean.instantiateMVars',heartbeatBound:['nat','200000'],retainedMetadata:'definograph.raw.v1'},
    expectedType:{status:'absent'},original:{...unavailable},prepared:{...unavailable},checking:{...unavailable,attempted:false}
  }};
  if (${prepared}) {
    const frame = {schema:'definograph.raw-frame.v1',naturalProfile:2,originalDeclarations:[],
      sourceTerm:['const',['str',['anonymous'],'True'],[]],sourceType:['sort',['zero']]};
    response.sourceSnapshot.original = {status:'available',typeOrigin:'inferred',frame};
    response.sourceSnapshot.prepared = {status:'available',typeOrigin:'inferred-instantiated',frame,checkerUniverseParams:[]};
  }
  const configFile = ${JSON.stringify(configFile)};
  ${action}
  fs.writeFileSync(process.env.STATEMENTLENS_CONTEXT_RESULT, JSON.stringify(response));
});
`;
    await writeFile(executable, body); await chmod(executable, 0o700);
    const manifest = JSON.parse(await readFile(new URL('../vendor/DefinographCapture/UPSTREAM.json', import.meta.url), 'utf8'));
    const identity = { sourceCommit: manifest.sourceCommit, packageSha256: sha('test package'), leanVersion: 'Lean (version 4.28.0, test)', leanSha256: sha('test compiler'),
      artifacts: manifest.modules.map((entry: { module: string; sha256: string }) => ({ module: entry.module, sourceSha256: entry.sha256, oleanSha256: sha('test olean'), cSha256: sha('test C') })),
      adapter: { module: 'StatementLens.SourceSnapshot', sourceSha256: sha('test adapter'), oleanSha256: sha('test adapter olean'), cSha256: sha('test adapter C') },
      contextSourceSha256: sha('test context source'), contextCSha256: sha('test context C'), contextSha256: sha(body) };
    const config: Record<string, unknown> = { leanSysroot: root };
    if (!legacy) config.sourceCapture = { ...identity, buildFingerprint: buildFingerprint(identity), libraryPath: path.join(root, 'not-loaded-library') };
    await writeFile(configFile, JSON.stringify(config));
    const request: EditorContextRequest = { engineDirectory: engine, fileName, source: 'True', workspaceTrusted: true,
      selection: { start: { line: 0, character: 0 }, end: { line: 0, character: 4 } }, document: { uri: 'file:///controlled/Main.lean', version: 7 } };
    await run(request, config);
    assert.equal(await readFile(fileName, 'utf8'), '-- Saved source must remain unchanged.\n');
  } finally { await rm(root, { recursive: true, force: true }); }
}

test('source attachments survive guided failure and receive only actual host request/build metadata', async () => {
  await syntheticContext('response.testLibraryPath = process.env.LEAN_PATH;', async (request, config) => {
    const response = await analyzeEditorContext(request);
    assert.equal(response.ok, false);
    assert.ok(response.sourceSnapshot);
    const origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
    assert.equal(origin.kind, 'local-editor-process-snapshot');
    assert.equal(origin.sourceSha256, sha(request.source));
    assert.match(origin.captureId, /^[a-f0-9]{8}-[a-f0-9]{4}-4[a-f0-9]{3}-[89ab][a-f0-9]{3}-[a-f0-9]{12}$/);
    assert.deepEqual(origin.document, request.document);
    assert.deepEqual(origin.selection, request.selection);
    assert.equal(origin.engine.contextSha256, (config.sourceCapture as Record<string, unknown>).contextSha256);
    assert.equal(origin.project.dependencyTracking, 'snapshot-paths-only');
    assert.equal(response.testLibraryPath, path.join(origin.project.root, '.lake/build/lib/lean'));
    assert.ok(!String(response.testLibraryPath).includes('not-loaded-library'));
    assert.equal(Object.hasOwn(origin, 'forged'), false);
    assert.ok(Object.isFrozen(response) && Object.isFrozen(origin) && Object.isFrozen(response.sourceSnapshot));
    assert.equal(Object.isFrozen(request.document), false, 'retaining host metadata must not freeze the caller input');
    request.document!.version = 8;
    assert.equal(origin.document?.version, 7, 'retained metadata must not alias the next request');
    const next = await analyzeEditorContext({ ...request, document: { ...request.document!, version: 8 } });
    assert.notEqual((next.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId, origin.captureId);
    assert.equal((next.sourceSnapshotOrigin as SourceSnapshotOrigin).document?.version, 8);
  });
});

test('native source attachments must match requested and selected byte ranges', async () => {
  for (const action of [
    'response.sourceSnapshot.selection.requestedStartByte += 1;',
    'response.sourceSnapshot.selection.startByte += 1;',
    'response.sourceSnapshot.selection.endByte += 1;',
  ]) await syntheticContext(action, async request => {
    await assert.rejects(analyzeEditorContext(request), /selection|request|range/i);
  });
});

test('a response cannot supply source authority through a legacy engine or an origin-only field', async () => {
  await syntheticContext('', async request => {
    await assert.rejects(analyzeEditorContext(request), (error: unknown) => error instanceof WorkerError && error.code === 'EDITOR_PROTOCOL');
  }, true);
  await syntheticContext('delete response.sourceSnapshot;', async request => {
    const response = await analyzeEditorContext(request);
    assert.equal(Object.hasOwn(response, 'sourceSnapshotOrigin'), false);
  }, true);
});

test('configuration or executable replacement during a request refuses the completed response', async () => {
  for (const action of ['fs.appendFileSync(configFile, "\\n");', 'fs.appendFileSync(process.argv[1], "\\n");']) {
    await syntheticContext(action, async request => {
      await assert.rejects(analyzeEditorContext(request), (error: unknown) => error instanceof WorkerError && error.code === 'EDITOR_STALE');
    });
  }
});

test('cancelled source requests and invalid document revisions never return an attachment', async () => {
  await syntheticContext('', async request => {
    const cancellation = new AbortController(); cancellation.abort();
    await assert.rejects(analyzeEditorContext({ ...request, signal: cancellation.signal }),
      (error: unknown) => error instanceof WorkerError && error.code === 'CANCELLED');
    await assert.rejects(analyzeEditorContext({ ...request, document: { uri: 'file:///controlled/Main.lean', version: -1 } }),
      (error: unknown) => error instanceof WorkerError && error.code === 'EDITOR_SELECTION');
  });
});

// A transport-only follow-up: no declarations, receipts, or typing claims are
// fabricated. Native extraction itself is covered by the separate Lean suite.
const occurrenceReply = `if (input.occurrence) {
  response.sourceOccurrence = {schema:'definograph.source-occurrence.v1',captureId:input.captureId,
    parentCaptureId:input.occurrence.parentCaptureId,path:input.occurrence.path,
    policy:{id:'named-extraction-v1',operation:'editor-occurrence',preparation:'Lean.instantiateMVars',heartbeatBound:['nat','200000'],retainedMetadata:'definograph.raw.v1'},
    checking:{...unavailable,phase:'occurrence-capture',attempted:false}};
  response.testOccurrence = input.occurrence;
}`;
async function parentRequest(request: EditorContextRequest): Promise<EditorContextRequest> {
  const result = await analyzeEditorContext(request);
  return { ...request, occurrence: { snapshot: result.sourceSnapshot as SourceSnapshot,
    origin: result.sourceSnapshotOrigin as SourceSnapshotOrigin, path: [] } };
}
test('occurrence follow-up uses a fresh capture and exact retained input without pre-resolving the path', async () => {
  await syntheticContext(occurrenceReply, async request => {
    const followup = await parentRequest(request), parent = followup.occurrence!;
    for (const path of [[], ['appArg']] as const) {
      const response = await analyzeEditorContext({ ...followup, occurrence: { ...parent, path: [...path] } });
      const sent = response.testOccurrence as Record<string, unknown>;
      assert.deepEqual(Object.keys(sent).sort(), ['parentCaptureId', 'path', 'prepared', 'schema', 'selection']);
      assert.equal(sent.schema, 'definograph.source-occurrence-request.v1');
      assert.equal(sent.parentCaptureId, parent.origin.captureId);
      assert.deepEqual(sent.path, path);
      assert.deepEqual(JSON.parse(JSON.stringify(sent.prepared)), JSON.parse(JSON.stringify(parent.snapshot.prepared)));
      assert.deepEqual(JSON.parse(JSON.stringify(sent.selection)), JSON.parse(JSON.stringify(parent.snapshot.selection)));
      const occurrence = response.sourceOccurrence as {captureId:string;parentCaptureId:string};
      assert.notEqual(occurrence.captureId, parent.origin.captureId);
      assert.equal(occurrence.captureId, (response.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId);
      assert.equal(occurrence.parentCaptureId, parent.origin.captureId);
      assert.equal(response.ok, false, 'guided failure preserves occurrence data');
      assert.ok(Object.isFrozen(response.sourceOccurrence));
    }
  }, false, true);
});
test('stale document, source, selection, engine and project parents are refused before another process', async () => {
  await syntheticContext("fs.appendFileSync(process.argv[1] + '.runs', 'x');" + occurrenceReply, async request => {
    const followup = await parentRequest(request);
    const changes: ((value: EditorContextRequest) => void)[] = [
      value => { value.source = 'False'; },
      value => { value.document!.version++; },
      value => { value.document!.uri += '-other'; },
      value => { value.selection.end.character = 3; },
      value => { value.occurrence!.origin.engine.contextSha256 = '0'.repeat(64); },
      value => { value.occurrence!.origin.project.libraryPaths = []; },
      value => { value.occurrence!.origin.project.root += '-other'; },
      value => { value.occurrence!.snapshot.selection.endByte = 3; },
      value => { value.occurrence!.path = ['notAnEdge' as never]; },
      value => { value.occurrence!.path = Array(65).fill('appArg'); },
    ];
    for (const change of changes) {
      const changed = { ...structuredClone(followup), occurrence: structuredClone(followup.occurrence) }; change(changed);
      await assert.rejects(analyzeEditorContext(changed), change.toString());
    }
    const aborted = new AbortController(); aborted.abort();
    await assert.rejects(analyzeEditorContext({ ...followup, signal: aborted.signal }), /cancelled/);
    assert.equal(await readFile(path.join(request.engineDirectory, '.local/statementlens-context.runs'), 'utf8'), 'x');
  }, false, true);
});
test('fresh parent mismatch is retained only when extraction did not begin', async () => {
  for (const attempted of [false, true]) await syntheticContext(occurrenceReply + `if(input.occurrence) {
    response.sourceOccurrence.checking.phase='parent-match';response.sourceOccurrence.checking.attempted=${attempted};
  }`, async request => {
    const followup = await parentRequest(request);
    const changed = structuredClone(followup);
    assert.equal(changed.occurrence!.snapshot.prepared.status, 'available');
    if (changed.occurrence!.snapshot.prepared.status === 'available') changed.occurrence!.snapshot.prepared.frame.sourceTerm = ['const', ['str', ['anonymous'], 'False'], []];
    if (attempted) await assert.rejects(analyzeEditorContext(changed), /changed prepared parent|parent-match/);
    else {
      const response = await analyzeEditorContext(changed);
      assert.equal((response.sourceOccurrence as {checking:{phase:string}}).checking.phase, 'parent-match');
      assert.ok(response.sourceSnapshot, 'fresh raw source remains available after parent mismatch');
    }
  }, false, true);
});
test('occurrence responses cannot change parent, capture or path, or arrive unrequested', async () => {
  for (const mutation of [
    "response.sourceOccurrence.parentCaptureId='550e8400-e29b-41d4-a716-446655440000';",
    "response.sourceOccurrence.captureId=input.occurrence.parentCaptureId;",
    "response.sourceOccurrence.path=['appFun'];",
    'delete response.sourceOccurrence;',
    'delete response.sourceSnapshot;',
  ]) await syntheticContext(occurrenceReply + `if(input.occurrence) {${mutation}}`, async request => {
    await assert.rejects(analyzeEditorContext(await parentRequest(request)), /occurrence|snapshot/i);
  }, false, true);
  await syntheticContext("response.sourceOccurrenceUnavailable='unrequested';", async request => {
    await assert.rejects(analyzeEditorContext(request), /unrequested/);
  });
});
test('bounded occurrence omission survives independent source omission, while ambiguous omissions are refused', async () => {
  for (const malformed of [false, true]) await syntheticContext(occurrenceReply + `if(input.occurrence) {
    ${malformed ? '' : 'delete response.sourceOccurrence; delete response.sourceSnapshot;'}
    response.sourceOccurrenceUnavailable='No occurrence record was produced.';
  }`, async request => {
    const followup = await parentRequest(request);
    if (malformed) await assert.rejects(analyzeEditorContext(followup), /omission/);
    else assert.equal((await analyzeEditorContext(followup)).sourceOccurrenceUnavailable, 'No occurrence record was produced.');
  }, false, true);
});


/** Synthetic receipt data exist only to exercise host retention/correlation.
 * This controlled process performs no Lean checking or definition exposure. */
async function headParentRequest(request: EditorContextRequest): Promise<EditorContextRequest> {
  const response = await analyzeEditorContext(request);
  const snapshot = response.sourceSnapshot as SourceSnapshot, origin = response.sourceSnapshotOrigin as SourceSnapshotOrigin;
  assert.equal(snapshot.prepared.status, 'available');
  if (snapshot.prepared.status !== 'available') throw new Error('Missing synthetic prepared frame.');
  const name = (part: string, parent: unknown = ['anonymous']): unknown => ['str', parent, part];
  const constant = (part: string): unknown => ['const', part.split('.').reduce((p, part) => name(part, p), ['anonymous'] as unknown), []];
  const prefix = name(origin.captureId, name('SourceOccurrence', name('StatementLens')));
  const checks: unknown[] = [], audits: unknown[] = [];
  for (const base of [name('source', prefix), name('root', name('extraction', prefix)), name('selected', name('extraction', prefix))]) {
    for (const label of ['context', 'component']) {
      const id = checks.length, component = label === 'component', declaredName = name(label, base);
      const declaration = { kind: component ? 'defnDecl' : 'thmDecl', name: declaredName, levelParams: [],
        type: component ? ['sort', ['zero']] : constant('True'), value: component ? constant('True') : constant('True.intro'), all: [declaredName],
        ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
      checks.push({ id, pair: 'editor-occurrence', label, displayLabel: label, declaration,
        subject: { attempt: origin.captureId, pair: 'editor-occurrence', sequence: id, target: label, declaration },
        envBefore: id, envAfter: id + 1, heartbeatBound: ['nat', '200000'], outcome: { tag: 'accepted' } });
      audits.push({ checkId: id, subject: declaration, environment: id + 1, category: 'declarationCheck', result: { tag: 'available', axioms: [] } });
    }
  }
  const frame = snapshot.prepared.frame;
  const occurrence = validateSourceOccurrence({ schema: 'definograph.source-occurrence.v1', parentCaptureId: '550e8400-e29b-41d4-a716-446655440000', captureId: origin.captureId, path: [],
    policy: { id: 'named-extraction-v1', operation: 'editor-occurrence', preparation: 'Lean.instantiateMVars', heartbeatBound: ['nat', '200000'], retainedMetadata: 'definograph.raw.v1' },
    checking: { status: 'captured', action: { status: 'completed' }, binding: { schema: 3, naturalProfile: 2, rawProfile: 'definograph.raw.v1',
      attempt: origin.captureId, operation: 'editor-occurrence', sourceKind: 'namedExtraction', declarationPrefix: prefix, universeParams: [], initialEnvironment: 0,
      context: { arity: 0, telescope: ['nil'], registry: [], registryOrder: 'mostRecentFirst', originalDeclarations: [], originalDeclarationOrder: 'oldestFirst' },
      sourceTerm: frame.sourceTerm, sourceType: frame.sourceType, positionalTerm: frame.sourceTerm, positionalType: frame.sourceType, path: [] },
      selected: { home: { arity: 0, telescope: ['nil'] }, term: frame.sourceTerm, type: frame.sourceType }, checks, audits, environmentSnapshotCount: 7 } }, snapshot);
  return { ...request, headExposure: { snapshot, origin, occurrence, target: 'term' } };
}
const headExposureReply = `if (input.headExposure) {
  response.sourceHeadExposure = {schema:'definograph.source-head-exposure.v1',captureId:input.captureId,
    parentCaptureId:input.headExposure.parentCaptureId,path:input.headExposure.path,target:input.headExposure.target,
    policy:{id:'safe-definition-head-v1',operation:'editor-head-exposure',preparation:'Lean.instantiateMVars',universeSubstitution:'structural',reduction:'original-lambda-spine',heartbeatBound:['nat','200000'],retainedMetadata:'definograph.raw.v1'},
    checking:{...unavailable,phase:'head-exposure-capture',attempted:false}};
  response.testHeadExposure=input.headExposure;
}`;
test('definition-head requests preserve their original parent and send exact comparison data to a fresh process', async () => {
  await syntheticContext(headExposureReply, async request => {
    const followup = await headParentRequest(request), original = JSON.stringify(followup.headExposure);
    for (const target of ['term', 'type'] as const) {
      const result = await analyzeEditorContext({ ...followup, headExposure: { ...followup.headExposure!, target } });
      const sent = result.testHeadExposure as Record<string, unknown>;
      assert.deepEqual(Object.keys(sent).sort(), ['expectedSelected', 'parentCaptureId', 'path', 'prepared', 'schema', 'selection', 'target']);
      assert.equal(sent.target, target); assert.equal(sent.schema, 'definograph.source-head-exposure-request.v1');
      const parentChecking = followup.headExposure!.occurrence.checking;
      assert.equal(parentChecking.status, 'captured');
      if (parentChecking.status === 'captured') assert.deepEqual(JSON.parse(JSON.stringify(sent.expectedSelected)), JSON.parse(JSON.stringify(parentChecking.selected)));
      assert.equal((result.sourceHeadExposure as { captureId: string }).captureId, (result.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId);
      assert.notEqual((result.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId, followup.headExposure!.origin.captureId);
      assert.equal(result.ok, false, 'legacy guided failure does not discard explicit exposure refusal');
      assert.ok(Object.isFrozen(result.sourceHeadExposure));
    }
    assert.equal(JSON.stringify(followup.headExposure), original);
  }, false, true);
});
test('invalid or stale exposure parents and simultaneous operations are refused before a second process', async () => {
  await syntheticContext("fs.appendFileSync(process.argv[1] + '.runs', 'x');" + headExposureReply, async request => {
    const followup = await headParentRequest(request);
    for (const change of [
      (v: EditorContextRequest) => { v.source += ' '; },
      (v: EditorContextRequest) => { v.document!.version++; },
      (v: EditorContextRequest) => { v.headExposure!.origin.engine.contextSha256 = '0'.repeat(64); },
      (v: EditorContextRequest) => { v.headExposure!.origin.captureId = '550e8400-e29b-41d4-a716-446655440000'; },
      (v: EditorContextRequest) => { v.headExposure!.target = 'before' as never; },
      (v: EditorContextRequest) => { v.occurrence = { snapshot: v.headExposure!.snapshot, origin: v.headExposure!.origin, path: [] }; },
    ]) {
      const changed = structuredClone(followup); change(changed); await assert.rejects(analyzeEditorContext(changed));
    }
    assert.equal(await readFile(path.join(request.engineDirectory, '.local/statementlens-context.runs'), 'utf8'), 'x');
  }, false, true);
});
test('definition-head response identity, target, parent and attachment presence must match the request', async () => {
  for (const mutation of [
    "response.sourceHeadExposure.parentCaptureId='550e8400-e29b-41d4-a716-446655440000';",
    'response.sourceHeadExposure.captureId=input.headExposure.parentCaptureId;',
    "response.sourceHeadExposure.path=['appFun'];", "response.sourceHeadExposure.target='type';",
    'delete response.sourceHeadExposure;', 'delete response.sourceSnapshot;',
    "response.sourceHeadExposureUnavailable='ambiguous';",
  ]) await syntheticContext(headExposureReply + `if(input.headExposure){${mutation}}`, async request => {
    await assert.rejects(analyzeEditorContext(await headParentRequest(request)));
  }, false, true);
  await syntheticContext("response.sourceHeadExposureUnavailable='unrequested';", async request => {
    await assert.rejects(analyzeEditorContext(request), /unrequested/);
  });
});
test('changed fresh frames allow only an explicit unattempted parent-match refusal', async () => {
  for (const attempted of [false, true]) await syntheticContext(headExposureReply + `if(input.headExposure){
    response.sourceSnapshot.prepared.frame.sourceTerm=['const',['str',['anonymous'],'False'],[]];
    response.sourceHeadExposure.checking={...unavailable,phase:'parent-match',attempted:${attempted}};
  }`, async request => {
    const followup = await headParentRequest(request);
    if (attempted) await assert.rejects(analyzeEditorContext(followup), /changed prepared parent/);
    else assert.equal((await analyzeEditorContext(followup)).sourceHeadExposure !== undefined, true);
  }, false, true);
});
test('complete head-exposure omission can survive independent source omission', async () => {
  await syntheticContext(headExposureReply + `if(input.headExposure){
    delete response.sourceHeadExposure;delete response.sourceSnapshot;
    response.sourceHeadExposureUnavailable='No complete exposure record was produced.';
  }`, async request => {
    assert.equal((await analyzeEditorContext(await headParentRequest(request))).sourceHeadExposureUnavailable, 'No complete exposure record was produced.');
  }, false, true);
});

/** All parent receipts in these transport controls are synthetic test data.
 * Actual Lean replay/typing is exercised by source-decomposition-integration. */
async function decompositionParentRequest(request: EditorContextRequest): Promise<EditorContextRequest> {
  const first = await analyzeEditorContext(request);
  const origin = first.sourceSnapshotOrigin as SourceSnapshotOrigin;
  const original = headExposureFixture();
  const fixture = JSON.parse(JSON.stringify(original).replaceAll(original.parent.occurrence.captureId, origin.captureId)) as typeof original;
  const snapshot = validateSourceSnapshot({ ...fixture.parent.snapshot, selection: (first.sourceSnapshot as SourceSnapshot).selection });
  const occurrence = validateSourceOccurrence(fixture.parent.occurrence, snapshot);
  const record = validateSourceHeadExposure(fixture.value, snapshot, { snapshot, occurrence });
  return { ...request, decomposition: { snapshot, origin, occurrence,
    seed: { snapshot, origin: { ...origin, captureId: record.captureId }, record }, attempts: [],
    previousCaptureId: record.captureId, parentStepIndex: 0, operation: { kind: 'focus', path: [] } } };
}
const decompositionReply = `if(input.decomposition){
  response.sourceSnapshot = ${JSON.stringify(headExposureFixture().snapshot)};
  response.sourceSnapshot.selection = input.decomposition.selection;
  response.sourceDecomposition = {schema:'definograph.source-decomposition.v1',captureId:input.captureId,
    parentCaptureId:input.decomposition.parentCaptureId,previousCaptureId:input.decomposition.previousCaptureId,
    parentStepIndex:input.decomposition.parentStepIndex,path:input.decomposition.path,operations:input.decomposition.operations,
    policy:{id:'bounded-decomposition-v1',operation:'editor-decomposition',preparation:'Lean.instantiateMVars',universeSubstitution:'structural',reduction:'original-lambda-spine',heartbeatBound:['nat','200000'],retainedMetadata:'definograph.raw.v1',maxOperations:8},
    checking:{...unavailable,phase:'decomposition-capture',attempted:false}};
  if(input.decomposition.schema.endsWith('.v2')) {
    response.sourceDecomposition.schema='definograph.source-decomposition.v2';
    Object.assign(response.sourceDecomposition.policy,{id:'bounded-decomposition-v2',operation:'editor-decomposition-v2',maxChecks:30,maxFields:16});
  }
  response.testDecomposition = input.decomposition;
}`;
test('decomposition sends only a host-resolved exact prefix and one fresh operation', async () => {
  await syntheticContext(decompositionReply, async request => {
    const followup = await decompositionParentRequest(request), bytes = JSON.stringify(followup.decomposition);
    const result = await analyzeEditorContext(followup);
    const sent = result.testDecomposition as Record<string, unknown>;
    assert.deepEqual(Object.keys(sent).sort(), ['expectedHistory','expectedSelected','operations','parentCaptureId','parentStepIndex','path','prepared','previousCaptureId','schema','selection']);
    assert.equal(sent.schema, 'definograph.source-decomposition-request.v1');
    assert.deepEqual(sent.operations, [{kind:'expose',target:'term'},{kind:'focus',path:[]}]);
    assert.equal((sent.expectedHistory as unknown[]).length, 1);
    assert.equal(Object.hasOwn((sent.expectedHistory as Record<string, unknown>[])[0]!, 'checks'), false);
    assert.equal(JSON.stringify(followup.decomposition), bytes);
    assert.notEqual((result.sourceSnapshotOrigin as SourceSnapshotOrigin).captureId, followup.decomposition!.previousCaptureId);
    assert.ok(Object.isFrozen(result.sourceDecomposition));
    assert.equal(result.ok, false, 'legacy guided failure does not erase the retained operation boundary');
  });
});
test('invalid or stale decomposition ancestry is rejected before another process starts', async () => {
  await syntheticContext("fs.appendFileSync(process.argv[1] + '.runs','x');" + decompositionReply, async request => {
    const parent = await decompositionParentRequest(request);
    const mutations: ((r: EditorContextRequest) => void)[] = [
      r => { r.decomposition!.previousCaptureId = '550e8400-e29b-41d4-a716-446655440099'; },
      r => { r.decomposition!.parentStepIndex = 1; },
      r => { r.decomposition!.operation = { kind: 'expose', target: 'term' }; },
      r => { r.decomposition!.operation = { kind: 'focus', path: ['notAnEdge' as never] }; },
      r => { r.decomposition!.operation = { kind: 'focus', path: ['lamBody'] }; },
      r => { Object.assign(r.decomposition!.operation, { expectedType: ['sort', ['zero']] }); },
      r => { r.decomposition!.seed!.origin.document!.version++; },
      r => { r.decomposition!.seed!.origin.captureId = r.decomposition!.origin.captureId; },
      r => { r.decomposition!.seed!.origin.engine.contextSha256 = '0'.repeat(64); },
      r => { r.document!.version++; },
      r => { r.source += '\n'; },
      r => { r.occurrence = { snapshot: r.decomposition!.snapshot, origin: r.decomposition!.origin, path: [] }; },
    ];
    const runFile = path.join(request.engineDirectory, '.local/statementlens-context.runs');
    const initial = await readFile(runFile, 'utf8');
    for (const mutate of mutations) { const changed = structuredClone(parent); mutate(changed); await assert.rejects(analyzeEditorContext(changed)); }
    assert.equal(await readFile(runFile, 'utf8'), initial);
  });
});
test('decomposition responses must match the exact requested IDs, stage and recipe', async () => {
  for (const mutation of [
    "response.sourceDecomposition.previousCaptureId='550e8400-e29b-41d4-a716-446655440099';",
    'response.sourceDecomposition.parentStepIndex=1;',
    'response.sourceDecomposition.captureId=input.decomposition.previousCaptureId;',
    "response.sourceDecomposition.operations[1].path=['appArg'];",
    'delete response.sourceDecomposition;', 'delete response.sourceSnapshot;',
    "response.sourceDecompositionUnavailable='ambiguous';",
  ]) await syntheticContext(decompositionReply + `if(input.decomposition){${mutation}}`, async request => {
    await assert.rejects(analyzeEditorContext(await decompositionParentRequest(request)));
  });
  await syntheticContext("response.sourceDecompositionUnavailable='unrequested';", async request => {
    await assert.rejects(analyzeEditorContext(request), /unrequested/);
  });
});
test('decomposition changed-parent refusal and complete omission retain their explicit boundary', async () => {
  for (const attempted of [false, true]) await syntheticContext(decompositionReply + `if(input.decomposition){
    response.sourceSnapshot.prepared.frame.sourceTerm=['const',['str',['anonymous'],'False'],[]];
    response.sourceDecomposition.checking={...unavailable,phase:'parent-match',attempted:${attempted}};
  }`, async request => {
    const followup = await decompositionParentRequest(request);
    if (attempted) await assert.rejects(analyzeEditorContext(followup), /changed prepared parent/);
    else assert.ok((await analyzeEditorContext(followup)).sourceDecomposition);
  });
  await syntheticContext(decompositionReply + `if(input.decomposition){
    delete response.sourceSnapshot;delete response.sourceDecomposition;
    response.sourceDecompositionUnavailable='No complete decomposition record was produced.';
  }`, async request => {
    assert.equal((await analyzeEditorContext(await decompositionParentRequest(request))).sourceDecompositionUnavailable, 'No complete decomposition record was produced.');
  });
});

test('v2 begins at the exact original pair without a legacy seed', async () => {
  await syntheticContext(decompositionReply, async request => {
    const followup = await decompositionParentRequest(request), d = followup.decomposition!;
    d.version = 2; d.seed = null; d.previousCaptureId = d.occurrence.captureId; d.operation = { kind: 'fields' };
    const result = await analyzeEditorContext(followup), sent = result.testDecomposition as Record<string, unknown>;
    assert.equal(sent.schema, 'definograph.source-decomposition-request.v2');
    assert.deepEqual(sent.operations, [{ kind: 'fields' }]); assert.deepEqual(sent.expectedHistory, []);
    assert.equal(sent.parentStepIndex, 0); assert.equal(sent.previousCaptureId, sent.parentCaptureId);
    for (const mutate of [
      (value: typeof d) => { value.version = 1; },
      (value: typeof d) => { value.parentStepIndex = 1; },
      (value: typeof d) => { value.operation = { kind: 'project', index: 0 }; },
    ]) { const changed = structuredClone(followup); mutate(changed.decomposition!); await assert.rejects(analyzeEditorContext(changed)); }
  });
});
