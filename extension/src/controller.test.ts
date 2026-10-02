import { GUIDED_CONTEXT_CONTRACT } from '../../src/editor/guided-context-contract.js';
import { test } from 'node:test';
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { build } from 'esbuild';
import { mkdtemp, mkdir, rm, writeFile } from 'node:fs/promises';
import { createRequire } from 'node:module';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import vm from 'node:vm';
const nativeRequire = createRequire(import.meta.url);
const entry = fileURLToPath(new URL('./extension.ts', import.meta.url));
class Range {
  start: {line:number;character:number}; end: {line:number;character:number};
  constructor(a:any,b:any,c?:number,d?:number) { this.start = typeof a === 'number' ? {line:a,character:b} : a; this.end = typeof a === 'number' ? {line:c!,character:d!} : b; }
  isEqual(other: Range) { return JSON.stringify(this) === JSON.stringify(other); }
}
const tick = () => new Promise(resolve => setTimeout(resolve, 5));
test('extension controller orders host messages, cancels stale analysis, and guards reveal races', async () => {
  const engine = await mkdtemp(path.join(os.tmpdir(), 'statementlens-extension-test-'));
  try {
    await mkdir(path.join(engine, 'dist'));
    await writeFile(path.join(engine, 'dist/index.html'), '<html><head></head><body><script type="module" src="./assets/app.js"></script></body></html>');
    let configuredEngine = engine;
    const pending: {request:any;resolve:(value:any)=>void}[] = [];
    const commands = new Map<string,()=>Promise<void>>();
    const listeners: Record<string,Function> = {};
    const messages: any[] = [];
    const errors: string[] = [];
    let receiver: (value:any)=>Promise<void>;
    let disposePanel: ()=>void;
    let reveals = 0;
    const makeDocument = (name:string) => ({uri:{scheme:'file',toString:()=>`file://${engine}/${name}`},fileName:`${engine}/${name}`,languageId:'lean4',version:1,isDirty:false,getText:()=> 'example : True := True.intro',validateRange:(range:Range)=>range});
    const a = makeDocument('A.lean'), b = makeDocument('B.lean');
    const firstSelection = new Range(0,10,0,14);
    const editorA = {document:a,selection:firstSelection,revealRange:()=>{reveals++;}};
    const editorB = {document:b,selection:new Range(0,11,0,15),revealRange:()=>{reveals++;}};
    const panel:any = {webview:{html:'',cspSource:'vscode-resource:',asWebviewUri:(uri:any)=>({toString:()=>`vscode-resource:${uri.fsPath}`}),postMessage:(message:any)=>{messages.push(message);return Promise.resolve(true);},onDidReceiveMessage:(fn:any)=>{receiver=fn;return{dispose(){}};}},reveal(){},onDidDispose:(fn:any)=>{disposePanel=fn;return{dispose(){}};},dispose(){disposePanel?.();}};
    let showDocument: (doc:any)=>Promise<any> = async doc => doc === a ? editorA : editorB;
    const vscode:any = {
      Range, Selection:Range, ViewColumn:{Beside:2,One:1}, TextEditorRevealType:{InCenterIfOutsideViewport:1}, Uri:{file:(fsPath:string)=>({fsPath})},
      commands:{registerCommand:(name:string,fn:any)=>{commands.set(name,fn);return{dispose(){}};}},
      workspace:{isTrusted:true,textDocuments:[a,b],getWorkspaceFolder:()=>({uri:{toString:()=>engine}}),getConfiguration:()=>({get:(name:string,fallback:any)=>name==='engineDirectory'?configuredEngine:fallback}),onDidChangeTextDocument:(fn:any)=>{listeners.change=fn;return{dispose(){}};},onDidCloseTextDocument:(fn:any)=>{listeners.close=fn;return{dispose(){}};},onDidChangeConfiguration:(fn:any)=>{listeners.config=fn;return{dispose(){}};}},
      window:{activeTextEditor:editorA,visibleTextEditors:[editorA],createWebviewPanel:()=>panel,showErrorMessage:(message:string)=>{errors.push(message);},showTextDocument:(doc:any)=>showDocument(doc),onDidChangeTextEditorSelection:(fn:any)=>{listeners.selection=fn;return{dispose(){}};}},
    };
    const bundled = await build({entryPoints:[entry],bundle:true,write:false,platform:'node',format:'cjs',external:['vscode'],plugins:[{name:'bounded-adapter-test',setup(api){api.onResolve({filter:/server\/editor-context\.js$/},()=>({path:'context-adapter',namespace:'fixture'}));api.onLoad({filter:/.*/,namespace:'fixture'},()=>({contents:'export const analyzeEditorContext = globalThis.__analyze;',loader:'js'}));}}]});
    const module = {exports:{} as any};
    const sandbox = vm.createContext({module,exports:module.exports,require:(name:string)=>name==='vscode'?vscode:nativeRequire(name),Buffer,process,AbortController,structuredClone,TextEncoder,TextDecoder,__analyze:(request:any)=>new Promise(resolve=>pending.push({request,resolve})),__fixture:''});
    vm.runInContext(bundled.outputFiles[0]!.text, sandbox);
    const intoContext = (value:any) => { sandbox.__fixture = JSON.stringify(value); return vm.runInContext('JSON.parse(__fixture)', sandbox); };
    const context = {extensionPath:path.join(engine,'extension'),subscriptions:[]};
    module.exports.activate(context);
    const command = commands.get('statementLens.visualizeSelection')!;
    await command();
    assert.match(panel.webview.html,/Content-Security-Policy/);
    assert.match(panel.webview.html,/vscode-resource:.*assets\/app.js/);
    await receiver!({type:'statementlens.ready'});
    await writeFile(path.join(engine, 'dist/index.html'), '<html><head></head><body>rebuilt-after-missing-contract<script type="module" src="./assets/app.js"></script></body></html>');
    await command(); // A new command must load rebuilt assets after a rejected panel.
    assert.match(panel.webview.html,/rebuilt-after-missing-contract/);
    await receiver!({type:'statementlens.ready',guidedContextContract:'unsupported'});
    await writeFile(path.join(engine, 'dist/index.html'), '<html><head></head><body>rebuilt-after-unsupported-contract<script type="module" src="./assets/app.js"></script></body></html>');
    await command();
    assert.match(panel.webview.html,/rebuilt-after-unsupported-contract/);
    assert.equal(pending.length,0,'incompatible browser must not start native analysis');
    assert.equal(errors.length,2);
    assert.ok(errors.every(error=>error.includes('incompatible guided context')));
    const ready = receiver!({type:'statementlens.ready',guidedContextContract:GUIDED_CONTEXT_CONTRACT}); await tick();
    assert.equal(messages.at(-1).phase,'analyzing');
    const oldRequest = pending.shift()!;
    a.version = 2; listeners.change!({document:a,contentChanges:[{}]});
    assert.equal(oldRequest.request.signal.aborted,true);
    assert.equal(messages.at(-1).phase,'stale');
    oldRequest.resolve({ok:true,diagnostics:[]}); await ready;
    assert.equal(messages.filter(message=>message.type==='statementlens.analysis').length,0);
    editorA.selection = new Range(0,9,0,13);
    const refresh = receiver!({type:'statementlens.refresh',expansion:{constants:['Custom'],maxDepth:2}}); await tick();
    const fresh = pending.shift()!;
    assert.equal(fresh.request.selection.start.character,9);
    assert.deepEqual(JSON.parse(JSON.stringify(fresh.request.expansion)),{constants:['Custom'],maxDepth:2});
    fresh.resolve({ok:true,diagnostics:[]}); await refresh;
    assert.equal(messages.at(-1).type,'statementlens.analysis');
    assert.equal(messages.at(-1).document.version,2);
    assert.equal(fresh.request.document.uri, a.uri.toString());
    assert.equal(fresh.request.document.version, 2);
    editorA.selection = new Range(0,10,0,14); listeners.selection!({textEditor:editorA});
    assert.equal(messages.at(-1).phase,'stale','selection changes clear the source/check attachment');
    const failedReading = receiver!({type:'statementlens.refresh'}); await tick();
    const retained = pending.shift()!;
    const snapshot = {schema:'control-only-snapshot'}, origin = {kind:'control-only-origin'};
    retained.resolve({ok:false,error:'guided export failed',diagnostics:[],sourceSnapshot:snapshot,sourceSnapshotOrigin:origin}); await failedReading;
    assert.equal(messages.at(-1).type,'statementlens.error');
    assert.deepEqual(messages.at(-1).sourceSnapshot,snapshot,'source survives a guided view failure');
    assert.equal(messages.at(-1).source,a.getText());
    const sourceResult = (request:any, captureId:string) => {
      const unavailable = {status:'unavailable',kind:'prerequisite',phase:'control',reason:'No Lean checking in the controller test.'};
      const frame = {schema:'definograph.raw-frame.v1',naturalProfile:2,originalDeclarations:[],sourceTerm:['const',['str',['anonymous'],'True'],[]],sourceType:['sort',['zero']]};
      return intoContext({ok:false,error:'guided control failure',diagnostics:[],sourceSnapshot:{schema:'definograph.source-snapshot.v1',
        selection:{startByte:10,endByte:14,requestedStartByte:10,requestedEndByte:14,parentDeclaration:null},
        policy:{id:'named-source-v1',operation:'editor-source',preparation:'Lean.instantiateMVars',heartbeatBound:['nat','200000'],retainedMetadata:'definograph.raw.v1'},
        expectedType:{status:'absent'},original:{status:'available',typeOrigin:'inferred',frame},prepared:{status:'available',typeOrigin:'inferred-instantiated',frame,checkerUniverseParams:[]},checking:{...unavailable,attempted:false}},
        sourceSnapshotOrigin:{kind:'local-editor-process-snapshot',captureId,sourceSha256:createHash('sha256').update(request.source).digest('hex'),
          engine:{contextSha256:'1'.repeat(64),buildFingerprint:'2'.repeat(64),packageSha256:'3'.repeat(64),leanSha256:'4'.repeat(64)},
          project:{root:engine,toolchain:'v4.28.0',libraryPaths:[],dependencyTracking:'snapshot-paths-only'},document:request.document,selection:request.selection,policyId:'named-source-v1'}});
    };
    const parentId = '550e8400-e29b-41d4-a716-446655440000';
    const establishParent = async () => {
      const call = receiver!({type:'statementlens.refresh'}); await tick();
      const current = pending.shift()!, result = sourceResult(current.request,parentId);
      current.resolve(result); await call; return {current,result};
    };
    const parent = await establishParent();
    const occurrenceCommand = {type:'statementlens.checkOccurrence',parentCaptureId:parentId,path:['appArg']};
    const errorCount = errors.length;
    for (const invalid of [
      {...occurrenceCommand,parentCaptureId:'660e8400-e29b-41d4-a716-446655440000'},
      {...occurrenceCommand,path:['metadata']}, {...occurrenceCommand,path:Array(65).fill('appArg')},
      {...occurrenceCommand,snapshot:parent.result.sourceSnapshot}, {...occurrenceCommand,fileName:b.fileName},
    ]) { await receiver!(invalid); assert.equal(pending.length,0,'webview cannot replace host parent/file or send a stale path'); }
    assert.equal(errors.length,errorCount+5);
    const followupCall = receiver!(occurrenceCommand); await tick();
    const followup = pending.shift()!;
    assert.equal(parent.current.request.signal.aborted,true,'follow-up uses the ordinary new request lifecycle');
    assert.equal(followup.request.occurrence.snapshot,parent.result.sourceSnapshot);
    assert.equal(followup.request.occurrence.origin,parent.result.sourceSnapshotOrigin);
    assert.deepEqual(JSON.parse(JSON.stringify(followup.request.occurrence.path)),['appArg']);
    assert.equal(messages.at(-1).phase,'analyzing');
    await receiver!(occurrenceCommand);
    assert.equal(pending.length,0,'a second click cannot reuse a parent while its follow-up is running');
    assert.equal(followup.request.signal.aborted,false,'a refused obsolete message cannot cancel the active follow-up');
    const next = sourceResult(followup.request,'770e8400-e29b-41d4-a716-446655440000');
    const occurrence = intoContext({schema:'control-only-occurrence',captureId:next.sourceSnapshotOrigin.captureId,path:['appArg'],
      checking:{status:'captured',action:{status:'completed'},selected:{home:{arity:0,telescope:['nil']},term:['const',['str',['anonymous'],'f'],[]],type:['sort',['zero']]}}});
    followup.resolve({...next,sourceOccurrence:occurrence}); await followupCall;
    assert.equal(messages.at(-1).type,'statementlens.error');
    assert.equal(messages.at(-1).sourceOccurrence,occurrence,'guided failure retains independent occurrence output');
    const exposureCommand = {type:'statementlens.exposeDefinitionHead',parentCaptureId:next.sourceSnapshotOrigin.captureId,target:'term'};
    for (const invalid of [
      {...exposureCommand,parentCaptureId:parentId}, {...exposureCommand,target:'body'}, {...exposureCommand,target:{toString:()=> 'term'}},
      {...exposureCommand,term:['const','forged']}, {...exposureCommand,fileName:b.fileName}, {...exposureCommand,origin:next.sourceSnapshotOrigin},
    ]) { await receiver!(invalid); assert.equal(pending.length,0,'head exposure takes only current identity and target'); }
    const exposeCall = receiver!(exposureCommand); await tick();
    const exposureRequest = pending.shift()!;
    assert.equal(exposureRequest.request.occurrence,undefined);
    assert.equal(exposureRequest.request.headExposure.snapshot,next.sourceSnapshot);
    assert.equal(exposureRequest.request.headExposure.origin,next.sourceSnapshotOrigin);
    assert.equal(exposureRequest.request.headExposure.occurrence,occurrence);
    assert.equal(exposureRequest.request.headExposure.target,'term');
    await receiver!(exposureCommand);
    assert.equal(pending.length,0,'a repeated click cannot reuse an in-flight exposure parent');
    assert.equal(exposureRequest.request.signal.aborted,false,'rejected duplicate does not cancel current work');
    const freshExposure = sourceResult(exposureRequest.request,'880e8400-e29b-41d4-a716-446655440000');
    const exposureRecord = intoContext({schema:'control-only-exposure',captureId:freshExposure.sourceSnapshotOrigin.captureId,target:'term', checking:{status:'captured',action:{status:'completed'},exposure:{status:'candidate',result:occurrence.checking.selected,checking:{status:'completed'}}}});
    exposureRequest.resolve({...freshExposure,sourceHeadExposure:exposureRecord}); await exposeCall;
    assert.equal(messages.at(-1).sourceSnapshot,next.sourceSnapshot,'parent snapshot survives unchanged');
    assert.equal(messages.at(-1).sourceSnapshotOrigin,next.sourceSnapshotOrigin,'parent keeps its original process identity');
    assert.equal(messages.at(-1).sourceOccurrence,occurrence,'original outcomes remain in the original occurrence');
    assert.equal(messages.at(-1).headExposure.snapshot,freshExposure.sourceSnapshot);
    assert.equal(messages.at(-1).headExposure.origin,freshExposure.sourceSnapshotOrigin);
    assert.equal(messages.at(-1).headExposure.record,exposureRecord);
    await receiver!({...exposureCommand,target:'type'});
    assert.equal(pending.length,0,'one retained seed cannot be replaced by a second v1 action');
    await receiver!({...occurrenceCommand,parentCaptureId:next.sourceSnapshotOrigin.captureId});
    assert.equal(pending.length,0,'a retained history cannot be replaced by another occurrence without Refresh');
    const focusCommand = {type:'statementlens.focusExposedPart',parentCaptureId:next.sourceSnapshotOrigin.captureId,
      previousCaptureId:freshExposure.sourceSnapshotOrigin.captureId,parentStepIndex:0,path:[]};
    for (const invalid of [
      {...focusCommand,previousCaptureId:parentId}, {...focusCommand,parentStepIndex:1}, {...focusCommand,parentStepIndex:-1},
      {...focusCommand,path:['metadata']}, {...focusCommand,path:['lamBody']}, {...focusCommand,path:new Array(1)}, {...focusCommand,expectedSelected:occurrence.checking.selected},
      {...focusCommand,origin:next.sourceSnapshotOrigin}, {...focusCommand,type:'statementlens.exposeFocusedHead',path:undefined,target:'term'},
    ]) { await receiver!(invalid); assert.equal(pending.length,0,'continuation cannot forge history, fields or step kind'); }
    const focusCall = receiver!(focusCommand); await tick();
    const focusRequest = pending.shift()!;
    assert.equal(focusRequest.request.decomposition.seed.record,exposureRecord);
    assert.equal(focusRequest.request.decomposition.occurrence,occurrence);
    assert.deepEqual(JSON.parse(JSON.stringify(focusRequest.request.decomposition.operation)),{kind:'focus',path:[]});
    assert.equal(focusRequest.request.decomposition.attempts.length,0);
    await receiver!(focusCommand); assert.equal(pending.length,0); assert.equal(focusRequest.request.signal.aborted,false);
    const focusFresh = sourceResult(focusRequest.request,'aa0e8400-e29b-41d4-a716-446655440000');
    // The native adapter is mocked here. These controls exercise retained identity
    // and lifecycle, while the frontend/native suites validate real receipt data.
    const focusRecord = intoContext({schema:'control-only-decomposition',captureId:focusFresh.sourceSnapshotOrigin.captureId,
      operations:[{kind:'expose',target:'term'},{kind:'focus',path:[]}],checking:{status:'captured',action:{status:'completed'},steps:[
        {index:0,operation:{kind:'expose',target:'term'},output:exposureRecord.checking.exposure,replay:'matched'},
        {index:1,operation:{kind:'focus',path:[]},output:{status:'candidate',result:occurrence.checking.selected,checking:{status:'completed'}},replay:'new'},
      ]}});
    focusRequest.resolve({...focusFresh,sourceDecomposition:focusRecord}); await focusCall;
    assert.equal(messages.at(-1).decompositions.length,1); assert.equal(messages.at(-1).decompositions[0].record,focusRecord);
    assert.equal(messages.at(-1).headExposure.record,exposureRecord); assert.equal(messages.at(-1).sourceOccurrence,occurrence);
    assert.equal(Object.isFrozen(focusRecord.checking.steps),true);
    const exposeFocused = {type:'statementlens.exposeFocusedHead',parentCaptureId:next.sourceSnapshotOrigin.captureId,
      previousCaptureId:focusRecord.captureId,parentStepIndex:1,target:'type'};
    const refusalCall = receiver!(exposeFocused); await tick();
    const refusalRequest = pending.shift()!;
    assert.equal(refusalRequest.request.decomposition.attempts[0].record,focusRecord);
    refusalRequest.resolve({...sourceResult(refusalRequest.request,'bb0e8400-e29b-41d4-a716-446655440000'),sourceDecompositionUnavailable:'No supported head.'}); await refusalCall;
    assert.equal(messages.at(-1).decompositionUnavailable,'No supported head.');
    assert.equal(messages.at(-1).decompositions.length,1,'native omission preserves every retained attempt');
    const backtrackCall = receiver!(focusCommand); await tick();
    const backtrackRequest = pending.shift()!;
    assert.equal(backtrackRequest.request.decomposition.previousCaptureId,exposureRecord.captureId);
    assert.equal(backtrackRequest.request.decomposition.attempts.length,1,'earlier-prefix replay preserves existing history');
    const secondFresh = sourceResult(backtrackRequest.request,'cc0e8400-e29b-41d4-a716-446655440000');
    const secondRecord = intoContext({...focusRecord,captureId:secondFresh.sourceSnapshotOrigin.captureId});
    backtrackRequest.resolve({...secondFresh,sourceDecomposition:secondRecord}); await backtrackCall;
    assert.equal(messages.at(-1).decompositions.length,2);
    assert.equal(messages.at(-1).decompositions[0].record,focusRecord,'earlier suffix stays immutable');
    const staleExposureCall = receiver!(exposeFocused); await tick();
    const staleExposure = pending.shift()!;
    a.version++; listeners.change!({document:a,contentChanges:[{}]});
    assert.equal(staleExposure.request.signal.aborted,true);
    const priorExposureMessages = messages.length;
    staleExposure.resolve({...secondFresh,sourceDecomposition:secondRecord}); await staleExposureCall;
    assert.equal(messages.length,priorExposureMessages,'late continuation restores no history after an edit');
    await establishParent();
    const cancelledCall = receiver!({...occurrenceCommand,parentCaptureId:parentId,path:[]}); await tick();
    const cancelled = pending.shift()!;
    a.version++; listeners.change!({document:a,contentChanges:[{}]});
    assert.equal(cancelled.request.signal.aborted,true);
    const messageCount = messages.length;
    cancelled.resolve({...sourceResult(cancelled.request,parentId),sourceOccurrence:occurrence}); await cancelledCall;
    assert.equal(messages.length,messageCount,'a cancelled late occurrence cannot restore any attachment');
    await receiver!({...occurrenceCommand,parentCaptureId:next.sourceSnapshotOrigin.captureId});
    assert.equal(pending.length,0,'document revision invalidates the retained parent');
    await establishParent();
    const boundedOccurrenceCall = receiver!({...occurrenceCommand,path:[]}); await tick();
    const boundedOccurrenceRequest = pending.shift()!;
    const boundedSource = sourceResult(boundedOccurrenceRequest.request,'dd0e8400-e29b-41d4-a716-446655440000');
    const boundedOccurrence = intoContext({...occurrence,captureId:boundedSource.sourceSnapshotOrigin.captureId,path:[]});
    boundedOccurrenceRequest.resolve({...boundedSource,sourceOccurrence:boundedOccurrence}); await boundedOccurrenceCall;
    const boundedFocus = {type:'statementlens.focusExposedPart',parentCaptureId:boundedOccurrence.captureId,
      previousCaptureId:boundedOccurrence.captureId,parentStepIndex:0,path:[]};
    for (let index = 0; index < 8; index++) {
      const call = receiver!(boundedFocus); await tick();
      const request = pending.shift()!;
      assert.equal(request.request.decomposition.attempts.length,index);
      if (index === 7) {
        const beforeDuplicates = messages.length;
        for (const invalid of [boundedFocus,{...boundedFocus,parentCaptureId:parentId},{...boundedFocus,term:['const','forged']}])
          await receiver!(invalid);
        assert.equal(pending.length,0,'duplicate, obsolete and malformed requests cannot start another analysis');
        assert.equal(messages.length,beforeDuplicates,'rejected controls cannot replace the active request status');
        assert.equal(request.request.signal.aborted,false,'preflight rejection cannot cancel active native work');
      }
      const fresh = sourceResult(request.request,`ee0e840${index}-e29b-41d4-a716-446655440000`);
      const record = intoContext({schema:'control-only-decomposition',captureId:fresh.sourceSnapshotOrigin.captureId,
        parentCaptureId:boundedOccurrence.captureId,previousCaptureId:boundedOccurrence.captureId,parentStepIndex:0,
        operations:[{kind:'focus',path:[]}],checking:{status:'captured',action:{status:'completed'},steps:[
          {index:0,operation:{kind:'focus',path:[]},output:{status:'candidate',result:boundedOccurrence.checking.selected,checking:{status:'completed'}},replay:'new'},
        ]}});
      request.resolve({...fresh,sourceDecomposition:record}); await call;
    }
    const completeHistory = messages.at(-1);
    const exhaustedCommand = {type:'statementlens.exposeFocusedHead',parentCaptureId:boundedOccurrence.captureId,
      previousCaptureId:completeHistory.decompositions.at(-1).record.captureId,parentStepIndex:0,target:'term'};
    let lastResult = completeHistory;
    for (let attempt = 0; attempt < 2; attempt++) {
      const beforeRefusal = messages.length;
      await receiver!(exhaustedCommand);
      assert.equal(pending.length,0,'the ninth attempt is refused without calling native analysis');
      assert.equal(messages.length,beforeRefusal+2,'a bounded refusal sends both status and terminal result');
      const status = messages.at(-2), result = messages.at(-1);
      assert.equal(status.type,'statementlens.status'); assert.equal(status.phase,'analyzing');
      assert.equal(result.type,'statementlens.error'); assert.equal(result.requestId,status.requestId);
      assert.ok(BigInt(status.requestId)>BigInt(lastResult.requestId),'the refusal starts a new request');
      assert.deepEqual(status.document,lastResult.document);
      assert.deepEqual(result.document,status.document,'the refusal completes the exact document association');
      assert.match(result.decompositionUnavailable,/Eight continuation attempts/);
      assert.equal(result.message,result.decompositionUnavailable);
      assert.equal(result.sourceSnapshot,completeHistory.sourceSnapshot);
      assert.equal(result.sourceSnapshotOrigin,completeHistory.sourceSnapshotOrigin);
      assert.equal(result.sourceOccurrence,boundedOccurrence);
      assert.equal(result.decompositions,completeHistory.decompositions,'refusal retains all eight attempts unchanged');
      lastResult = result;
    }
    await establishParent();
    assert.equal(messages.at(-1).sourceSnapshotOrigin.captureId,parentId,'Refresh recovers from exhausted history');
    listeners.config!({affectsConfiguration:()=>true});
    assert.equal(messages.at(-1).phase,'stale','configuration changes invalidate the process association');
    await receiver!(occurrenceCommand); assert.equal(pending.length,0,'configuration changes discard retained parent');
    b.isDirty = true; listeners.change!({document:b,contentChanges:[{}]});
    assert.equal(messages.at(-1).phase,'stale','another Lean buffer invalidates imported context');
    b.isDirty = false;
    let finishReveal:(editor:any)=>void = ()=>{};
    showDocument = ()=>new Promise(resolve=>{finishReveal=resolve;});
    const reveal = receiver!({type:'statementlens.reveal',range:{start:{line:0,character:1},end:{line:0,character:2}}});
    vscode.window.activeTextEditor = editorB; vscode.window.visibleTextEditors=[editorB];
    const newCommand = command(); await tick();
    finishReveal(editorA); await reveal;
    assert.equal(reveals,0,'a new document must invalidate the awaited reveal');
    pending.shift()!.resolve({ok:true,diagnostics:[]}); await newCommand;
    configuredEngine = path.join(engine,'missing');
    const beforeEngineError = errors.length;
    await command();
    assert.equal(messages.at(-1).type,'statementlens.error');
    assert.equal(errors.length,beforeEngineError+1);
    const analyzed = messages.filter(message=>message.type==='statementlens.status'&&message.phase==='analyzing').map(message=>Number(message.requestId));
    assert.ok(analyzed.every((id,index)=>index===0 || id > analyzed[index-1]!));
    for (const disposable of context.subscriptions as any[]) disposable.dispose?.();
  } finally { await rm(engine,{recursive:true,force:true}); }
});
