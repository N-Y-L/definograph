import { test } from 'node:test';
import assert from 'node:assert/strict';
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
      workspace:{isTrusted:true,textDocuments:[a,b],getWorkspaceFolder:()=>({uri:{toString:()=>engine}}),getConfiguration:()=>({get:(name:string,fallback:any)=>name==='engineDirectory'?configuredEngine:fallback}),onDidChangeTextDocument:(fn:any)=>{listeners.change=fn;return{dispose(){}};},onDidCloseTextDocument:(fn:any)=>{listeners.close=fn;return{dispose(){}};}},
      window:{activeTextEditor:editorA,visibleTextEditors:[editorA],createWebviewPanel:()=>panel,showErrorMessage:(message:string)=>{errors.push(message);},showTextDocument:(doc:any)=>showDocument(doc)},
    };
    const bundled = await build({entryPoints:[entry],bundle:true,write:false,platform:'node',format:'cjs',external:['vscode'],plugins:[{name:'bounded-adapter-test',setup(api){api.onResolve({filter:/server\/editor-context\.js$/},()=>({path:'context-adapter',namespace:'fixture'}));api.onLoad({filter:/.*/,namespace:'fixture'},()=>({contents:'export const analyzeEditorContext = globalThis.__analyze;',loader:'js'}));}}]});
    const module = {exports:{} as any};
    vm.runInNewContext(bundled.outputFiles[0]!.text, {module,exports:module.exports,require:(name:string)=>name==='vscode'?vscode:nativeRequire(name),Buffer,process,AbortController,structuredClone,__analyze:(request:any)=>new Promise(resolve=>pending.push({request,resolve}))});
    const context = {extensionPath:path.join(engine,'extension'),subscriptions:[]};
    module.exports.activate(context);
    const command = commands.get('statementLens.visualizeSelection')!;
    await command();
    assert.match(panel.webview.html,/Content-Security-Policy/);
    assert.match(panel.webview.html,/vscode-resource:.*assets\/app.js/);
    const ready = receiver!({type:'statementlens.ready'}); await tick();
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
    await command();
    assert.equal(messages.at(-1).type,'statementlens.error');
    assert.equal(errors.length,1);
    const analyzed = messages.filter(message=>message.type==='statementlens.status'&&message.phase==='analyzing').map(message=>Number(message.requestId));
    assert.ok(analyzed.every((id,index)=>index===0 || id > analyzed[index-1]!));
    for (const disposable of context.subscriptions as any[]) disposable.dispose?.();
  } finally { await rm(engine,{recursive:true,force:true}); }
});
