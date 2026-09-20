import { lazy, Suspense, useEffect, useMemo, useRef, useState } from 'react';
import type { EditorView } from '@codemirror/view';
import type { Analysis, Expr, Scenario, ScenarioValue, StatementNode } from './core';
import { ballGeometry, collectBinders, evaluatePredicate, initialScenario, updateScenario } from './core';
import { compileSemanticDocument, planViews } from './semantic';
import type { PlannedView } from './semantic/types';
import { SemanticView } from './visual';
import { compileReading, compileReadingCues } from './reading';
import { acceptsEditorResult, acceptsEditorStatus, getEditorHost, parseEditorMessage, type EditorSession } from './editor/host';
import { inspectSmallDefinitions } from './semantic/inspection';
import { checkedBinderTypeExpansion } from './semantic/expression';
import { compileInterpretationReport } from './semantic/coverage';
import { InterpretationCoverage } from './visual/InterpretationCoverage';
import { StatementReadingView } from './visual/StatementReadingView';
import { MetricStatementFigure } from './statement-geometry/MetricStatementFigure';
import { expressionKey } from './semantic';
import type { AnalysisRequest } from './protocol';
import { sourceTermAtRange } from './editor/sourceTerms';
const MathematicalStatement=lazy(()=>import('./notation/MathematicalStatement').then(module=>({default:module.MathematicalStatement})));
const LeanEditor=lazy(()=>import('./editor/LeanEditor').then(module=>({default:module.LeanEditor})));
import { VariableControl } from './VariableControl';
import { examples } from './examples';
import { SceneView } from './SceneView';
import { Drawer } from './components/Drawer';
import { FeatureBoundary } from './components/FeatureBoundary';

const symbols = ['∀','∃','ℝ','∈','→','∧','↔','ε','δ','≤'];
const flatten = (node: StatementNode): StatementNode[] => [node,...node.children.flatMap(flatten)];
const mark: Record<string,string> = {forall:'∀',exists:'∃',implies:'→',and:'∧',or:'∨',iff:'↔',not:'¬',predicate:'·',parameter:'↦'};
const kindLabel: Record<string,string> = {'semantic-map':'Structure','relation-map':'Relationships','quantifier-flow':'Choices',ball:'Geometry',graph:'Function',mapping:'Map',interval:'Condition'};
function errorText(value: unknown): string {
  if(typeof value==='string')return value;
  if(Array.isArray(value))return value.map(v=>typeof v==='object'&&v!==null&&'message' in v?String(v.message):String(v)).join('\n');
  return JSON.stringify(value);
}
function constants(expr: Expr): string[] {
  if(expr.kind==='const')return [expr.name];
  if(expr.kind==='app')return [...constants(expr.fn),...expr.args.flatMap(constants)];
  if(expr.kind==='lambda'||expr.kind==='forall')return constants(expr.body);
  return [];
}
function StatementTree({node,selected,choose,interpreted,depth=0}:{node:StatementNode;selected:string;choose:(id:string)=>void;interpreted:Set<string>;depth?:number}) {
  const [closed,setClosed]=useState(false);
  return <div className="tree-branch"><div className={`tree-row ${selected===node.id?'selected':''}`} style={{paddingLeft:Math.min(depth,7)*10}}>
    <button className="tree-collapse" aria-label={`${closed?'Expand':'Collapse'} ${node.label}`} disabled={!node.children.length} onClick={()=>setClosed(!closed)}>{node.children.length?(closed?'›':'⌄'):' '}</button>
    <button className="tree-node" onClick={()=>choose(node.id)} title={node.lean}><span className={`logic-symbol ${node.kind}`}>{mark[node.kind]}</span><span className="tree-label">{node.binder&&node.kind!=='implies'?`${node.binder.name} : ${node.binder.type}`:node.label||node.lean}</span>{interpreted.has(node.id)&&<span className="plot-indicator" aria-label="Has a semantic interpretation"/>}</button>
  </div>{!closed&&node.children.map(child=><StatementTree key={child.id} node={child} selected={selected} choose={choose} interpreted={interpreted} depth={depth+1}/>)}</div>;
}

export default function App(){
  const host=useMemo(()=>getEditorHost(),[]);
  const hostSession=useRef<EditorSession|null>(null);
  const [editorSession,setEditorSession]=useState<EditorSession|null>(null);
  const [source,setSource]=useState(host?'':examples[0].source);
  const [mode,setMode]=useState<'term'|'declaration'>('term');
  const [exampleId,setExampleId]=useState(examples[0].id);
  const [inspectBody,setInspectBody]=useState(true);
  const [autoInspect,setAutoInspect]=useState(true);
  const autoInspectRef=useRef(autoInspect);autoInspectRef.current=autoInspect;
  const [analysis,setAnalysis]=useState<Analysis|null>(null);
  const [analyzedKey,setAnalyzedKey]=useState('');
  const [selected,setSelected]=useState('');
  const [objectId,setObjectId]=useState('');
  const [overrideView,setOverrideView]=useState('');
  const [experience,setExperience]=useState<'read'|'explore'>('read');
  const [scenario,setScenario]=useState<Scenario>({});
  const [busy,setBusy]=useState(false);
  const [error,setError]=useState('');
  const [health,setHealth]=useState<{ready:boolean;leanVersion?:string;issue?:string}|null>(null);
  const [drawer,setDrawer]=useState<'source'|'inspect'|'guide'|null>(null);
  const [showNotation,setShowNotation]=useState(false);
  const [expandNames,setExpandNames]=useState<string[]>([]);
  const [expandName,setExpandName]=useState('');
  const [selection,setSelection]=useState<[number,number]>([0,0]);
  const [sourceTab,setSourceTab]=useState<'source'|'structure'>('source');
  const [inspectorTab,setInspectorTab]=useState<'objects'|'scenario'>('objects');
  const editor=useRef<EditorView|null>(null);
  const plainEditor=useRef<HTMLTextAreaElement|null>(null);
  const request=useRef(0);
  const active=useRef<AbortController|null>(null);
  const stateKey=JSON.stringify([source,mode,expandNames]);
  const currentKey=useRef(stateKey);currentKey.current=stateKey;
  const checked=analyzedKey===stateKey?analysis:null;
  const inspected=useMemo(()=>checked&&autoInspect?inspectSmallDefinitions(checked):checked,[checked,autoInspect]);
  const current=useMemo(()=>inspected&&inspectBody&&inspected.definitionTree?{...inspected,tree:inspected.definitionTree,expression:inspected.definitionTree.expression,pretty:inspected.definitionTree.lean}:inspected,[inspected,inspectBody]);
  const typedSelection=useMemo(()=>current?sourceTermAtRange(source,current.sourceTerms??[],...selection):undefined,[current,source,selection]);
  const document=useMemo(()=>current?compileSemanticDocument(current):null,[current]);
  const coverage=useMemo(()=>document?compileInterpretationReport(document,current?.definitions,selected||undefined):null,[document,current,selected]);
  const plan=useMemo(()=>document?planViews(document,{selectedNodeId:selected||undefined,maxDetailedViews:4}):null,[document,selected]);
  const reading=useMemo(()=>document?compileReading(document,{selectedNodeId:selected||undefined}):null,[document,selected]);
  const cues=useMemo(()=>reading&&document?compileReadingCues(reading,document):null,[reading,document]);
  const allNodes=useMemo(()=>current?flatten(current.tree):[],[current]);
  const selectedNode=allNodes.find(n=>n.id===selected)??current?.tree;
  const primary=plan?.views.find(v=>v.id===(overrideView||plan.primaryViewId))??plan?.views[0];
  const supports=plan?.views.filter(v=>v.id!==primary?.id&&['relation-map','quantifier-flow','semantic-map'].includes(v.kind)).slice(0,2)??[];
  const binders=useMemo(()=>current?collectBinders(current.tree):[],[current]);
  const names=Object.fromEntries(binders.map(b=>[b.id,b.name]));
  const selectedObject=document?.objects.find(o=>o.id===objectId);
  const scene=document?.scenes.find(s=>s.id===primary?.sceneIds[0]);
  const ball=scene?.kind==='ball'?ballGeometry(scene,scenario):null;
  const sample=ball?.status==='geometry'&&ball.membership?ball.membership:scene?evaluatePredicate(scene.expression,scenario):null;
  const availableConstants=useMemo(()=>current?[...new Set(constants(current.expression))].filter(n=>!n.startsWith('inst')&&!n.includes('._')).sort():[],[current]);
  const typedAnalysis=current as (Analysis&{validation?:string;declaration?:{name:string;kind:string;module:string};expansion?:unknown;definitions?:{name:string;canExpand:boolean}[]})|null;

  async function analyze(text=source,inputMode=mode,expansions=expandNames,closeEditor=true){
    if(host){host.postMessage({type:'statementlens.refresh',expansion:{constants:expansions,maxDepth:2}});return;}
    if(!text.trim())return;
    const generation=++request.current;
    const initiatingDrawer=drawer;
    active.current?.abort();const controller=new AbortController();active.current=controller;
    const key=JSON.stringify([text,inputMode,expansions]);
    setBusy(true);setError('');
    const payload:AnalysisRequest={source:text,inputMode,previewDefinitions:expansions.length===0,...(expansions.length?{expansion:{constants:expansions,maxDepth:2}}:{})};
    try{
      const response=await fetch('/api/analyze',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload),signal:controller.signal});
      const data=await response.json();
      if(generation!==request.current||currentKey.current!==key)return;
      if(!response.ok||!data.ok){setAnalysis(null);setError(errorText(data.error??data.diagnostics??'Lean could not read this input.'));return;}
      const enriched=autoInspectRef.current?inspectSmallDefinitions(data):data;
      const effective=enriched.definitionTree?{...enriched,tree:enriched.definitionTree,expression:enriched.definitionTree.expression}:enriched;
      setExperience('read');setInspectorTab('objects');if(closeEditor)setDrawer(currentDrawer=>currentDrawer===initiatingDrawer?null:currentDrawer);
      setAnalysis(data);setInspectBody(true);setAnalyzedKey(key);setSelected(effective.tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(effective.tree));
    }catch(cause){if(generation===request.current&&currentKey.current===key&&!(cause instanceof DOMException&&cause.name==='AbortError')){setAnalysis(null);setError('The local Lean service is unavailable. Start the application with npm run dev.');}}
    finally{if(generation===request.current)setBusy(false);}
  }
  useEffect(()=>{
    if(host){
      setBusy(true);
      const receive=(event:MessageEvent)=>{
        const message=parseEditorMessage(event.data);if(!message)return;
        if(message.type==='statementlens.status'){
          if(message.phase==='idle'||!acceptsEditorStatus(hostSession.current,message))return;
          const session:EditorSession={requestId:message.requestId,document:message.document,phase:message.phase};
          hostSession.current=session;setEditorSession(session);setAnalysis(null);setAnalyzedKey('');setError('');setBusy(message.phase==='analyzing');setObjectId('');
          return;
        }
        if(!acceptsEditorResult(hostSession.current,message))return;
        const session:EditorSession={requestId:message.requestId,document:message.document,phase:message.type==='statementlens.error'?'error':'idle'};
        hostSession.current=session;setEditorSession(session);setBusy(false);
        if(message.type==='statementlens.error'){setAnalysis(null);setError(message.message);return;}
        const data=message.analysis;const policy=data.expansionPolicy as {constants?:unknown}|undefined;const expansions=Array.isArray(policy?.constants)?policy.constants.filter((name):name is string=>typeof name==='string').slice(0,12):[];const key=JSON.stringify([data.source,'term',expansions]);
        const effective=autoInspectRef.current?inspectSmallDefinitions(data):data;
        currentKey.current=key;setSource(data.source);setMode('term');setExpandNames(expansions);setExampleId('');setAnalysis(data);setAnalyzedKey(key);setInspectBody(false);setSelected(data.tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(effective.tree));setExperience('read');setError('');setHealth({ready:true,leanVersion:'4.28.0'});
      };
      window.addEventListener('message',receive);host.postMessage({type:'statementlens.ready'});
      return()=>window.removeEventListener('message',receive);
    }
    fetch('/api/health').then(r=>r.json()).then(setHealth).catch(()=>setHealth({ready:false,issue:'Local Lean service is unavailable.'}));
    void analyze(examples[0].source,'term',[],false);return()=>active.current?.abort();
  },[host]);
  function edit(text:string){setSource(text);setExampleId(examples.find(e=>e.source===text)?.id??'');currentKey.current=JSON.stringify([text,mode,expandNames]);setError('');}
  function chooseNode(id:string){setSelected(id);setOverrideView('');setDrawer(null);}
  function chooseObject(id:string){setObjectId(id);setInspectorTab('objects');setDrawer('inspect');}
  function loadExample(id:string){setAutoInspect(true);const e=examples.find(x=>x.id===id)!;setExampleId(id);setMode('term');setExpandNames([]);setSource(e.source);currentKey.current=JSON.stringify([e.source,'term',[]]);void analyze(e.source,'term',[]);}
  function changeVariable(id:string,value:ScenarioValue){if(current)setScenario(old=>updateScenario(current.tree,old,id,value));}
  function insert(symbol:string){const view=editor.current;if(view){view.dispatch(view.state.replaceSelection(symbol));view.focus();return;}const area=plainEditor.current;if(area){const start=area.selectionStart;edit(source.slice(0,start)+symbol+source.slice(area.selectionEnd));area.focus();requestAnimationFrame(()=>area.setSelectionRange(start+symbol.length,start+symbol.length));}}
  function expand(name:string){setAutoInspect(true);const next=[...new Set([...expandNames,name.trim()])].filter(Boolean).slice(0,12);setExpandNames(next);setExpandName('');currentKey.current=JSON.stringify([source,mode,next]);void analyze(source,mode,next);}
  function exportDocument(){if(!document||!plan)return;const blob=new Blob([JSON.stringify({format:'statementlens-workspace',version:4,reading,cues,coverage,automaticInspection:current?.automaticInspection,editor:editorSession?.document,experience,analysis:checked,viewMode:inspectBody&&checked?.definitionTree?'definition-body':current?.automaticInspection?'automatic-inspection':'original',document,plan,scenario},null,2)],{type:'application/json'});const url=URL.createObjectURL(blob);const a=window.document.createElement('a');a.href=url;a.download='statementlens-workspace.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}
  function renderView(view:PlannedView){
    if(!document)return null;
    if(['semantic-map','relation-map','quantifier-flow'].includes(view.kind))return <SemanticView document={document} view={view} selectedObjectId={objectId} onObjectSelect={chooseObject} onNodeSelect={chooseNode}/>;
    const s=document.scenes.find(x=>view.sceneIds.includes(x.id));
    return s?<SceneView key={`${analyzedKey}:${inspectBody}:${s.id}`} scene={s} scenario={scenario} onVariableChange={changeVariable}/>:null;
  }
  const interpreted=new Set(document?.coverage.filter(c=>c.status!=='structural').map(c=>c.nodeId));
  const activeExample=mode==='term'?examples.find(example=>example.id===exampleId):undefined;
  const editorFileName=editorSession?.document.fileName.split(/[\\/]/).at(-1);
  const parentDeclaration=current?.provenance?.parentDeclaration;
  const title=host?(typeof parentDeclaration==='string'&&!parentDeclaration.startsWith('_')?`A fragment of ${parentDeclaration}`:'Your selected statement'):mode==='declaration'?checked?.provenance?.declaration?.name??source.trim():activeExample?.title??'Your mathematical statement';
  return <div className="app-shell">
    <a className="skip-link" href="#statement-reading">Skip to the statement</a>
    <header className="topbar"><a href="#statement-reading" className="brand" aria-label="Definograph home">Definograph</a><nav className="top-actions" aria-label="Workspace tools"><span className="local-label"><i className={health?.ready?'ready':''}/>{host?'Lean editor':health?.ready?'Lean connected':'Connecting to Lean'}</span><button className="quiet-button" onClick={()=>setDrawer('guide')}>Guide</button><button className="toolbar-button" onClick={exportDocument} disabled={!current}>Export</button></nav></header>
    <Drawer open={drawer==='guide'} title="Reading the diagrams" onClose={()=>setDrawer(null)}>
      <section className="guide"><p className="guide-lead">Follow a statement through its objects, assumptions, and conclusions.</p><div className="guide-grid"><p><strong>A sequence with an overview.</strong> Read each mathematical region in order. The overview keeps the whole statement alongside, including branches and nested conditions.</p><p><strong>Quantifiers describe choices.</strong> ∀ introduces an arbitrary choice; ∃ asks for a witness. A witness may use earlier choices, never a choice introduced later.</p><p><strong>Abstract objects need no coordinates.</strong> Maps connect the types supplied by Lean. Regions express membership and inclusion; distances and shapes appear only when their meaning is recognized.</p><p><strong>Every diagram has a source.</strong> Select an object to inspect its type and occurrences. Use Lean source to read or change the input, and Inspect for definition expansion and interpretation details.</p><p><strong>Samples are optional.</strong> Exploration uses numerical examples. The reading sequence is symbolic. A type-checked statement can still be false; neither its diagram nor a sample is a proof.</p></div></section>
    </Drawer>
    <main className="workspace atlas-workspace">
      <div className="statement-bar">{host?<div className="editor-context"><span>FROM YOUR LEAN EDITOR</span><strong>{editorFileName??'Select a mathematical statement'}</strong>{editorSession&&<small>Buffer v{editorSession.document.version} · line {editorSession.document.selection.start.line+1}</small>}</div>:<div className="statement-picker"><label htmlFor="example">Statement</label><select id="example" value={mode==='term'?exampleId:''} onChange={e=>loadExample(e.target.value)} disabled={busy}><option value="" disabled>{mode==='declaration'?'Lean declaration':'Custom Lean statement'}</option>{examples.map(e=><option key={e.id} value={e.id}>{e.title}</option>)}</select></div>}<div className="statement-actions">{host&&<button className="toolbar-button" onClick={()=>void analyze()} disabled={busy}>Refresh from editor</button>}<button className="toolbar-button" onClick={()=>setDrawer('source')}>Lean source <span aria-hidden="true">↗</span></button><button className="toolbar-button" onClick={()=>setDrawer('inspect')} disabled={!current}>Inspect <span aria-hidden="true">↗</span></button></div></div>
      <Drawer open={drawer==='source'} side="left" title="Lean source" onClose={()=>setDrawer(null)}>
      <section className="source-panel">
        <div className="source-tabs"><button className={sourceTab==='source'?'active':''} onClick={()=>setSourceTab('source')}>Source</button><button className={sourceTab==='structure'?'active':''} onClick={()=>setSourceTab('structure')}>Structure <span>{allNodes.length||'—'}</span></button></div>
        {sourceTab==='source'?host?<div className="editor-source-readonly"><p>This fragment comes from your actual Lean buffer and its imported definitions. Edit in VS Code, then refresh this view.</p><button className="toolbar-button" onClick={()=>host.postMessage({type:'statementlens.reveal'})}>Reveal selection in Lean ↗</button><pre>{current?.pretty??source}</pre>{error&&<div className="error-box" role="alert"><pre>{error}</pre></div>}</div>:<>
          <div className="input-modes" aria-label="Lean input mode"><button className={mode==='term'?'active':''} aria-pressed={mode==='term'} onClick={()=>{setMode('term');setExpandNames([]);}}>Statement</button><button className={mode==='declaration'?'active':''} aria-pressed={mode==='declaration'} onClick={()=>{setMode('declaration');setExampleId('');setSource('Function.Injective');setExpandNames([]);}}>Declaration</button></div>
          <p className="example-description">{mode==='term'?'Enter a complete Lean expression with its variable binders.':'Read the statement or typed signature of a declaration in the local Lean environment.'}</p>
          <div className="editor-label"><span>{mode==='term'?'Lean expression':'Qualified declaration name'}</span><span>⌘ / Ctrl + Enter</span></div>
          <FeatureBoundary fallback={<div className="plain-editor"><p>The enhanced editor could not load. You can continue in this basic editor.</p><textarea ref={plainEditor} aria-label="Lean statement editor" value={source} spellCheck={false} onChange={event=>edit(event.target.value)} onSelect={event=>setSelection([event.currentTarget.selectionStart,event.currentTarget.selectionEnd])} onKeyDown={event=>{if((event.metaKey||event.ctrlKey)&&event.key==='Enter'){event.preventDefault();if(!busy)void analyze();}}}/></div>}><Suspense fallback={<div className="editor-loading">Loading editor…</div>}><LeanEditor value={source} onChange={edit} onAnalyze={()=>{if(!busy)void analyze();}} onSelection={(from,to)=>setSelection([from,to])} editorRef={editor}/></Suspense></FeatureBoundary>
          {mode==='term'&&<div className="symbol-bar">{symbols.map(s=><button key={s} onClick={()=>insert(s)} title={`Insert ${s}`}>{s}</button>)}</div>}
          <p className="input-help">{mode==='term'?<>Type <code>\forall</code> + Tab for ∀. Include variable binders; select a fragment after analysis.</>:<>For example <code>Metric.mem_ball</code>, <code>Function.comp</code>, or <code>Function.Injective</code>.</>}</p>
          <button className="analyze-button" disabled={busy||!source.trim()} onClick={()=>void analyze()}>{busy?<><span className="spinner"/>Reading with Lean…</>:<>Interpret {mode==='term'?'statement':'declaration'}<span>↗</span></>}</button>
          {error&&<div className="error-box" role="alert"><strong>The statement could not be read.</strong><pre>{error}</pre></div>}
          {typedSelection&&<details className="typed-selection"><summary>Type at selection <code>{typedSelection.type}</code></summary><pre>{typedSelection.lean}</pre><p>Exact source occurrence from Lean · bytes {typedSelection.startByte}–{typedSelection.endByte}</p></details>}

        </>:<><div className="outline-heading"><p>Select any part of the statement. Its surrounding scope stays attached.</p><button className="quiet-button" disabled={!current} onClick={()=>current&&chooseNode(current.tree.id)}>Whole statement</button></div>{current?<div className="statement-tree"><StatementTree key={analyzedKey} node={current.tree} selected={selected} choose={chooseNode} interpreted={interpreted}/></div>:<p className="empty-tree muted">Analyze the current source to read its logical structure.</p>}</>}
        <div className="engine-status">{host?'Project context · isolated reader process':health?.ready?`Lean ${health.leanVersion?.match(/\d+\.\d+\.\d+/)?.[0]??'4'} · read-only environment`:health?.issue??'Connecting to Lean…'}</div>
      </section></Drawer>
      <section className="visual-panel" id="statement-reading" aria-label="Statement reading">

        {current&&document&&reading&&plan&&primary?<>
          <div className="visual-title"><div className="atlas-kicker"><span>THE VISUAL STATEMENT</span><span className="status-tag">{host?'Project context fragment':checked?.definitionTree&&inspectBody?'Definition body':typedAnalysis?.validation?.includes('declaration')?'Signature checked by Lean':'Type checked by Lean'}</span></div><h1>{title}</h1><p>{host?'The selected expression, with its local parameters and assumptions. Reading a fragment does not assert a theorem.':activeExample?.description??'Read the objects and relationships in their logical context.'}</p></div>
          {host&&current.diagnostics.length>0&&<button className="editor-diagnostics-note quiet-button" onClick={()=>setDrawer('inspect')}>{current.diagnostics.length} Lean {current.diagnostics.length===1?'diagnostic':'diagnostics'} in this buffer · inspect ↗</button>}
          {checked?.definitionTree&&<div className="definition-mode" aria-label="Declaration view">{(['body','signature'] as const).map(view=><button key={view} className={inspectBody===(view==='body')?'active':''} aria-pressed={inspectBody===(view==='body')} onClick={()=>{const body=view==='body';const tree=body?checked.definitionTree!:checked.tree;setInspectBody(body);setExperience('read');setInspectorTab('objects');setSelected(tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(tree));}}>{view==='body'?'Definition body':'Typed signature'}</button>)}<span>{inspectBody?'The body describes the result under its parameters.':'Parameters specify inputs; they do not assert a proposition.'}</span></div>}
          <div className="experience-tabs" aria-label="Reading and exploration"><button className={experience==='read'?'active':''} aria-pressed={experience==='read'} onClick={()=>{setExperience('read');setInspectorTab('objects');}}>Visual sequence</button><button className={experience==='explore'?'active':''} aria-pressed={experience==='explore'} onClick={()=>{setExperience('explore');setInspectorTab(primary.fidelity==='numerical'?'scenario':'objects');}}>Explore a sample</button><button className="notation-toggle" aria-pressed={showNotation} onClick={()=>setShowNotation(!showNotation)}>{showNotation?'Hide notation':'Mathematical notation'}</button></div>
          {showNotation&&<FeatureBoundary fallback={<section className="notation-fallback"><p>Mathematical typesetting could not load. The checked Lean statement is available here.</p><pre>{current.pretty}</pre></section>}><Suspense fallback={<p>Loading mathematical notation…</p>}><MathematicalStatement notation={inspectBody&&checked?.definitionTree?checked.definitionReadableMath:checked?.readableMath} lean={current.pretty}/></Suspense></FeatureBoundary>}
          {experience==='read'?<StatementReadingView reading={reading} document={document} selectedObjectId={objectId} onObjectSelect={chooseObject} onNodeSelect={chooseNode} renderGeometry={panel=>{
            // Replace only a complete membership clause, never geometry nested inside an unknown claim.
            const roots=panel.rootRelationIds.map(id=>document.relations.find(r=>r.id===id)).filter(Boolean);
            if(roots.length!==1||roots[0]?.kind!=='membership')return null;
            const setId=roots[0].ports.find(p=>p.role==='set')?.objectId;
            const set=document.objects.find(o=>o.id===setId);
            const ballScene=document.scenes.find(s=>panel.sceneIds.includes(s.id)&&s.kind==='ball'&&s.point&&set&&expressionKey(s.expression)===expressionKey(set.expression));
            return ballScene?.kind==='ball'?<MetricStatementFigure scene={ballScene}/>:null;
          }}/>:<><div className="exploration-heading"><p className="exploration-intro">Optional illustrations of selected fragments. Numerical values do not change the statement or establish its truth.</p><button className="toolbar-button" onClick={()=>{setInspectorTab('scenario');setDrawer('inspect');}}>Sample choices ↗</button></div>
          <div className="view-tabs" aria-label="Representations">{plan.views.map(v=><button key={v.id} className={primary.id===v.id?'active':''} aria-pressed={primary.id===v.id} title={v.title} onClick={()=>{setOverrideView(v.id);if(v.fidelity==='numerical')setInspectorTab('scenario');}}>{kindLabel[v.kind]}{v.id===plan.primaryViewId&&<span className="recommended-dot"/>}</button>)}</div>
          <article className="view-card primary-view"><header><div><span className="view-index">01</span><strong>{primary.title}</strong></div><span className={`fidelity ${primary.fidelity}`}>{primary.fidelity==='numerical'?'Numerical illustration':primary.fidelity==='symbolic'?'Symbolic relationships':'Formal structure'}</span></header>{scene&&(scene.context.length>0||scene.guards.length>0)&&<div className="view-context">{scene.context.map((c,i)=><span key={i}>{c}</span>)}{scene.guards.length>0&&<span>Under {scene.guards.length} local {scene.guards.length===1?'assumption':'assumptions'}</span>}</div>}{renderView(primary)}<div className="view-reason"><span>Why this view</span><p>{primary.reason}</p></div></article>
          {supports.map((view,i)=><article className="view-card supporting-view" key={view.id}><header><div><span className="view-index">0{i+2}</span><strong>{view.title}</strong></div><span className="fidelity">{kindLabel[view.kind]}</span></header>{renderView(view)}</article>)}
          </>}
          {current.automaticInspection&&<div className="automatic-reading-note"><span>Reading <code>{current.automaticInspection.constant}</code> through its checked definition.</span><button type="button" onClick={()=>{setDrawer('inspect');setInspectorTab('objects');}}>See original and details ↗</button></div>}
          {expandNames.length>0&&<div className="expansion-note">{allNodes.filter(n=>n.expansion).length?`${allNodes.filter(n=>n.expansion).length} definition expansions checked by Lean for definitional equality.`:'No selected definition occurred at an expandable fragment head.'}</div>}
          <div className="reading-footnote"><span>A diagram of the statement, not a proof.</span><button className="quiet-button" onClick={()=>setDrawer('inspect')}>Interpretation details ↗</button></div>
        </>:<div className="empty-view"><h1>{busy?'Reading the mathematical structure':editorSession?.phase==='stale'?'Your Lean buffer has changed':host?'Read a statement from your Lean editor':analysis?'Your source has changed':'From a statement to its structure'}</h1><p>{busy?'Lean is resolving types, scope, and definitions.':host?(error||'Select a proposition in your Lean file, then refresh. Its local context stays attached to the reading.'):error?'Open Lean source to review and correct the input.':'Interpret the current Lean input to build connected views of its objects, relationships, and choices.'}</p>{!busy&&<button className="toolbar-button" onClick={()=>host?void analyze():setDrawer('source')}>{host?'Refresh from editor':error?'Review Lean source':'Open Lean source'}</button>}{error&&<p className="error-summary" role="alert">The input could not be read.</p>}</div>}
      </section>
      <Drawer open={drawer==='inspect'} title="Inspect the statement" onClose={()=>setDrawer(null)}><section className="scenario-panel inspector">
        <div className="source-tabs"><button className={inspectorTab==='objects'?'active':''} onClick={()=>setInspectorTab('objects')}>Objects</button>{experience==='explore'&&<button className={inspectorTab==='scenario'?'active':''} onClick={()=>setInspectorTab('scenario')}>Scenario</button>}</div>
        {inspectorTab==='objects'?<>
          {selectedObject?<div className="object-detail"><span className="object-kind">{selectedObject.kind}</span><h2>{selectedObject.label}</h2><pre>{selectedObject.type||'Type retained in expression'}</pre>{selectedObject.binder && checkedBinderTypeExpansion(selectedObject.binder) && <details className="lean-details"><summary>Structure behind this named type</summary><p>Lean checked this small type expansion for definitional equality. The declared name remains above.</p><pre>{selectedObject.binder.typeExpansion!.after}</pre></details>}<span className="eyebrow">APPEARS IN</span>{[...new Set(selectedObject.provenance.map(p=>p.nodeId))].map(id=><button className="object-occurrence" key={id} onClick={()=>chooseNode(id)}>{allNodes.find(n=>n.id===id)?.lean??id}<span>↗</span></button>)}<button className="quiet-button" onClick={()=>setObjectId('')}>All objects</button></div>:<><p className="scenario-intro">Select an object in any diagram to follow its relationships.</p><div className="object-list">{document?.objects.filter(o=>o.binder||['set','function','point'].includes(o.kind)).slice(0,40).map(o=><button key={o.id} onClick={()=>setObjectId(o.id)}><span className={`object-monogram ${o.kind}`}>{o.kind==='function'?'↦':o.kind==='set'?'∈':o.binder?.role==='existential'?'∃':'·'}</span><span><strong>{o.label}</strong><small>{o.type||o.kind}</small></span><span>›</span></button>)}</div></>}
          {current&&(!host||typedAnalysis?.definitions?.some(definition=>definition.canExpand))&&<details className="definition-tools"><summary>Look inside a definition</summary><p>Expand a trusted definition to expose its underlying relationships. Expansion is explicit and bounded.</p><label className="field-label" htmlFor="definition">Definition name</label><input id="definition" list="definitions" value={expandName} onChange={e=>setExpandName(e.target.value)} placeholder="Function.Injective"/><datalist id="definitions">{(typedAnalysis?.definitions?.filter(d=>d.canExpand).map(d=>d.name)??availableConstants).map(n=><option key={n} value={n}/>)}</datalist><button className="toolbar-button" disabled={busy||!expandName.trim()} onClick={()=>expand(expandName)}>Expand definition ↗</button>{expandNames.length>0&&<><div className="expanded-list">{expandNames.map(n=><code key={n}>{n}</code>)}</div><button className="quiet-button" onClick={()=>{setAutoInspect(false);setExpandNames([]);currentKey.current=JSON.stringify([source,mode,[]]);void analyze(source,mode,[]);}}>Return to original structure</button></>}</details>}
        </>:<><h2>Choices, in order</h2><p className="scenario-intro">Each numerical view shares this scenario. Changing an earlier choice clears dependent witnesses.</p><div className="quantifier-key"><span><b>∀</b> arbitrary choice</span><span><b>∃</b> candidate witness</span></div><div className="variables">{binders.map(b=><VariableControl key={b.id} binder={b} value={scenario[b.id]} names={names} onChange={value=>changeVariable(b.id,value)}/>)}</div>{sample&&<div className="sample-status"><span className="eyebrow">AT THIS SAMPLE</span><strong className={sample.status==='false'?'sample-false':''}>{sample.status==='unknown'?'No numerical decision':sample.status==='true'?'Condition holds numerically':'Condition fails numerically'}</strong><p>{sample.status==='unknown'?sample.reason:sample.explanation}</p><span className="small muted">Approximate values, not a proof.</span></div>}{scene?.guards.length?<div className="assumptions"><span className="eyebrow">ASSUMPTIONS IN SCOPE</span>{scene.guards.map((g,i)=>{const value=evaluatePredicate(g,scenario);return <p key={i}><code>{allNodes.find(n=>n.expression===g)?.lean??'Local assumption'}</code><br/><span className={value.status==='false'?'sample-false':''}>{value.status==='unknown'?'Symbolic assumption':value.status==='true'?'Satisfied numerically':'Not satisfied at this sample'}</span></p>;})}</div>:null}</>}
        {!current&&<p className="scenario-footnote">The inspector will show the objects and choices in your next analysis.</p>}
        {current&&document&&plan&&<div className="inspection-details">{checked?.definitionPreviews?.length ? <div className="automatic-inspection"><label><input type="checkbox" checked={autoInspect} onChange={event=>{setAutoInspect(event.target.checked);setSelected(checked.tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(event.target.checked?inspectSmallDefinitions(checked).tree:checked.tree));}}/> Automatically inspect small definitions</label>{current.automaticInspection?<><p>Opened <code>{current.automaticInspection.constant}</code>. {current.automaticInspection.reason}</p><details><summary>Original statement before inspection</summary><pre>{current.automaticInspection.originalPretty}</pre></details></>:<p>{autoInspect ? 'The original reading is retained when an expansion does not reduce uninterpreted meaning within the size limit.' : 'Automatic inspection is off. Reading the original checked statement.'}</p>}</div>:null}          <details className="lean-details"><summary>{selected===current.tree.id?(checked?.definitionTree&&inspectBody?'Definition body':typedAnalysis?.validation?.includes('declaration')?'Typed signature':'Elaborated statement'):'Selected fragment · enclosing scope retained'}</summary><pre>{selectedNode?.lean}</pre></details>
          <details className="buffer-diagnostics"><summary>Lean diagnostics <span>{current.diagnostics.length}</span></summary>{current.diagnostics.length?current.diagnostics.slice(0,100).map((diagnostic,index)=>{const item=diagnostic&&typeof diagnostic==='object'?diagnostic as Record<string,unknown>:{};return <div key={index}><span>{String(item.severity??'note')}{typeof item.line==='number'?` · line ${item.line}`:''}</span><pre>{typeof item.message==='string'?item.message:errorText(diagnostic)}</pre></div>;}):<p>No diagnostics were reported for this analysis.</p>}</details><details className="coverage-details"><summary>Interpretation coverage <span>{plan.coverage.interpreted} interpreted · {plan.coverage.partial} partial · {plan.coverage.structural} structural fragments</span></summary>{coverage&&<InterpretationCoverage report={coverage} busy={busy} onNodeSelect={chooseNode} onExpand={expand}/>}</details>
</div>}
      </section></Drawer>
    </main>
  </div>;
}
