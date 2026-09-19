import { lazy, Suspense, useEffect, useMemo, useRef, useState } from 'react';
import type { EditorView } from '@codemirror/view';
import type { Analysis, Expr, Scenario, ScenarioValue, StatementNode } from './core';
import { ballGeometry, collectBinders, evaluatePredicate, initialScenario, updateScenario } from './core';
import { compileSemanticDocument, planViews } from './semantic';
import type { PlannedView } from './semantic/types';
import { SemanticView } from './visual';
import type { AnalysisRequest } from './protocol';
import { sourceTermAtRange } from './editor/sourceTerms';
const LeanEditor=lazy(()=>import('./editor/LeanEditor').then(module=>({default:module.LeanEditor})));
import { VariableControl } from './VariableControl';
import { examples } from './examples';
import { SceneView } from './SceneView';

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
  const [source,setSource]=useState(examples[0].source);
  const [mode,setMode]=useState<'term'|'declaration'>('term');
  const [exampleId,setExampleId]=useState(examples[0].id);
  const [inspectBody,setInspectBody]=useState(true);
  const [analysis,setAnalysis]=useState<Analysis|null>(null);
  const [analyzedKey,setAnalyzedKey]=useState('');
  const [selected,setSelected]=useState('');
  const [objectId,setObjectId]=useState('');
  const [overrideView,setOverrideView]=useState('');
  const [scenario,setScenario]=useState<Scenario>({});
  const [busy,setBusy]=useState(false);
  const [error,setError]=useState('');
  const [health,setHealth]=useState<{ready:boolean;leanVersion?:string;issue?:string}|null>(null);
  const [guide,setGuide]=useState(false);
  const [expandNames,setExpandNames]=useState<string[]>([]);
  const [expandName,setExpandName]=useState('');
  const [selection,setSelection]=useState<[number,number]>([0,0]);
  const [sourceTab,setSourceTab]=useState<'source'|'structure'>('source');
  const [inspectorTab,setInspectorTab]=useState<'objects'|'scenario'>('objects');
  const editor=useRef<EditorView|null>(null);
  const request=useRef(0);
  const active=useRef<AbortController|null>(null);
  const stateKey=JSON.stringify([source,mode,expandNames]);
  const currentKey=useRef(stateKey);currentKey.current=stateKey;
  const checked=analyzedKey===stateKey?analysis:null;
  const current=useMemo(()=>checked&&inspectBody&&checked.definitionTree?{...checked,tree:checked.definitionTree,expression:checked.definitionTree.expression,pretty:checked.definitionTree.lean}:checked,[checked,inspectBody]);
  const typedSelection=useMemo(()=>current?sourceTermAtRange(source,current.sourceTerms??[],...selection):undefined,[current,source,selection]);
  const document=useMemo(()=>current?compileSemanticDocument(current):null,[current]);
  const plan=useMemo(()=>document?planViews(document,{selectedNodeId:selected||undefined,maxDetailedViews:4}):null,[document,selected]);
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

  async function analyze(text=source,inputMode=mode,expansions=expandNames){
    if(!text.trim())return;
    const generation=++request.current;
    active.current?.abort();const controller=new AbortController();active.current=controller;
    const key=JSON.stringify([text,inputMode,expansions]);
    setBusy(true);setError('');
    const payload:AnalysisRequest={source:text,inputMode,...(expansions.length?{expansion:{constants:expansions,maxDepth:2}}:{})};
    try{
      const response=await fetch('/api/analyze',{method:'POST',headers:{'Content-Type':'application/json'},body:JSON.stringify(payload),signal:controller.signal});
      const data=await response.json();
      if(generation!==request.current||currentKey.current!==key)return;
      if(!response.ok||!data.ok){setAnalysis(null);setError(errorText(data.error??data.diagnostics??'Lean could not read this input.'));return;}
      const effective=data.definitionTree?{...data,tree:data.definitionTree,expression:data.definitionTree.expression}:data;
      const doc=compileSemanticDocument(effective);const automatic=planViews(doc);setInspectorTab(automatic.views[0]?.fidelity==='numerical'?'scenario':'objects');
      setAnalysis(data);setInspectBody(true);setAnalyzedKey(key);setSelected(effective.tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(effective.tree));
    }catch(cause){if(generation===request.current&&currentKey.current===key&&!(cause instanceof DOMException&&cause.name==='AbortError')){setAnalysis(null);setError('The local Lean service is unavailable. Start the application with npm run dev.');}}
    finally{if(generation===request.current)setBusy(false);}
  }
  useEffect(()=>{fetch('/api/health').then(r=>r.json()).then(setHealth).catch(()=>setHealth({ready:false,issue:'Local Lean service is unavailable.'}));void analyze(examples[0].source,'term',[]);return()=>active.current?.abort();},[]);
  function edit(text:string){setSource(text);setExampleId(examples.find(e=>e.source===text)?.id??'');currentKey.current=JSON.stringify([text,mode,expandNames]);setError('');}
  function chooseNode(id:string){setSelected(id);setOverrideView('');}
  function loadExample(id:string){const e=examples.find(x=>x.id===id)!;setExampleId(id);setMode('term');setExpandNames([]);setSource(e.source);currentKey.current=JSON.stringify([e.source,'term',[]]);void analyze(e.source,'term',[]);}
  function changeVariable(id:string,value:ScenarioValue){if(current)setScenario(old=>updateScenario(current.tree,old,id,value));}
  function insert(symbol:string){const view=editor.current;if(!view)return;view.dispatch(view.state.replaceSelection(symbol));view.focus();}
  function expand(name:string){const next=[...new Set([...expandNames,name.trim()])].filter(Boolean).slice(0,12);setExpandNames(next);setExpandName('');currentKey.current=JSON.stringify([source,mode,next]);void analyze(source,mode,next);}
  function exportDocument(){if(!document||!plan)return;const blob=new Blob([JSON.stringify({format:'statementlens-workspace',version:1,analysis:checked,viewMode:inspectBody&&checked?.definitionTree?'definition-body':'original',document,plan,scenario},null,2)],{type:'application/json'});const url=URL.createObjectURL(blob);const a=window.document.createElement('a');a.href=url;a.download='statementlens-workspace.json';a.click();setTimeout(()=>URL.revokeObjectURL(url),1000);}
  function renderView(view:PlannedView){
    if(!document)return null;
    if(['semantic-map','relation-map','quantifier-flow'].includes(view.kind))return <SemanticView document={document} view={view} selectedObjectId={objectId} onObjectSelect={id=>{setObjectId(id);setInspectorTab('objects');}} onNodeSelect={chooseNode}/>;
    const s=document.scenes.find(x=>view.sceneIds.includes(x.id));
    return s?<SceneView key={`${analyzedKey}:${inspectBody}:${s.id}`} scene={s} scenario={scenario} onVariableChange={changeVariable}/>:null;
  }
  const interpreted=new Set(document?.coverage.filter(c=>c.status!=='structural').map(c=>c.nodeId));
  return <div className="app-shell">
    <header className="topbar"><div className="brand"><span className="brand-icon">∈</span><span>Statement<span className="brand-light">Lens</span></span><span className="version">MATHEMATICAL WORKBENCH</span></div><div className="top-actions"><span className="local-label"><i/>Local · Lean 4</span><button className="quiet-button" onClick={()=>setGuide(!guide)} aria-expanded={guide}>Reading the diagrams</button><button className="toolbar-button" onClick={exportDocument} disabled={!current}>Export workspace ↗</button></div></header>
    {guide&&<section className="guide"><button className="close-guide quiet-button" onClick={()=>setGuide(false)}>Close</button><h2>Read the relationships. Explore the choices.</h2><div className="guide-grid"><p><strong>One statement, linked views.</strong> Objects retain their identity across diagrams. Select an object to inspect its type and the fragments where it appears.</p><p><strong>Quantifiers describe choices.</strong> ∀ introduces an arbitrary choice; ∃ asks for a witness. Dependency arrows show which earlier choices a witness may use.</p><p><strong>The representation follows the structure.</strong> Spatial objects receive geometry when a metric is recognized. Sets, functions, and other typed objects receive symbolic relationships.</p><p><strong>Each view states what it preserves.</strong> Numerical samples, symbolic relationships, and formal types carry different information. Elaboration alone never establishes truth.</p></div></section>}
    <main className="workspace workbench">
      <aside className="source-panel"><div className="panel-heading"><span className="eyebrow">LEAN WORKSPACE</span><span className={`engine-dot ${health?.ready?'ready':''}`} title={health?.leanVersion??health?.issue}/></div>
        <div className="source-tabs"><button className={sourceTab==='source'?'active':''} onClick={()=>setSourceTab('source')}>Source</button><button className={sourceTab==='structure'?'active':''} onClick={()=>setSourceTab('structure')}>Structure <span>{allNodes.length||'—'}</span></button></div>
        {sourceTab==='source'?<>
          <div className="input-modes" aria-label="Lean input mode"><button className={mode==='term'?'active':''} aria-pressed={mode==='term'} onClick={()=>{setMode('term');setExpandNames([]);}}>Statement</button><button className={mode==='declaration'?'active':''} aria-pressed={mode==='declaration'} onClick={()=>{setMode('declaration');setSource('Function.Injective');setExpandNames([]);}}>Declaration</button></div>
          {mode==='term'?<><label className="field-label" htmlFor="example">Explore a mathematical structure</label><select id="example" value={exampleId} onChange={e=>loadExample(e.target.value)} disabled={busy}><option value="" disabled>Custom Lean statement</option>{examples.map(e=><option key={e.id} value={e.id}>{e.title}</option>)}</select><p className="example-description">{examples.find(e=>e.id===exampleId)?.description??'Read the typed objects and relationships in your own statement.'}</p></>:<p className="example-description">Read the statement or typed signature of a declaration in the local Lean environment.</p>}
          <div className="editor-label"><span>{mode==='term'?'Lean expression':'Qualified declaration name'}</span><span>⌘ / Ctrl + Enter</span></div>
          <Suspense fallback={<div className="editor-loading">Loading editor…</div>}><LeanEditor value={source} onChange={edit} onAnalyze={()=>{if(!busy)void analyze();}} onSelection={(from,to)=>setSelection([from,to])} editorRef={editor}/></Suspense>
          {mode==='term'&&<div className="symbol-bar">{symbols.map(s=><button key={s} onClick={()=>insert(s)} title={`Insert ${s}`}>{s}</button>)}</div>}
          <p className="input-help">{mode==='term'?<>Type <code>\forall</code> + Tab for ∀. Include variable binders; select a fragment after analysis.</>:<>For example <code>Metric.mem_ball</code>, <code>Function.comp</code>, or <code>Function.Injective</code>.</>}</p>
          <button className="analyze-button" disabled={busy||!source.trim()} onClick={()=>void analyze()}>{busy?<><span className="spinner"/>Reading with Lean…</>:<>Interpret {mode==='term'?'statement':'declaration'}<span>↗</span></>}</button>
          {error&&<div className="error-box" role="alert"><strong>Lean could not elaborate this input.</strong><pre>{error}</pre></div>}
          {typedSelection&&<details className="typed-selection"><summary>Type at selection <code>{typedSelection.type}</code></summary><pre>{typedSelection.lean}</pre><p>Exact source occurrence from Lean · bytes {typedSelection.startByte}–{typedSelection.endByte}</p></details>}
          <div className="source-summary"><span className="eyebrow">FROM LEAN TO A VIEW</span><ol><li><b>01</b> Resolve types and local scope</li><li><b>02</b> Connect objects and relationships</li><li><b>03</b> Compose the available representations</li></ol></div>
        </>:<><div className="outline-heading"><p>Select any part of the statement. Its surrounding scope stays attached.</p><button className="quiet-button" disabled={!current} onClick={()=>current&&chooseNode(current.tree.id)}>Whole statement</button></div>{current?<div className="statement-tree"><StatementTree key={analyzedKey} node={current.tree} selected={selected} choose={chooseNode} interpreted={interpreted}/></div>:<p className="empty-tree muted">Analyze the current source to read its logical structure.</p>}</>}
        <div className="engine-status">{health?.ready?`Lean ${health.leanVersion?.match(/\d+\.\d+\.\d+/)?.[0]??'4'} · read-only environment`:health?.issue??'Connecting to Lean…'}</div>
      </aside>
      <section className="visual-panel">
        <div className="canvas-heading"><div className="eyebrow">INTERPRETATION CANVAS</div>{current&&<span className="status-tag">{checked?.definitionTree&&inspectBody?'Definition body from Lean':typedAnalysis?.validation?.includes('declaration')?'Signature checked by Lean':'Statement type checked by Lean'}</span>}</div>
        {current&&document&&plan&&primary?<>
          <div className="visual-title"><div><div className="canvas-breadcrumb"><button onClick={()=>chooseNode(current.tree.id)}>Statement</button>{selected!==current.tree.id&&<><span>/</span><span>{selectedNode?.binder?.name??selectedNode?.kind}</span></>}</div><h1>{primary.title}</h1></div><span className="auto-badge">Automatic composition</span></div>
          {checked?.definitionTree&&<div className="definition-mode" aria-label="Declaration view">{(['body','signature'] as const).map(view=><button key={view} className={inspectBody===(view==='body')?'active':''} aria-pressed={inspectBody===(view==='body')} onClick={()=>{const body=view==='body';const tree=body?checked.definitionTree!:checked.tree;setInspectBody(body);setSelected(tree.id);setObjectId('');setOverrideView('');setScenario(initialScenario(tree));}}>{view==='body'?'Definition body':'Typed signature'}</button>)}<span>{inspectBody?'The body describes the result under its parameters.':'Parameters specify inputs; they do not assert a proposition.'}</span></div>}
          <div className="document-stats"><span><b>{document.objects.length}</b> objects</span><span><b>{document.relations.length}</b> relationships</span><span><b>{document.choices.length}</b> choices</span><span><b>{allNodes.length}</b> fragments</span></div>
          <div className="view-tabs" aria-label="Representations">{plan.views.map(v=><button key={v.id} className={primary.id===v.id?'active':''} aria-pressed={primary.id===v.id} title={v.title} onClick={()=>{setOverrideView(v.id);if(v.fidelity==='numerical')setInspectorTab('scenario');}}>{kindLabel[v.kind]}{v.id===plan.primaryViewId&&<span className="recommended-dot"/>}</button>)}</div>
          <article className="view-card primary-view"><header><div><span className="view-index">01</span><strong>{primary.title}</strong></div><span className={`fidelity ${primary.fidelity}`}>{primary.fidelity==='numerical'?'Numerical illustration':primary.fidelity==='symbolic'?'Symbolic relationships':'Formal structure'}</span></header>{scene&&(scene.context.length>0||scene.guards.length>0)&&<div className="view-context">{scene.context.map((c,i)=><span key={i}>{c}</span>)}{scene.guards.length>0&&<span>Under {scene.guards.length} local {scene.guards.length===1?'assumption':'assumptions'}</span>}</div>}{renderView(primary)}<div className="view-reason"><span>Why this view</span><p>{primary.reason}</p></div></article>
          {supports.map((view,i)=><article className="view-card supporting-view" key={view.id}><header><div><span className="view-index">0{i+2}</span><strong>{view.title}</strong></div><span className="fidelity">{kindLabel[view.kind]}</span></header>{renderView(view)}</article>)}
          {expandNames.length>0&&<div className="expansion-note">{allNodes.filter(n=>n.expansion).length?`${allNodes.filter(n=>n.expansion).length} definition expansions checked by Lean for definitional equality.`:'No selected definition occurred at an expandable fragment head.'}</div>}
          <details className="lean-details" open><summary>{selected===current.tree.id?(checked?.definitionTree&&inspectBody?'Definition body':typedAnalysis?.validation?.includes('declaration')?'Typed signature':'Elaborated statement'):'Selected fragment · enclosing scope retained'}</summary><pre>{selectedNode?.lean}</pre></details>
          <details className="coverage-details"><summary>Interpretation coverage <span>{plan.coverage.interpreted} interpreted · {plan.coverage.partial} partial · {plan.coverage.structural} structural fragments</span></summary><p>{plan.explanation}</p>{document.opaqueRegions.slice(0,12).map(r=><button className="opaque-region" key={r.id} onClick={()=>chooseNode(r.nodeId)}><code>{r.label}</code><span>{r.reason}</span></button>)}{document.opaqueRegions.length>12&&<p>{document.opaqueRegions.length-12} further regions remain in the exported document.</p>}</details>
          <div className="trust-note">The diagrams explain structure and illustrate conditions. A well-typed statement may be false; samples do not prove quantified claims.</div>
        </>:<div className="empty-view"><div className="empty-orbit"><span>∀</span><i>∈</i></div><h1>{busy?'Reading the mathematical structure':analysis?'Your source has changed':'From a statement to its structure'}</h1><p>{busy?'Lean is resolving types, scope, and definitions. The first analysis starts the local environment.':'Interpret the current Lean input to build connected views of its objects, relationships, and choices.'}</p></div>}
      </section>
      <aside className="scenario-panel inspector"><div className="panel-heading"><span className="eyebrow">INSPECTOR</span>{current&&<button className="quiet-button" onClick={()=>{setObjectId('');setScenario(initialScenario(current.tree));}}>Reset</button>}</div>
        <div className="source-tabs"><button className={inspectorTab==='objects'?'active':''} onClick={()=>setInspectorTab('objects')}>Objects</button><button className={inspectorTab==='scenario'?'active':''} onClick={()=>setInspectorTab('scenario')}>Scenario</button></div>
        {inspectorTab==='objects'?<>
          {selectedObject?<div className="object-detail"><span className="object-kind">{selectedObject.kind}</span><h2>{selectedObject.label}</h2><pre>{selectedObject.type||'Type retained in expression'}</pre><span className="eyebrow">APPEARS IN</span>{[...new Set(selectedObject.provenance.map(p=>p.nodeId))].map(id=><button className="object-occurrence" key={id} onClick={()=>chooseNode(id)}>{allNodes.find(n=>n.id===id)?.lean??id}<span>↗</span></button>)}<button className="quiet-button" onClick={()=>setObjectId('')}>All objects</button></div>:<><p className="scenario-intro">Select an object in any diagram to follow its relationships.</p><div className="object-list">{document?.objects.filter(o=>o.binder||['set','function','point'].includes(o.kind)).slice(0,40).map(o=><button key={o.id} onClick={()=>setObjectId(o.id)}><span className={`object-monogram ${o.kind}`}>{o.kind==='function'?'↦':o.kind==='set'?'∈':o.binder?.role==='existential'?'∃':'·'}</span><span><strong>{o.label}</strong><small>{o.type||o.kind}</small></span><span>›</span></button>)}</div></>}
          {current&&<details className="definition-tools"><summary>Look inside a definition</summary><p>Expand a trusted definition to expose its underlying relationships. Expansion is explicit and bounded.</p><label className="field-label" htmlFor="definition">Definition name</label><input id="definition" list="definitions" value={expandName} onChange={e=>setExpandName(e.target.value)} placeholder="Function.Injective"/><datalist id="definitions">{(typedAnalysis?.definitions?.filter(d=>d.canExpand).map(d=>d.name)??availableConstants).map(n=><option key={n} value={n}/>)}</datalist><button className="toolbar-button" disabled={busy||!expandName.trim()} onClick={()=>expand(expandName)}>Expand definition ↗</button>{expandNames.length>0&&<><div className="expanded-list">{expandNames.map(n=><code key={n}>{n}</code>)}</div><button className="quiet-button" onClick={()=>{setExpandNames([]);currentKey.current=JSON.stringify([source,mode,[]]);void analyze(source,mode,[]);}}>Return to original structure</button></>}</details>}
        </>:<><h2>Choices, in order</h2><p className="scenario-intro">Each numerical view shares this scenario. Changing an earlier choice clears dependent witnesses.</p><div className="quantifier-key"><span><b>∀</b> arbitrary choice</span><span><b>∃</b> candidate witness</span></div><div className="variables">{binders.map(b=><VariableControl key={b.id} binder={b} value={scenario[b.id]} names={names} onChange={value=>changeVariable(b.id,value)}/>)}</div>{sample&&<div className="sample-status"><span className="eyebrow">AT THIS SAMPLE</span><strong className={sample.status==='false'?'sample-false':''}>{sample.status==='unknown'?'No numerical decision':sample.status==='true'?'Condition holds numerically':'Condition fails numerically'}</strong><p>{sample.status==='unknown'?sample.reason:sample.explanation}</p><span className="small muted">Approximate values, not a proof.</span></div>}{scene?.guards.length?<div className="assumptions"><span className="eyebrow">ASSUMPTIONS IN SCOPE</span>{scene.guards.map((g,i)=>{const value=evaluatePredicate(g,scenario);return <p key={i}><code>{allNodes.find(n=>n.expression===g)?.lean??'Local assumption'}</code><br/><span className={value.status==='false'?'sample-false':''}>{value.status==='unknown'?'Symbolic assumption':value.status==='true'?'Satisfied numerically':'Not satisfied at this sample'}</span></p>;})}</div>:null}</>}
        {!current&&<p className="scenario-footnote">The inspector will show the objects and choices in your next analysis.</p>}
      </aside>
    </main><footer><span>StatementLens <span className="footer-divider">/</span> Mathematical structure, made inspectable</span><span>Codex under the supervision of Neil Yuanting Li</span></footer>
  </div>;
}
