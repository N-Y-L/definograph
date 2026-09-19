import { useEffect, useMemo, useRef, useState } from 'react';
import type { Analysis, Binder, Scenario, ScenarioValue, Scene, StatementNode } from './core';
import { ballGeometry, collectBinders, discoverScenes, evaluatePredicate, initialScenario, updateScenario } from './core';
import { examples } from './examples';
import { SceneView } from './SceneView';

const symbols = ['∀', '∃', 'ℝ', '∈', '→', '∧', '↔', 'ε', 'δ', '≤'];
const flatten = (node: StatementNode): StatementNode[] => [node, ...node.children.flatMap(flatten)];
const mark: Record<string, string> = { forall: '∀', exists: '∃', implies: '→', and: '∧', or: '∨', iff: '↔', not: '¬', predicate: '·' };
function errorText(value: unknown): string { return typeof value === 'string' ? value : JSON.stringify(value); }

function StatementTree({node, selected, choose, sceneNodes, depth = 0}: {node: StatementNode; selected: string; choose: (id: string) => void; sceneNodes: Set<string>; depth?: number}) {
  return <div className="tree-branch">
    <button className={`tree-node ${node.id === selected ? 'selected' : ''}`} style={{paddingLeft: `${12 + Math.min(depth, 8) * 13}px`}} onClick={() => choose(node.id)} title={node.lean}>
      <span className={`logic-symbol ${node.kind}`}>{mark[node.kind]}</span><span className="tree-label">{node.binder && node.kind !== 'implies' ? `${node.binder.name} : ${node.binder.type}` : node.label || node.lean}</span>{sceneNodes.has(node.id) && <span className="plot-indicator" aria-label="Has a visual interpretation"/>}
    </button>
    {node.children.map(child => <StatementTree key={child.id} node={child} selected={selected} choose={choose} sceneNodes={sceneNodes} depth={depth + 1}/>)}
  </div>;
}

function VariableControl({binder, value, onChange, names}: {binder: Binder; value: ScenarioValue | undefined; onChange: (value: ScenarioValue) => void; names: Record<string, string>}) {
  if (binder.role === 'assumption' || binder.role === 'lambda') return null;
  const supported = binder.domain && !['unknown', 'realFunction'].includes(binder.domain);
  const current = value ?? (binder.domain === 'real' ? 0 : Array.from({length: binder.dimension ?? 2}, () => 0));
  const values = typeof current === 'number' ? [current] : current;
  return <div className="variable">
    <div className="variable-heading"><strong><span className={`role ${binder.role}`}>{binder.role === 'existential' ? '∃' : '∀'}</span>{binder.name}</strong><span>{binder.role === 'existential' ? 'candidate witness' : 'representative'}</span></div>
    {!supported ? <p className="muted small">{binder.type} · symbolic</p> : <>
      {value === undefined && <p className="pending">Choose a new value for this scenario. <button className="quiet-button" onClick={() => onChange(current)}>Use {typeof current === 'number' ? current : 'these coordinates'}</button></p>}
      {values.map((v, i) => <label className="coordinate-control" key={i}><span>{values.length > 1 ? `x${i + 1}` : binder.name}</span><input aria-label={`${binder.name}${values.length > 1 ? ` coordinate ${i + 1}` : ''}`} type="range" min={Math.min(-4, v)} max={Math.max(4, v)} step="0.05" value={v} onChange={event => {const next = Number(event.target.value); onChange(typeof current === 'number' ? next : values.map((x, j) => j === i ? next : x));}}/><input aria-label={`${binder.name}${values.length > 1 ? ` coordinate ${i + 1}` : ''} value`} type="number" step="0.05" value={Number(v.toFixed(5))} onChange={event => { if (event.target.value === '') return; const next = Number(event.target.value); if (Number.isFinite(next) && Math.abs(next) <= 1000000) onChange(typeof current === 'number' ? next : values.map((x,j) => j === i ? next : x)); }}/></label>)}
    </>}
    {binder.role === 'existential' && <p className="dependency">{binder.dependsOn.length ? `May depend on ${binder.dependsOn.map(id => names[id] ?? id).join(', ')}.` : 'Chosen before the variables that follow.'}</p>}
  </div>;
}

export default function App() {
  const [source, setSource] = useState(examples[0].source);
  const [exampleId, setExampleId] = useState(examples[0].id);
  const [analysis, setAnalysis] = useState<Analysis | null>(null);
  const [selected, setSelected] = useState('');
  const [sceneId, setSceneId] = useState('');
  const [scenario, setScenario] = useState<Scenario>({});
  const [busy, setBusy] = useState(false);
  const [error, setError] = useState('');
  const [health, setHealth] = useState<{ready: boolean; leanVersion?: string; issue?: string} | null>(null);
  const [showGuide, setShowGuide] = useState(false);
  const editor = useRef<HTMLTextAreaElement>(null);
  const request = useRef(0);
  const active = useRef<AbortController | null>(null);
  const sourceRef = useRef(source);
  sourceRef.current = source;
  const current = analysis?.source === source ? analysis : null;
  const allScenes = useMemo(() => current ? discoverScenes(current.tree) : [], [current]);
  const allNodes = useMemo(() => current ? flatten(current.tree) : [], [current]);
  const selectedNode = allNodes.find(node => node.id === selected) ?? current?.tree;
  const selectedIds = new Set(selectedNode ? flatten(selectedNode).map(node => node.id) : []);
  const scenes = allScenes.filter(scene => selectedIds.has(scene.nodeId));
  const scene = scenes.find(s => s.id === sceneId) ?? scenes[0];
  const binders = useMemo(() => current ? collectBinders(current.tree) : [], [current]);
  const names = Object.fromEntries(binders.map(b => [b.id, b.name]));
  const visibleBinders = scene?.scope ?? binders;
  const ball = scene?.kind === 'ball' ? ballGeometry(scene, scenario) : null;
  const result = ball?.status === 'geometry' && ball.membership ? ball.membership : scene ? evaluatePredicate(scene.expression, scenario) : null;

  async function analyze(text: string) {
    const generation = ++request.current;
    active.current?.abort();
    const controller = new AbortController(); active.current = controller;
    setBusy(true); setError('');
    try {
      const response = await fetch('/api/analyze', {method:'POST', headers:{'Content-Type':'application/json'}, body:JSON.stringify({source:text}), signal:controller.signal});
      const data = await response.json();
      if (generation !== request.current || sourceRef.current !== text) return;
      if (!response.ok || !data.ok) { setAnalysis(null); setError(errorText(data.error ?? data.diagnostics ?? 'The statement could not be elaborated.')); return; }
      const views = discoverScenes(data.tree);
      setAnalysis(data); setSelected(data.tree.id); setSceneId((views.find(s => s.kind === 'ball') ?? views.find(s => s.kind === 'graph') ?? views[0])?.id ?? ''); setScenario(initialScenario(data.tree));
    } catch (cause) { if (generation === request.current && sourceRef.current === text && !(cause instanceof DOMException && cause.name === 'AbortError')) { setAnalysis(null); setError('The local Lean service is unavailable. Start the application with npm run dev.'); } }
    finally { if (generation === request.current) setBusy(false); }
  }
  useEffect(() => {
    fetch('/api/health').then(r => r.json()).then(setHealth).catch(() => setHealth({ready:false,issue:'Local Lean service is unavailable.'}));
    void analyze(examples[0].source);
    return () => { active.current?.abort(); };
  }, []);
  function edit(text: string) { sourceRef.current = text; setSource(text); setError(''); }
  function loadExample(id: string) { const e = examples.find(item => item.id === id)!; setExampleId(id); edit(e.source); void analyze(e.source); }
  function changeVariable(binderId: string, value: ScenarioValue) { if (current) setScenario(old => updateScenario(current.tree, old, binderId, value)); }
  function insert(symbol: string) { const el = editor.current; const start = el?.selectionStart ?? source.length; const end = el?.selectionEnd ?? start; edit(source.slice(0,start) + symbol + source.slice(end)); requestAnimationFrame(() => { el?.focus(); el?.setSelectionRange(start + symbol.length, start + symbol.length); }); }

  return <div className="app-shell">
    <header className="topbar"><div className="brand"><span className="brand-icon">∈</span><span>Statement<span className="brand-light">Lens</span></span><span className="version">RESEARCH PREVIEW</span></div><div className="top-actions"><span className="local-label">Local workspace</span><button className="quiet-button" onClick={() => setShowGuide(!showGuide)} aria-expanded={showGuide}>How to read a view</button></div></header>
    {showGuide && <section className="guide"><button className="close-guide quiet-button" onClick={() => setShowGuide(false)}>Close</button><h2>Explore a statement without changing what it says.</h2><div className="guide-grid"><p><strong>∀ means any choice.</strong> A movable point represents one choice at a time. Its range belongs to the statement; the displayed sample does not establish a universal claim.</p><p><strong>∃ means a candidate witness.</strong> A witness can depend on earlier choices. Moving an earlier variable clears later witness choices; moving a later variable never adjusts an earlier witness.</p><p><strong>A slice is an intersection.</strong> In dimensions above two, the view fixes omitted coordinates. A 3-sphere has ambient dimension four. A coordinate slice does not show the whole object.</p><p><strong>Lean checks the statement’s type.</strong> This application does not prove the statement. Geometry is recognized from typed expressions; numerical evaluations are approximations.</p></div></section>}
    <main className="workspace">
      <aside className="source-panel">
        <div className="panel-heading"><span className="eyebrow">01 / STATEMENT</span><span className="language-badge">Lean 4</span></div>
        <label className="field-label" htmlFor="example">Start from an example</label>
        <select id="example" value={exampleId} disabled={busy} onChange={e => loadExample(e.target.value)}>{examples.map(e => <option value={e.id} key={e.id}>{e.title}</option>)}</select>
        <p className="example-description">{examples.find(e => e.id === exampleId)?.description}</p>
        <div className="editor-label"><label htmlFor="statement">Statement or condition</label><span>Ctrl / ⌘ + Enter</span></div>
        <textarea id="statement" ref={editor} spellCheck={false} value={source} onChange={e => edit(e.target.value)} onKeyDown={e => {if ((e.ctrlKey || e.metaKey) && e.key === 'Enter') {e.preventDefault(); if (!busy && source.trim()) void analyze(source);}}} aria-describedby="input-help"/>
        <div className="symbol-bar">{symbols.map(symbol => <button onClick={() => insert(symbol)} key={symbol} title={`Insert ${symbol}`}>{symbol}</button>)}</div>
        <p id="input-help" className="input-help">Enter a proposition with its variables, using <code>∀</code>. Definitions, imports, and proof scripts are outside this editor.</p>
        <button className="analyze-button" disabled={busy || !source.trim()} onClick={() => void analyze(source)}>{busy ? <><span className="spinner"/>Reading with Lean…</> : <>Analyze statement <span>↗</span></>}</button>
        <div className="engine-status">{health?.ready ? `Lean ${health.leanVersion?.match(/\d+\.\d+\.\d+/)?.[0] ?? '4'} · local process` : health?.issue ?? 'Connecting to Lean…'}</div>
        {error && <div className="error-box" role="alert"><strong>Lean could not read this statement.</strong><pre>{error}</pre><span>Correct the expression and analyze again. No diagram is inferred from invalid text.</span></div>}
        <div className="structure-heading"><span className="eyebrow">LOGICAL STRUCTURE</span><span>{allNodes.length || '—'} fragments</span></div>
        {current ? <div className="statement-tree" aria-label="Statement fragments"><StatementTree node={current.tree} selected={selected} choose={id => {setSelected(id); setSceneId('');}} sceneNodes={new Set(allScenes.map(s => s.nodeId))}/></div> : <p className="muted empty-tree">{analysis ? 'The source changed. Analyze to refresh its structure and views.' : 'Lean’s logical structure appears here after analysis.'}</p>}
      </aside>
      <section className="visual-panel">
        <div className="panel-heading"><span className="eyebrow">02 / VISUAL INTERPRETATION</span><span className="count-badge">{allScenes.length} available {allScenes.length === 1 ? 'view' : 'views'}</span></div>
        {current ? <>
          <div className="visual-title"><h1>{scene?.title ?? 'Inspect this fragment'}</h1><span className="status-tag">Elaborated by Lean</span></div>
          {scenes.length > 1 && <div className="view-tabs" role="tablist" aria-label="Available visual fragments">{scenes.map((s,i) => <button key={s.id} role="tab" aria-selected={s.id === scene?.id} className={s.id === scene?.id ? 'active' : ''} onClick={() => setSceneId(s.id)}>{s.kind === 'ball' ? s.boundary === 'sphere' ? 'Sphere' : 'Ball' : s.kind === 'graph' ? 'Function graph' : s.kind === 'mapping' ? 'Mapping' : 'Relation'} <span>{i + 1}</span></button>)}</div>}
          {scene ? <><SceneView key={scene.id} scene={scene} scenario={scenario} onVariableChange={changeVariable}/><div className="reading-strip"><span className="reading-symbol">{scene.kind === 'ball' ? '∈' : scene.kind === 'graph' || scene.kind === 'mapping' ? '↦' : '<'}</span><div><strong>Numerical illustration</strong><p>{scene.kind === 'ball' ? 'The region shows a recognized geometric object. Move the representative point and parameters to inspect the condition.' : scene.kind === 'mapping' ? 'The arrows describe the function’s role. A symbolic map does not assign numerical outputs.' : 'These values explore one scenario. They do not establish the quantified statement.'}</p></div></div></> : <div className="no-view"><span>⌁</span><h2>No registered geometric view</h2><p>This fragment is retained in the statement. Select a marked fragment in the logical structure to inspect a supported part.</p></div>}
          {scene?.context.length ? <div className="context-note"><strong>Logical context</strong> {scene.context.join(' · ')}</div> : null}
          <details className="lean-details" open><summary>{scene ? 'Visualized Lean fragment' : 'Selected Lean fragment'}</summary><pre>{(scene && allNodes.find(n => n.id === scene.nodeId)?.lean) || selectedNode?.lean}</pre></details>
          <div className="trust-note">A well-typed statement may be false. Lean elaboration, geometric interpretation, and numerical sampling are different checks.</div>
        </> : <div className="empty-view"><div className="empty-orbit"><span>∀</span><i>∈</i></div><h1>{busy ? 'Reading the mathematical structure' : analysis ? 'Ready for the next interpretation' : 'See the parts of a statement'}</h1><p>{busy ? 'Lean is resolving types, variables, and metric instances.' : 'Analyze a Lean proposition to discover its geometry and inspect its quantifiers.'}</p></div>}
      </section>
      <aside className="scenario-panel"><div className="panel-heading"><span className="eyebrow">03 / SCENARIO</span>{current && <button className="quiet-button" onClick={() => setScenario(initialScenario(current.tree))}>Reset</button>}</div>
        <h2>Choices, in order</h2><p className="scenario-intro">Move a representative. Keep track of which choices came first.</p>
        <div className="quantifier-key"><span><b>∀</b> arbitrary choice</span><span><b>∃</b> candidate witness</span></div>
        {current && <div className="variables">{visibleBinders.map(b => <VariableControl key={b.id} binder={b} value={scenario[b.id]} onChange={value => changeVariable(b.id, value)} names={names}/>)}</div>}
        {scene && <div className="sample-status"><span className="eyebrow">AT THIS SAMPLE</span><strong className={result?.status === 'false' ? 'sample-false' : ''}>{result?.status === 'unknown' ? 'No numerical decision' : result?.status === 'true' ? 'Condition holds numerically' : 'Condition fails numerically'}</strong><p>{result?.status === 'unknown' ? result.reason : result?.explanation}</p><span className="small muted">Approximate values, not a proof or certified counterexample.</span></div>}
        {scene && scene.guards.length > 0 && <div className="assumptions"><span className="eyebrow">ASSUMPTIONS IN SCOPE</span>{scene.guards.map((guard, i) => {const status = evaluatePredicate(guard, scenario); return <p key={i}><code>{allNodes.find(n => n.expression === guard)?.lean ?? 'Assumption'}</code><br/><span className={status.status === 'false' ? 'sample-false' : ''}>{status.status === 'true' ? 'Satisfied numerically' : status.status === 'false' ? 'Not satisfied at this sample' : 'Symbolic assumption'}</span></p>;})}</div>}
        <div className="scenario-footnote">The shaded region can represent infinitely many points. Only the selected representative is evaluated.</div>
      </aside>
    </main>
    <footer><span>StatementLens <span className="footer-divider">/</span> Local, read-only mathematical exploration</span><span>Codex under the supervision of Neil Yuanting Li</span></footer>
  </div>;
}
