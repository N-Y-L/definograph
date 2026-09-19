import { useState } from 'react';
import type { PointerEvent, ReactNode } from 'react';
import { ballGeometry, evaluateExpression, evaluatePredicate, sliceGeometry } from './core';
import type { BallScene, Expr, Scenario, ScenarioValue, Scene } from './core';

const num = (n: number) => Number(n.toPrecision(4)).toString();
function expressionName(e: Expr): string { return e.kind === 'var' ? e.name : e.kind === 'const' ? e.name : e.kind === 'literal' ? String(e.value) : e.kind === 'lambda' ? `${e.binder.name} ↦ …` : 'f'; }
function scalar(e: Expr, state: Scenario): number | undefined { const r = evaluateExpression(e,state); return r.status === 'value' && typeof r.value === 'number' ? r.value : undefined; }
const metricLabel = (metric: string) => metric === 'real' ? 'Absolute distance on ℝ' : metric.startsWith('sup') ? 'Maximum metric · L∞' : 'Euclidean metric · L2';

function Frame({children, onPointerDown, onPointerMove, title = 'Geometric illustration'}: {children: ReactNode; onPointerDown?: (e: PointerEvent<SVGSVGElement>) => void; onPointerMove?: (e: PointerEvent<SVGSVGElement>) => void; title?: string}) {
  return <svg className="math-plot" viewBox="0 0 760 470" role="img" aria-label={title} onPointerDown={onPointerDown} onPointerMove={onPointerMove}>
    <title>{title}</title><defs><pattern id="small-grid" width="38" height="38" patternUnits="userSpaceOnUse"><path d="M 38 0 L 0 0 0 38" fill="none" stroke="#e8edf3" strokeWidth="1"/></pattern><clipPath id="plot-clip"><rect x="30" y="25" width="700" height="415"/></clipPath><marker id="arrowhead" markerWidth="8" markerHeight="8" refX="6" refY="3" orient="auto"><path d="M0 0 L6 3 L0 6" fill="none" stroke="#2a66b9"/></marker></defs>
    <rect width="760" height="470" fill="#fbfcfe"/><rect width="760" height="470" fill="url(#small-grid)"/>{children}
  </svg>;
}

function LinePlot({left, right, point, center, radius, boundary, empty}: {left?: number;right?:number;point?:number;center?:number;radius?:number;boundary?:string;empty?:boolean}) {
  const extent = Math.max(3, ...[left,right,point,center].filter((v):v is number => v !== undefined).map(Math.abs), radius ? Math.abs(radius)*1.4 : 0) * 1.15;
  const x = (v:number) => 380 + 300*v/extent;
  return <Frame title="A metric ball on the real line"><path d="M45 235 H715" stroke="#899bb0" strokeWidth="1.5"/>{[-2,-1,0,1,2].map(t => <g key={t}><path d={`M${x(t*extent/3)} 229 v12`} stroke="#899bb0"/><text x={x(t*extent/3)} y="266" textAnchor="middle" className="axis-text">{num(t*extent/3)}</text></g>)}<text x="710" y="215" className="axis-name">ℝ</text>
    {!empty && left !== undefined && right !== undefined && <g><path d={`M${x(left)} 235 H${x(right)}`} stroke="#669fe5" strokeWidth={boundary === 'sphere' ? 0 : 11} opacity=".5"/>{[left,right].map((v,i) => <circle key={i} cx={x(v)} cy="235" r="7" stroke="#2463af" fill={boundary === 'open' ? '#fbfcfe' : '#2463af'} strokeWidth="2"/>)}</g>}
    {center !== undefined && <text x={x(center)} y="302" textAnchor="middle" className="point-label">c = {num(center)}</text>}
    {point !== undefined && <g><circle cx={x(point)} cy="235" r="6" fill="#cf792c" stroke="white" strokeWidth="2"/><text x={x(point)} y="206" textAnchor="middle" className="point-label">x = {num(point)}</text></g>}
    {empty && <text x="380" y="145" textAnchor="middle" className="empty-geometry">∅ · empty set</text>}
  </Frame>;
}

function BallView({scene,scenario,onVariableChange}: {scene:BallScene;scenario:Scenario;onVariableChange:(id:string,value:ScenarioValue)=>void}) {
  const [axes,setAxes] = useState<[number,number]>([0,1]);
  const [fixed,setFixed] = useState<number[]>(Array(scene.dimension).fill(0));
  const raw = ballGeometry(scene,scenario);
  const slice = scene.dimension > 1 ? sliceGeometry(scene,scenario,{axes,fixed}) : null;
  const c = slice?.status === 'geometry' ? slice.center : [0,0];
  const r = slice?.status === 'geometry' ? slice.radius : 1;
  const extent = Math.max(2.7, Math.abs(r)*1.4);
  const scale = 190/extent;
  const sx = (v:number) => 380 + (v-c[0])*scale;
  const sy = (v:number) => 235 - (v-c[1])*scale;
  const shape = scene.metric.startsWith('sup') ? 'square' : 'disk';
  function place(event: PointerEvent<SVGSVGElement>) {
    if (scene.point?.kind !== 'var' || !slice || slice.status !== 'geometry') return;
    const svg = event.currentTarget; const matrix = svg.getScreenCTM(); if (!matrix) return;
    const pt = new DOMPoint(event.clientX,event.clientY).matrixTransform(matrix.inverse());
    if (pt.x < 30 || pt.x > 730 || pt.y < 25 || pt.y > 440) return;
    const value = [...fixed]; value[axes[0]] = Math.round(((pt.x-380)/scale+c[0])*100)/100; value[axes[1]] = Math.round(((235-pt.y)/scale+c[1])*100)/100;
    onVariableChange(scene.point.id,value);
  }
  const unknown = raw.status === 'unknown' ? raw.reason : slice?.status === 'unknown' ? slice.reason : null;
  return <div className="scene-view">
    <div className="plot-meta"><span className="metric-tag">{metricLabel(scene.metric)}</span><span>{scene.dimension > 2 ? `Ambient dimension ${scene.dimension} · coordinate slice` : scene.dimension === 1 ? 'Real line' : 'Full two-dimensional view'}</span></div>
    {scene.dimension > 2 && <div className="slice-settings"><div className="slice-heading"><strong>Slice through coordinates</strong>{axes.map((axis,i) => <select key={i} aria-label={`Slice axis ${i+1}`} value={axis} onChange={e => {const value=Number(e.target.value); setAxes(old => i === 0 ? [value,value === old[1] ? old[0] : old[1]] : [value === old[0] ? old[1] : old[0],value]);}}>{Array.from({length:scene.dimension},(_,j)=><option key={j} value={j}>x{j+1}</option>)}</select>)}</div><div className="slice-coordinates">{fixed.map((v,i)=> axes.includes(i) ? null : <label key={i}><span>x{i+1} = {num(v)}</span><input aria-label={`Slice fixed coordinate ${i+1}`} type="range" min="-3" max="3" step="0.05" value={v} onChange={e=>setFixed(old=>old.map((x,j)=>j===i?Number(e.target.value):x))}/></label>)}</div></div>}
    {unknown ? <div className="no-view"><h2>Choose the missing parameters</h2><p>{unknown}</p></div> : scene.dimension === 1 && raw.status === 'geometry' && typeof raw.center === 'number' ? <LinePlot left={raw.center-raw.radius} right={raw.center+raw.radius} center={raw.center} radius={raw.radius} point={typeof raw.point === 'number' ? raw.point : undefined} boundary={raw.boundary} empty={raw.empty}/> : slice?.status === 'geometry' ? <>
      <Frame title={`${scene.boundary === 'sphere' ? 'Sphere' : 'Ball'} in ${scene.dimension} dimensions, ${scene.dimension > 2 ? 'coordinate slice' : metricLabel(scene.metric)}`} onPointerDown={e=>{e.currentTarget.setPointerCapture(e.pointerId);place(e);}} onPointerMove={e=>{if(e.buttons===1)place(e);}}>
        <g clipPath="url(#plot-clip)"><path d="M35 235 H725 M380 30 V440" stroke="#aebdcd" strokeWidth="1"/>{[-2,-1,1,2].map(t => <g key={t}><path d={`M${380+t*scale} 230 v10 M375 ${235-t*scale} h10`} stroke="#aebdcd"/><text x={380+t*scale} y="256" textAnchor="middle" className="axis-text">{num(c[0]+t)}</text><text x="366" y={239-t*scale} textAnchor="end" className="axis-text">{num(c[1]+t)}</text></g>)}
        {!slice.empty && !slice.singleton && (shape === 'square' ? <rect x={sx(c[0]-r)} y={sy(c[1]+r)} width={Math.max(0,2*r*scale)} height={Math.max(0,2*r*scale)} className={`ball-region ${slice.boundary}`}/> : <circle cx="380" cy="235" r={Math.max(0,r*scale)} className={`ball-region ${slice.boundary}`}/>)}
        {!slice.empty && <><circle cx="380" cy="235" r={slice.singleton ? 5 : 3} fill="#2a66b9"/><text x="391" y="256" className="point-label">{scene.dimension > 2 ? "c_slice" : "c"}</text>{!slice.singleton && <><path d={`M380 235 L${sx(c[0]+r)} ${sy(c[1])}`} stroke="#4978ad" strokeDasharray="4 4"/><text x={sx(c[0]+r*.5)} y={sy(c[1])-12} className="radius-label">{scene.dimension > 2 ? 'slice r' : 'r'} = {num(r)}</text></>}</>}
        {slice.point && slice.pointInSlice !== false && <g><circle cx={sx(slice.point[0])} cy={sy(slice.point[1])} r="15" fill="#ce7a2c" opacity=".13"/><circle cx={sx(slice.point[0])} cy={sy(slice.point[1])} r="6" fill="#ce7a2c" stroke="white" strokeWidth="2"/><text x={sx(slice.point[0])+13} y={sy(slice.point[1])-12} className="point-label point-name">{scene.point?.kind === 'var' ? scene.point.name : 'P'}</text></g>}
        </g><text x="701" y="223" className="axis-name">x{axes[0]+1}</text><text x="391" y="45" className="axis-name">x{axes[1]+1}</text>
        {slice.empty && <><text x="380" y="145" textAnchor="middle" className="empty-geometry">∅</text><text x="380" y="178" textAnchor="middle" className="axis-text">{scene.dimension > 2 ? 'This slice does not intersect the object.' : 'The set is empty at this radius.'}</text></>}
      </Frame>
      {slice.pointInSlice === false && <div className="slice-warning">The representative point is outside this slice and is not drawn. Click the plot to place it in the slice.</div>}
      <div className="plot-legend"><span><i className="legend-region"/>{scene.boundary === 'sphere' ? scene.dimension > 2 ? 'Sphere ∩ coordinate plane' : 'Sphere boundary' : scene.boundary === 'open' ? 'Open ball · boundary excluded' : 'Closed ball · boundary included'}</span>{scene.point && <span><i className="legend-point"/>Representative point · click or drag</span>}</div>
      {scene.dimension > 2 && <p className="slice-note">{slice.note} {scene.boundary === 'sphere' && raw.status === 'geometry' && raw.radius > 0 ? `The original sphere has intrinsic dimension ${scene.dimension-1}.` : ''}</p>}
    </> : null}
  </div>;
}

export function SceneView({scene,scenario,onVariableChange}: {scene:Scene;scenario:Scenario;onVariableChange:(id:string,value:ScenarioValue)=>void}) {
  if (scene.kind === 'ball') return <BallView scene={scene} scenario={scenario} onVariableChange={onVariableChange}/>;
  if (scene.kind === 'mapping') return <div className="scene-view"><div className="plot-meta"><span className="metric-tag">Symbolic function diagram</span><span>{scene.property ?? 'mapping'} · no numerical model</span></div><Frame title="Symbolic domain and codomain mapping"><ellipse cx="195" cy="235" rx="104" ry="150" fill="#e7f0fc" stroke="#a9c6ed"/><ellipse cx="565" cy="235" rx="104" ry="150" fill="#f1edf8" stroke="#c4b6dc"/><text x="195" y="62" textAnchor="middle" className="axis-name">Domain</text><text x="565" y="62" textAnchor="middle" className="axis-name">Codomain</text><circle cx="220" cy="235" r="6" fill="#2a66b9"/><circle cx="540" cy="205" r="6" fill="#7053a0"/><path d="M234 231 Q380 145 528 202" fill="none" stroke="#2a66b9" strokeWidth="2" markerEnd="url(#arrowhead)"/><text x="201" y="265" className="point-label">x</text><text x="549" y="230" className="point-label">f(x)</text><text x="380" y="174" textAnchor="middle" className="radius-label">{expressionName(scene.fn)}</text></Frame><p className="slice-note">A schematic arrow shows how inputs and outputs are related. It does not establish {scene.property ?? 'any property of the function'}.</p></div>;
  if (scene.kind === 'graph') {
    const points=Array.from({length:241},(_,i)=>{const x=-4+i/30;const y=scalar(scene.body,{...scenario,[scene.input.id]:x});return {x,y};});
    let drawing=false; const path=points.map(({x,y})=>{if(y===undefined || !Number.isFinite(y) || Math.abs(y)>8){drawing=false;return '';} const cmd=drawing?'L':'M';drawing=true;return `${cmd}${380+x*70} ${235-y*45}`;}).join(' ');
    return <div className="scene-view"><div className="plot-meta"><span className="metric-tag">Explicit real function</span><span>241 numerical samples · x ∈ [−4, 4]</span></div><Frame title="Sampled graph of a real function"><path d="M40 235 H720 M380 35 V435" stroke="#aebdcd"/>{[-4,-2,2,4].map(v=><g key={v}><text x={380+v*70} y="257" textAnchor="middle" className="axis-text">{v}</text><text x="366" y={239-v*45} textAnchor="end" className="axis-text">{v}</text></g>)}<g clipPath="url(#plot-clip)"><path d={path} stroke="#2a66b9" strokeWidth="3" fill="none"/></g><text x="710" y="220" className="axis-name">x</text><text x="396" y="45" className="axis-name">f(x)</text>{!path.trim()&&<text x="380" y="140" textAnchor="middle" className="axis-text">No supported numerical evaluation.</text>}</Frame><p className="slice-note">The curve joins sampled values. It may miss discontinuities or other behavior between samples; it does not prove the stated property.</p></div>;
  }
  const currentValue=scenario[scene.variable.id]; const current=typeof currentValue==='number'?currentValue:undefined;
  const min=-4,max=4,step=(max-min)/200;
  const samples=Array.from({length:201},(_,i)=>{const x=min+i*step;return {x,result:evaluatePredicate(scene.expression,{...scenario,[scene.variable.id]:x})};});
  const px=(x:number)=>380+x*76;
  const left=scalar(scene.left,scenario),right=scalar(scene.right,scenario);
  return <div className="scene-view"><div className="plot-meta"><span className="metric-tag">Real-valued condition</span><span>Vary {scene.variable.name}; hold other choices fixed</span></div><Frame title="Numerical scan of a condition on the real line"><path d="M50 255 H710" stroke="#899bb0"/>{samples.filter(s=>s.result.status==='true').map((s,i)=><path key={i} d={`M${px(s.x)} 236 v38`} stroke="#79a9e4" strokeWidth="3" opacity=".7"/>)}{[-4,-3,-2,-1,0,1,2,3,4].map(x=><text key={x} x={px(x)} y="300" textAnchor="middle" className="axis-text">{x}</text>)}{current !== undefined && <g><circle cx={px(current)} cy="255" r="7" fill="#cf792c" stroke="#fff" strokeWidth="2"/><text x={px(current)} y="217" textAnchor="middle" className="point-label">{scene.variable.name} = {num(current)}</text></g>}<text x="380" y="130" textAnchor="middle" className="relation-text">{left===undefined?expressionName(scene.left):num(left)} {scene.relation==='lt'?'<':scene.relation==='le'?'≤':scene.relation==='eq'?'=':'≠'} {right===undefined?expressionName(scene.right):num(right)}</text></Frame><div className="plot-legend"><span><i className="legend-region"/>Sampled values satisfying this condition</span>{current !== undefined && <span><i className="legend-point"/>Current representative</span>}</div><p className="slice-note">A finite scan of [−4, 4]. Unshaded values may be false or numerically unsupported. The quantifiers still range over the full stated domain.</p></div>;
}
