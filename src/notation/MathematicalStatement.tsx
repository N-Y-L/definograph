import { useMemo } from 'react';
import { typesetStatement } from './render';
import 'katex/dist/katex.min.css';
import './notation.css';

export interface ReadableMath {
  provider:'leantex';
  status:'rendered'|'unavailable';
  latex?:string;
  reason?:string;
}

export function MathematicalStatement({notation,lean}:{notation?:ReadableMath;lean:string}) {
  const rendered=useMemo(()=>notation?.status==='rendered'&&notation.latex?typesetStatement(notation.latex):null,[notation]);
  return <section className="mathematical-statement" aria-label="Mathematical notation">
    <header><strong>Mathematical notation</strong><span>{rendered?.status==='rendered'?'LeanTeX · from the elaborated expression':'Lean notation'}</span></header>
    {rendered?.status==='rendered'?<div className="typeset-statement" dangerouslySetInnerHTML={{__html:rendered.html}}/>:<><pre>{lean}</pre><p>{rendered?.status==='unavailable'?rendered.reason:notation?.reason??'Typeset notation is unavailable in this worker build.'}</p></>}
    <details><summary>Compare with Lean</summary><pre>{lean}</pre><p>Typesetting is a reading aid. Lean’s checked expression remains the source for the diagrams.</p>{notation?.latex&&<><span>LaTeX</span><pre>{notation.latex}</pre></>}</details>
  </section>;
}
