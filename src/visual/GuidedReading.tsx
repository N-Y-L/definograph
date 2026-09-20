import type { CSSProperties, ReactNode } from 'react';
import type { ReadingCue, ReadingCuePlan } from '../reading/cues';
import type { ReadingDocument } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';
import { readingObjectColor } from './object-identity';
import './guided-reading.css';

interface Props {
  plan: ReadingCuePlan;
  cue: ReadingCue;
  reading: ReadingDocument;
  document: SemanticDocument;
  onChoose: (cue: ReadingCue) => void;
  onObjectSelect?: (id: string) => void;
  children: ReactNode;
}

/** Navigation changes attention, never the mathematical scope of the diagram. */
export function GuidedReading({ plan, cue, reading, document, onChoose, onObjectSelect, children }: Props) {
  const index = plan.cues.indexOf(cue);
  const nodes = new Map(reading.nodes.map(node => [node.id, node]));
  const objects = new Map(document.objects.map(object => [object.id, object]));
  const path = cue.branchPath.filter(part => !['body', 'result'].includes(part.edge.role));
  const assumptions = cue.assumptionNodeIds.flatMap(id => nodes.has(id) ? [nodes.get(id)!] : []);
  const inScope = cue.contextObjectIds.flatMap(id => objects.has(id) && objects.get(id)!.binder && objects.get(id)!.binder!.role !== 'assumption' && !(cue.intent === 'introduce' && cue.focusObjectIds.includes(id)) ? [objects.get(id)!] : []);
  function step(offset: number) { const next = plan.cues[index + offset]; if (next) onChoose(next); }
  return <section className="reading-guide" aria-label="Guided visual sequence">
    <nav className="rg-navigation" aria-label="Reading steps" onKeyDown={event => {
      if (event.target instanceof HTMLSelectElement) return;
      if (event.key === 'ArrowRight' || event.key === 'ArrowLeft') { event.preventDefault(); step(event.key === 'ArrowRight' ? 1 : -1); }
    }}>
      <div className="rg-position"><span>Reading step</span><label><span className="sr-only">Choose reading step</span><select aria-label="Choose reading step" value={cue.id} onChange={event => { const chosen = plan.cues.find(candidate => candidate.id === event.target.value); if (chosen) onChoose(chosen); }}>{plan.cues.map((candidate, ordinal) => <option key={candidate.id} value={candidate.id}>{ordinal + 1}. {candidate.title}</option>)}</select></label></div>
      <div className="rg-buttons"><span className="rg-count">{index + 1} / {plan.cues.length}</span><button type="button" aria-label="Previous reading step" disabled={index <= 0} onClick={() => step(-1)}>←</button><button type="button" aria-label="Next reading step" disabled={index >= plan.cues.length - 1} onClick={() => step(1)}>Next <span aria-hidden="true">→</span></button></div>
    </nav>
    <div className="rg-progress" aria-hidden="true"><span style={{ width: `${100 * (index + 1) / plan.cues.length}%` }}/></div>
    <div className="rg-envelope" aria-label="Enclosing mathematical context">
      {inScope.length > 0 && <div className="rg-in-scope"><span className="rg-context-label">In scope</span>{inScope.map(object => <button key={object.id} type="button" data-reading-object={object.id} style={{ '--object-color': readingObjectColor(object.id) } as CSSProperties} title={`${object.label} : ${object.type}`} onClick={() => onObjectSelect?.(object.id)}>{object.binder?.role === 'universal' ? '∀ ' : object.binder?.role === 'existential' ? '∃ ' : ''}{object.label}<span> : {object.type}</span></button>)}</div>}
      {path.length > 0 && <ol className="rg-logical-path">{path.map((part, ordinal) => <li key={`${part.nodeId}:${ordinal}`} data-logic-role={part.edge.role}>{part.edge.role === 'alternative' ? `Alternative ${part.edge.index + 1} · either or both may hold` : part.edge.role === 'conjunct' ? `Condition ${part.edge.index + 1} · required together` : part.edge.role === 'negated' ? 'Under negation' : part.edge.role === 'assumption' ? 'Given assumption' : part.edge.role === 'conclusion' ? 'Conditional conclusion' : part.edge.role === 'equivalence-left' ? 'First equivalent condition' : 'Second equivalent condition'}</li>)}</ol>}
      {assumptions.length > 0 && <details className="rg-assumptions" open><summary>{assumptions.length === 1 ? 'Given' : `${assumptions.length} assumptions in scope`}</summary><ul>{assumptions.map(node => <li key={node.id}><code>{node.lean}</code></li>)}</ul></details>}
    </div>
    <header className="rg-heading" aria-live="polite" aria-atomic="true"><span className="rg-stage-kind">{cue.stage.kind === 'contained' ? 'Inside the expression' : cue.intent === 'introduce' ? 'Objects and choices' : cue.intent === 'apply' ? 'Construction' : cue.intent === 'compare' ? 'Compare' : cue.intent === 'logic' ? 'Logical structure' : 'Condition'}</span><h2>{cue.title}</h2><p>{cue.detail}</p></header>
    <div className="rg-stage" data-cue-id={cue.id} data-cue-node={cue.nodeId} data-cue-scope={cue.scopeId} data-cue-kind={cue.stage.kind}>{children}</div>
    {plan.truncated && <p className="rg-limit">The guide has reached its display bound. {plan.omittedCueCount} further steps remain in the full statement below.</p>}
  </section>;
}
