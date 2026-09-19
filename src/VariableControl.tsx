import { useState } from 'react';
import type { Binder, ScenarioValue } from './core';
import { MAX_NUMERICAL_DIMENSION } from './core/limits';

export function VariableControl({binder, value, onChange, names}: {binder: Binder; value: ScenarioValue | undefined; onChange: (value: ScenarioValue) => void; names: Record<string, string>}) {
  const [coordinate, setCoordinate] = useState(0);
  if (binder.role === 'assumption' || binder.role === 'lambda') return null;
  const vectorDimension = binder.dimension ?? (binder.domain?.endsWith('2') ? 2 : undefined);
  const supportedVector = binder.domain && ['sup2', 'euclidean2', 'supN', 'euclideanN'].includes(binder.domain) && vectorDimension !== undefined && Number.isSafeInteger(vectorDimension) && vectorDimension >= 1 && vectorDimension <= MAX_NUMERICAL_DIMENSION;
  const supported = binder.domain === 'real' || supportedVector;
  const current = supported ? value ?? (binder.domain === 'real' ? 0 : Array.from({length: vectorDimension!}, () => 0)) : 0;
  const values = typeof current === 'number' ? [current] : current;
  const selectedCoordinate = Math.min(coordinate, Math.max(0, values.length - 1));
  const displayedCoordinates = values.length > 8 ? [selectedCoordinate] : values.map((_, index) => index);
  return <div className="variable">
    <div className="variable-heading"><strong><span className={`role ${binder.role}`}>{binder.role === 'existential' ? '∃' : binder.role === 'parameter' ? '↦' : '∀'}</span>{binder.name}</strong><span>{binder.role === 'existential' ? 'candidate witness' : binder.role === 'parameter' ? 'function input' : 'representative'}</span></div>
    {!supported ? <p className="muted small">{binder.type} · symbolic{vectorDimension && vectorDimension > MAX_NUMERICAL_DIMENSION ? ` · numerical controls support up to ${MAX_NUMERICAL_DIMENSION} coordinates` : ''}</p> : <>
      {value === undefined && <p className="pending">Choose a new value for this scenario. <button className="quiet-button" onClick={() => onChange(current)}>Use {typeof current === 'number' ? current : 'these coordinates'}</button></p>}
      {values.length > 8 && <label className="coordinate-selector"><span>Edit coordinate · {values.length} total</span><select aria-label={`${binder.name} coordinate to edit`} value={selectedCoordinate} onChange={event => setCoordinate(Number(event.target.value))}>{values.map((_, index) => <option key={index} value={index}>x{index + 1}</option>)}</select></label>}
      {displayedCoordinates.map(i => { const v = values[i]; return <label className="coordinate-control" key={i}><span>{values.length > 1 ? `x${i + 1}` : binder.name}</span><input aria-label={`${binder.name}${values.length > 1 ? ` coordinate ${i + 1}` : ''}`} type="range" min={Math.min(-4, v)} max={Math.max(4, v)} step="0.05" value={v} onChange={event => {const next = Number(event.target.value); onChange(typeof current === 'number' ? next : values.map((x, j) => j === i ? next : x));}}/><input aria-label={`${binder.name}${values.length > 1 ? ` coordinate ${i + 1}` : ''} value`} type="number" step="0.05" value={Number(v.toFixed(5))} onChange={event => { if (event.target.value === '') return; const next = Number(event.target.value); if (Number.isFinite(next) && Math.abs(next) <= 1000000) onChange(typeof current === 'number' ? next : values.map((x,j) => j === i ? next : x)); }}/></label>; })}
    </>}
    {binder.role === 'existential' && <p className="dependency">{binder.dependsOn.length ? `May depend on ${binder.dependsOn.map(id => names[id] ?? id).join(', ')}.` : 'Chosen before the variables that follow.'}</p>}
  </div>;
}
