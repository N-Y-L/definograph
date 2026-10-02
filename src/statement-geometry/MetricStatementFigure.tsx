import type { BallScene } from '../core';
import { FigureScroll } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import { layoutMetricInterval } from './metric-interval-layout';
import { metricReading, type MetricReading } from './model';
import './metric-statement.css';

/** Endpoint formulas keep their alignment with the interval as their glyphs grow. */
function MetricIntervalDiagram({ reading: m, condition }: { reading: MetricReading; condition: string }) {
  const text = useDiagramText();
  const left = `${m.center} − ${m.radius}`, right = `${m.center} + ${m.radius}`;
  const center = `center ${m.center}`, point = m.point ? `${m.point}${m.boundary === 'sphere' ? ' (either endpoint)' : ''}` : undefined;
  const layout = layoutMetricInterval({ left: text.size('left', left, 14), right: text.size('right', right, 14),
    center: text.size('center', center, 14), point: point ? text.size('point', point, 14) : undefined }, m.boundary === 'sphere');
  return <FigureScroll label="Metric region diagram; scroll to see all of it"><svg ref={text.ref}
    style={{ minWidth: Math.ceil(layout.width * 10 / 14), maxHeight: 'none', height: 'auto', aspectRatio: `${layout.width} / ${layout.height}` }}
    viewBox={`0 0 ${layout.width} ${layout.height}`} role="img" aria-label={`${condition}. Positions are schematic; no coordinates are selected.`}>
    <line x1={layout.leftX - 50} y1={layout.axisY} x2={layout.rightX + 50} y2={layout.axisY} className="metric-axis"/>
    {m.boundary !== 'sphere' && <line x1={layout.leftX} y1={layout.axisY} x2={layout.rightX} y2={layout.axisY} className="metric-interval"/>}
    {[layout.leftX, layout.rightX].map(x => <circle key={x} cx={x} cy={layout.axisY} r="5" className={`metric-endpoint ${m.boundary}`}/>)}
    <text data-diagram-label="left" x={layout.leftX} y={layout.endpointY} textAnchor="middle">{left}</text>
    <text data-diagram-label="right" x={layout.rightX} y={layout.endpointY} textAnchor="middle">{right}</text>
    <text data-diagram-label="center" x={layout.centerX} y={layout.centerY} textAnchor="middle">{center}</text>
    {point && <><circle cx={layout.pointX} cy={layout.axisY} r="3" className="metric-point"/>
      <text data-diagram-label="point" x={layout.pointX} y={layout.pointY} textAnchor="middle">{point}</text></>}
  </svg></FigureScroll>;
}

/** A condition diagram uses symbols from the statement, never a Scenario. */
export function MetricStatementFigure({scene}:{scene:BallScene}) {
  const m = metricReading(scene);
  const empty = m.sign === -1 || m.sign === 0 && m.zero === 'empty';
  const singleton = m.sign === 0 && m.zero === 'singleton';
  const shapeTitle = m.boundary === 'sphere' ? 'Sphere' : m.boundary === 'closed' ? 'Closed ball' : 'Open ball';
  const condition = `dist(${m.point ?? 'point'}, ${m.center}) ${m.relation} ${m.radius}`;
  return <figure className="metric-statement" aria-label={`${shapeTitle}: ${condition}`}>
    <div className="metric-statement-heading"><strong>{shapeTitle}</strong><span>Symbolic geometry</span></div>
    {m.pointIsCenter ? <div className="metric-self-condition"><div className="metric-empty"><b>•</b><span>{m.center} is the center and the named point.</span></div><div className="metric-condition">dist({m.center}, {m.center}) = 0<br/>Membership condition: 0 {m.relation} {m.radius}</div></div>
      : empty ? <div className="metric-empty"><b>∅</b><span>The region is empty.{m.point ? ' No point belongs to it.' : ''}</span></div>
      : singleton ? <div className="metric-empty"><b>•</b><span>Only the center {m.center}.{m.point ? ` Membership requires ${m.point} = ${m.center}.` : ''}</span></div>
      : <>
        {m.sign === undefined && <p className="metric-case-title">Positive-radius case · {m.radius} &gt; 0</p>}
        {m.presentation === 'interval' ? <MetricIntervalDiagram reading={m} condition={condition}/> : <FigureScroll label="Metric region diagram; scroll to see all of it"><svg viewBox="0 0 460 200" role="img" aria-label={`${condition}. Positions are schematic; no coordinates are selected.`}>
          {m.presentation === 'circle' || m.presentation === 'square' ? <>
            {m.presentation === 'circle' ? <circle cx="205" cy="100" r="72" className={`metric-region ${m.boundary}`}/> : <rect x="133" y="28" width="144" height="144" rx="0" className={`metric-region ${m.boundary}`}/>}
            <line x1="205" y1="100" x2="277" y2="100" className="metric-radius"/>
            <circle cx="205" cy="100" r="3" className="metric-center"/><text x="191" y="122" textAnchor="end">{m.center}</text><text x="239" y="94" textAnchor="middle">{m.radius}</text>
            {m.point && <><circle cx={m.boundary === 'sphere' ? 205 : 175} cy={m.boundary === 'sphere' ? 28 : 69} r="4" className="metric-point"/><text x={m.boundary === 'sphere' ? 220 : 166} y={m.boundary === 'sphere' ? 27 : 62} textAnchor="end">{m.point}</text></>}
          </> : <>
            <text x="230" y="35" textAnchor="middle">Distance from {m.center} · all {m.dimension} dimensions</text>
            <line x1="80" y1="100" x2="390" y2="100" className="metric-axis"/>
            {m.boundary !== 'sphere' && <line x1="80" y1="100" x2="320" y2="100" className="metric-interval"/>}
            <circle cx="320" cy="100" r="5" className={`metric-endpoint ${m.boundary}`}/>
            <text x="80" y="127" textAnchor="middle">0</text><text x="320" y="127" textAnchor="middle">{m.radius}</text>
            <text x="230" y="165" textAnchor="middle">{m.boundary === 'sphere' ? 'At the radius' : m.boundary === 'closed' ? 'At most the radius' : 'Below the radius'}</text>
          </>}
        </svg></FigureScroll>}
        <div className="metric-condition">{condition}</div>
      </>}
    {m.sign === undefined && <div className="metric-radius-cases"><span><b>{m.radius} = 0</b> {m.zero === 'empty' ? 'empty region' : `only ${m.center}`}</span><span><b>{m.radius} &lt; 0</b> empty region</span></div>}
    <figcaption>{m.signFromAssumption ? `Uses the local assumption 0 < ${m.radius}. ` : ''}{m.presentation === 'distance' ? 'Distance condition, without choosing a projection or coordinates.' : 'Schematic positions; no coordinates chosen. Named points may coincide.'} {m.boundary === 'open' ? 'Boundary excluded.' : m.boundary === 'closed' ? 'Boundary included.' : 'Boundary only.'}</figcaption>
  </figure>;
}
