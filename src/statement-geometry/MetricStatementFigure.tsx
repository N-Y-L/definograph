import type { BallScene } from '../core';
import { FigureScroll } from '../components/FigureScroll';
import { useDiagramText } from '../components/use-diagram-text';
import { MathLabel } from '../components/MathLabel';
import { expressionDisplayNode, expressionMathDisplay, mathDisplay, sourceMathDisplay, withMathProse } from '../notation/math-display';
import { layoutMetricShape, layoutMetricDistance } from './metric-region-layout';
import { layoutMetricInterval } from './metric-interval-layout';
import { metricReading, type MetricReading } from './model';
import './metric-statement.css';

// Integer canvas extents times 3/4 land on exact CSS quarter-pixels. Keeping the
// minimum scale fixed avoids font-hinting/resize feedback for long fallback text.
const minimumLabelScale = .75;

/** Endpoint formulas keep their alignment with the interval as their glyphs grow. */
function MetricIntervalDiagram({ scene, reading: m, condition }: { scene: BallScene; reading: MetricReading; condition: string }) {
  const text = useDiagramText();
  const centerNode = expressionDisplayNode(scene.center), radiusNode = expressionDisplayNode(scene.radius);
  const endpoint = (operator: 'sub' | 'add', source: string) => centerNode && radiusNode
    ? mathDisplay({ kind: 'binary', operator, left: centerNode, right: radiusNode }, source) : sourceMathDisplay(source);
  const left = endpoint('sub', `${m.center} − ${m.radius}`), right = endpoint('add', `${m.center} + ${m.radius}`);
  const center = withMathProse(expressionMathDisplay(scene.center, m.center), 'center ');
  const point = scene.point ? withMathProse(expressionMathDisplay(scene.point, m.point), '', m.boundary === 'sphere' ? ' (either endpoint)' : '') : undefined;
  const layout = layoutMetricInterval({ left: text.size('left', left.source, 14), right: text.size('right', right.source, 14),
    center: text.size('center', center.source, 14), point: point ? text.size('point', point.source, 14) : undefined }, m.boundary === 'sphere');
  return <FigureScroll label="Metric region diagram; scroll to see all of it"><svg ref={text.ref}
    style={{ minWidth: layout.width * minimumLabelScale, maxHeight: 'none', height: 'auto', aspectRatio: `${layout.width} / ${layout.height}` }}
    viewBox={`0 0 ${layout.width} ${layout.height}`} role="img" aria-label={`${condition}. Positions are schematic; no coordinates are selected.`}>
    <line x1={layout.leftX - 50} y1={layout.axisY} x2={layout.rightX + 50} y2={layout.axisY} className="metric-axis"/>
    {m.boundary !== 'sphere' && <line x1={layout.leftX} y1={layout.axisY} x2={layout.rightX} y2={layout.axisY} className="metric-interval"/>}
    {[layout.leftX, layout.rightX].map(x => <circle key={x} cx={x} cy={layout.axisY} r="5" className={`metric-endpoint ${m.boundary}`}/>)}
    <MathLabel label={left} labelKey="left" x={layout.leftX} y={layout.endpointY} fontSize={14} textAnchor="middle"/>
    <MathLabel label={right} labelKey="right" x={layout.rightX} y={layout.endpointY} fontSize={14} textAnchor="middle"/>
    <MathLabel label={center} labelKey="center" x={layout.centerX} y={layout.centerY} fontSize={14} textAnchor="middle"/>
    {point && <><circle cx={layout.pointX} cy={layout.axisY} r="3" className="metric-point"/>
      <MathLabel label={point} labelKey="point" x={layout.pointX} y={layout.pointY} fontSize={14} textAnchor="middle"/></>}
  </svg></FigureScroll>;
}

function MetricRegionDiagram({ scene, reading: m, condition }: { scene: BallScene; reading: MetricReading; condition: string }) {
  const text = useDiagramText();
  const center = expressionMathDisplay(scene.center, m.center), radius = expressionMathDisplay(scene.radius, m.radius);
  const point = scene.point ? expressionMathDisplay(scene.point, m.point) : undefined;
  const centerLabel = withMathProse(center, 'center ');
  const title = withMathProse(center, 'Distance from ', ` · all ${m.dimension} dimensions`);
  const zero = mathDisplay({ kind: 'literal', value: 0 });
  const description = m.boundary === 'sphere' ? 'At the radius' : m.boundary === 'closed' ? 'At most the radius' : 'Below the radius';
  const shape = layoutMetricShape({ center: text.size('center', centerLabel.source, 14), radius: text.size('radius', radius.source, 14),
    point: point ? text.size('point', point.source, 14) : undefined }, m.boundary === 'sphere');
  const distance = layoutMetricDistance({ title: text.size('title', title.source, 14), zero: text.size('zero', zero.source, 14),
    radius: text.size('radius', radius.source, 14), description: text.size('description', description, 14) });
  const layout = m.presentation === 'distance' ? distance : shape;
  return <FigureScroll label="Metric region diagram; scroll to see all of it"><svg ref={text.ref}
    style={{ minWidth: layout.width * minimumLabelScale, maxHeight: 'none', height: 'auto', aspectRatio: `${layout.width} / ${layout.height}` }}
    viewBox={`0 0 ${layout.width} ${layout.height}`} role="img" aria-label={`${condition}. Positions are schematic; no coordinates are selected.`}>
    {m.presentation === 'distance' ? <>
      <MathLabel label={title} labelKey="title" x={distance.width / 2} y={distance.titleY} fontSize={14} textAnchor="middle"/>
      <line x1={distance.leftX} y1={distance.axisY} x2={distance.rightX + 70} y2={distance.axisY} className="metric-axis"/>
      {m.boundary !== 'sphere' && <line x1={distance.leftX} y1={distance.axisY} x2={distance.rightX} y2={distance.axisY} className="metric-interval"/>}
      <circle cx={distance.rightX} cy={distance.axisY} r="5" className={`metric-endpoint ${m.boundary}`}/>
      <MathLabel label={zero} labelKey="zero" x={distance.leftX} y={distance.endpointY} fontSize={14} textAnchor="middle"/>
      <MathLabel label={radius} labelKey="radius" x={distance.rightX} y={distance.endpointY} fontSize={14} textAnchor="middle"/>
      <text data-diagram-label="description" x={distance.width / 2} y={distance.descriptionY} textAnchor="middle">{description}</text>
    </> : <>
      {m.presentation === 'circle' ? <circle cx={shape.centerX} cy={shape.centerY} r="72" className={`metric-region ${m.boundary}`}/>
        : <rect x={shape.centerX - 72} y={shape.centerY - 72} width="144" height="144" className={`metric-region ${m.boundary}`}/>}
      <line x1={shape.centerX} y1={shape.centerY} x2={shape.centerX + 72} y2={shape.centerY} className="metric-radius"/>
      <circle cx={shape.centerX} cy={shape.centerY} r="3" className="metric-center"/>
      <MathLabel label={centerLabel} labelKey="center" x={shape.centerX} y={shape.centerLabelY} fontSize={14} textAnchor="middle"/>
      <MathLabel label={radius} labelKey="radius" x={shape.radiusX} y={shape.radiusY} fontSize={14} textAnchor="start"/>
      {point && <>
        <path d={`M${shape.pointX} ${shape.pointY - 6} V${shape.pointLeaderTop}`} className="metric-label-leader"/>
        <circle cx={shape.pointX} cy={shape.pointY} r="4" className="metric-point"/>
        <MathLabel label={point} labelKey="point" x={shape.pointX} y={shape.pointLabelY} fontSize={14} textAnchor="middle"/>
      </>}
    </>}
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
        {m.presentation === 'interval' ? <MetricIntervalDiagram scene={scene} reading={m} condition={condition}/>
          : <MetricRegionDiagram scene={scene} reading={m} condition={condition}/>}
        <div className="metric-condition">{condition}</div>
      </>}
    {m.sign === undefined && <div className="metric-radius-cases"><span><b>{m.radius} = 0</b> {m.zero === 'empty' ? 'empty region' : `only ${m.center}`}</span><span><b>{m.radius} &lt; 0</b> empty region</span></div>}
    <figcaption>{m.signFromAssumption ? `Uses the local assumption 0 < ${m.radius}. ` : ''}{m.presentation === 'distance' ? 'Distance condition, without choosing a projection or coordinates.' : 'Schematic positions; no coordinates chosen. Named points may coincide.'} {m.boundary === 'open' ? 'Boundary excluded.' : m.boundary === 'closed' ? 'Boundary included.' : 'Boundary only.'}</figcaption>
  </figure>;
}
