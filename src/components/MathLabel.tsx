import { useLayoutEffect, useMemo, useRef, useState } from 'react';
import type { MathDisplay } from '../notation/math-display';
import { typesetStatement } from '../notation/render';
import { estimatedMathLabelSize, measureMathLabel, sameMathLabelSize } from './math-label-measure';
import 'katex/dist/katex.min.css';
import './math-label.css';

export interface MathLabelProps {
  label: MathDisplay;
  labelKey: string;
  x: number;
  /** SVG baseline, matching a text element's y coordinate. */
  y: number;
  fontSize?: number;
  textAnchor?: 'start' | 'middle' | 'end';
  className?: string;
  fill?: string;
}

/** Display-only HTML + MathML. Callers keep source IDs and events on their
 * enclosing SVG group. Only the strict local KaTeX renderer supplies markup. */
export function MathLabel({ label, labelKey, x, y, fontSize = 16, textAnchor = 'middle', className = '', fill }: MathLabelProps) {
  const group = useRef<SVGGElement>(null);
  const rendered = useMemo(() => label.latex ? typesetStatement(label.latex) : undefined, [label.latex]);
  const [measured, setMeasured] = useState<{ key: string; fontSize: number; size: ReturnType<typeof estimatedMathLabelSize> }>();
  const size = measured?.key === label.key && measured.fontSize === fontSize ? measured.size : estimatedMathLabelSize(label.source, fontSize);
  useLayoutEffect(() => {
    if (rendered?.status !== 'rendered' || !group.current) return;
    let alive = true;
    const update = () => {
      if (!alive || !group.current) return;
      const next = measureMathLabel(group.current);
      if (next) setMeasured(previous => previous?.key === label.key && previous.fontSize === fontSize && sameMathLabelSize(previous.size, next)
        ? previous : { key: label.key, fontSize, size: next });
    };
    update();
    const observer = new ResizeObserver(update);
    const natural = group.current.querySelector('[data-math-measure]');
    if (natural) observer.observe(natural);
    void document.fonts.ready.then(update);
    document.fonts.addEventListener('loadingdone', update);
    return () => { alive = false; observer.disconnect(); document.fonts.removeEventListener('loadingdone', update); };
  }, [label.key, fontSize, rendered]);
  if (rendered?.status !== 'rendered') return <text className={className} data-diagram-label={labelKey} data-diagram-source={label.source}
    data-math-fallback="source" x={x} y={y} textAnchor={textAnchor} fontSize={fontSize} fill={fill} aria-label={label.source}>{label.source}</text>;
  const left = x - (textAnchor === 'middle' ? size.width / 2 : textAnchor === 'end' ? size.width : 0);
  return <g ref={group} className={`diagram-math-label ${className}`} data-diagram-label={labelKey} data-diagram-source={label.source}
    data-math-label={label.key} data-math-baseline-y={y} role="group" aria-label={label.source} style={{ fontSize, ...(fill ? { fill, color: fill } : {}) }}>
    <title>{label.source}</title>
    <foreignObject x={left} y={y - size.ascent} width={Math.max(1, size.width)} height={Math.max(1, size.height)} overflow="visible">
      <div {...{ xmlns: 'http://www.w3.org/1999/xhtml' }} className="diagram-math-content" style={{ fontSize }}>
        <span data-math-measure="" className="diagram-math-measure">
          {label.prefix && <span className="diagram-math-prose">{label.prefix}</span>}
          <span className="diagram-math-typeset" dangerouslySetInnerHTML={{ __html: rendered.html }}/>
          {label.suffix && <span className="diagram-math-prose">{label.suffix}</span>}
          <span data-math-baseline="" className="diagram-math-baseline"/>
        </span>
      </div>
    </foreignObject>
  </g>;
}
