import { useLayoutEffect, useRef, useState } from 'react';
import type { DiagramTextSize } from './map-diagram-layout';

interface MeasuredText extends DiagramTextSize { text: string }

/** Measure glyphs in SVG units, independent of the figure's CSS scale. The
 * conservative first-render estimate keeps server output usable; the browser
 * replaces it before paint and remeasures changed labels, fonts and selection. */
export function useDiagramText() {
  const ref = useRef<SVGSVGElement>(null);
  const [sizes, setSizes] = useState<Record<string, MeasuredText>>({});
  const measured = useRef<Record<string, MeasuredText>>({});
  function measure() {
    if (!ref.current) return;
    const next: Record<string, MeasuredText> = {};
    for (const text of ref.current.querySelectorAll<SVGTextElement>('text[data-diagram-label]')) {
      const box = text.getBBox(), baseline = Number(text.getAttribute('y'));
      next[text.getAttribute('data-diagram-label')!] = { text: text.textContent ?? '', width: box.width, height: box.height,
        ascent: baseline - box.y, descent: box.y + box.height - baseline };
    }
    const previous = measured.current, keys = Object.keys(next);
    // Engines can vary subpixel glyph bounds slightly as the SVG resizes.
    // This tolerance is well below the layout's eight-unit label clearance.
    const unchanged = keys.length === Object.keys(previous).length && keys.every(key => {
      const a = next[key], b = previous[key];
      return b && a.text === b.text && ['width', 'height', 'ascent', 'descent'].every(field => Math.abs(a[field as keyof DiagramTextSize] - b[field as keyof DiagramTextSize]) < .25);
    });
    // Do not schedule an update when measurements agree. Other layout effects
    // (including the scroll frame's measurement) may also run in this commit.
    if (!unchanged) { measured.current = next; setSizes(next); }
  }
  useLayoutEffect(measure);
  useLayoutEffect(() => {
    const observer = new ResizeObserver(measure);
    observer.observe(ref.current!);
    document.fonts.addEventListener('loadingdone', measure);
    return () => { observer.disconnect(); document.fonts.removeEventListener('loadingdone', measure); };
  }, []);
  const size = (key: string, text: string, fontSize: number): DiagramTextSize => sizes[key]?.text === text ? sizes[key]
    : { width: [...text].length * fontSize, height: fontSize * 1.4, ascent: fontSize, descent: fontSize * .4 };
  return { ref, size };
}
