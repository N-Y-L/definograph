import type { DiagramTextSize } from './map-diagram-layout';

export function estimatedMathLabelSize(source: string, fontSize: number): DiagramTextSize {
  return { width: Math.max(fontSize, [...source].length * fontSize), height: fontSize * 1.8, ascent: fontSize * 1.3, descent: fontSize * .5 };
}
/** HTML client boxes include the SVG's screen scale; divide it out before any
 * figure layout uses them. MathML is absolutely positioned outside this probe. */
export function measureMathLabel(group: SVGGElement): DiagramTextSize | undefined {
  const natural = group.querySelector<HTMLElement>('[data-math-measure]');
  const marker = group.querySelector<HTMLElement>('[data-math-baseline]');
  const matrix = group.getScreenCTM();
  if (!natural || !marker || !matrix) return;
  const scaleX = Math.hypot(matrix.a, matrix.b), scaleY = Math.hypot(matrix.c, matrix.d);
  if (!scaleX || !scaleY) return;
  const box = natural.getBoundingClientRect(), baseline = marker.getBoundingClientRect().top;
  const width = box.width / scaleX, height = box.height / scaleY;
  const ascent = (baseline - box.top) / scaleY, descent = (box.bottom - baseline) / scaleY;
  if (![width, height, ascent, descent].every(Number.isFinite) || width <= 0 || height <= 0
    || ascent < 0 || descent < 0 || width > 32768 || height > 4096) return;
  return { width, height, ascent, descent };
}
export function sameMathLabelSize(a: DiagramTextSize | undefined, b: DiagramTextSize): boolean {
  return !!a && (['width', 'height', 'ascent', 'descent'] as const).every(key => Math.abs(a[key] - b[key]) < .25);
}
