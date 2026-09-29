import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { afterEach, describe, expect, it, vi } from 'vitest';
import { FigureScroll, measureOverflow, overflowAttributes, watchOverflow } from './FigureScroll';

const size = (scrollWidth: number, clientWidth: number, scrollHeight = 300, clientHeight = scrollHeight) => ({ scrollWidth, clientWidth, scrollHeight, clientHeight });

describe('figure scroll frames', () => {
  afterEach(() => { vi.unstubAllGlobals(); });

  it('render as a plain frame with no Tab stop, role or label until they overflow', () => {
    const rendered = renderToStaticMarkup(createElement(FigureScroll, { label: 'Plot; scroll to see all of it', className: 'plot-scroll', children: createElement('svg') }));
    expect(rendered).toBe('<div class="figure-scroll plot-scroll"><svg></svg></div>');
  });

  it('count horizontal overflow, and vertical overflow only for frames that scroll vertically', () => {
    expect(measureOverflow(size(1100, 1100))).toBe('');
    expect(measureOverflow(size(585, 282))).toBe('x');
    expect(measureOverflow(size(1108, 1108, 1450, 638))).toBe('');
    expect(measureOverflow(size(1108, 1108, 1450, 638), true)).toBe('y');
    expect(measureOverflow(size(816, 240, 1068, 638), true)).toBe('x y');
  });

  it('become a labelled, focusable group only while their content overflows', () => {
    expect(overflowAttributes('', 'Plot; scroll to see all of it')).toEqual({});
    expect(overflowAttributes('x', 'Plot; scroll to see all of it')).toEqual({ role: 'group', tabIndex: 0, 'aria-label': 'Plot; scroll to see all of it', 'data-overflow': 'x' });
    expect(overflowAttributes('y', 'Objects and relations diagram')).toMatchObject({ tabIndex: 0, 'data-overflow': 'y' });
  });

  it('follow the frame as it is resized until they stop watching', () => {
    const observers: FakeObserver[] = [];
    class FakeObserver {
      targets: unknown[] = []; disconnected = false; callback: () => void;
      constructor(callback: () => void) { this.callback = callback; observers.push(this); }
      observe(target: unknown) { this.targets.push(target); }
      disconnect() { this.disconnected = true; }
    }
    vi.stubGlobal('ResizeObserver', FakeObserver);
    const frame = size(1100, 1100);
    const reports: string[] = [];
    const stop = watchOverflow(frame as unknown as Element, false, overflow => reports.push(overflow));
    observers[0]!.callback();
    Object.assign(frame, size(585, 282)); observers[0]!.callback();
    Object.assign(frame, size(700, 700)); observers[0]!.callback();
    expect(reports).toEqual(['', 'x', '']);
    expect(observers[0]!.targets).toEqual([frame]);
    stop();
    expect(observers[0]!.disconnected).toBe(true);
  });
});
