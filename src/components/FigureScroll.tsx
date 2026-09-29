import { useLayoutEffect, useRef, useState, type ReactNode } from 'react';
import { flushSync } from 'react-dom';
import './figure-scroll.css';

/** The axes along which a frame's content is larger than the frame, as data-overflow tokens. */
export type FrameOverflow = '' | 'x' | 'y' | 'x y';

/** Horizontal overflow, and vertical overflow for a frame that also scrolls vertically. */
export function measureOverflow(frame: Pick<Element, 'scrollWidth' | 'clientWidth' | 'scrollHeight' | 'clientHeight'>, vertical = false): FrameOverflow {
  const x = frame.scrollWidth > frame.clientWidth, y = vertical && frame.scrollHeight > frame.clientHeight;
  return x && y ? 'x y' : x ? 'x' : y ? 'y' : '';
}

/** Reports the frame's overflow whenever the frame is resized, starting when observation begins; returns the function
 * that stops watching. */
export function watchOverflow(frame: Element, vertical: boolean, report: (overflow: FrameOverflow) => void): () => void {
  const observer = new ResizeObserver(() => report(measureOverflow(frame, vertical)));
  observer.observe(frame);
  return () => observer.disconnect();
}

/** Only a frame whose content overflows is a labelled group in the Tab order, so that it can be scrolled from the
 * keyboard, and only then does data-overflow shade the edges where more of the diagram lies (figure-scroll.css). */
export function overflowAttributes(overflow: FrameOverflow, label: string) {
  return overflow ? { role: 'group', tabIndex: 0, 'aria-label': label, 'data-overflow': overflow } : {};
}

/** The current overflow of the element the returned ref is attached to. `vertical` is for an element that also
 * scrolls vertically. */
export function useFrameOverflow<T extends HTMLElement>(vertical = false) {
  const frame = useRef<T>(null);
  const [overflow, setOverflow] = useState<FrameOverflow>('');
  // Committed within the resize's own frame, so a diagram never paints spilling out of a frame that cannot scroll yet.
  useLayoutEffect(() => watchOverflow(frame.current!, vertical, next => flushSync(() => setOverflow(next))), [vertical]);
  // Measured after every render too: a different diagram can change the content's width without resizing the frame.
  useLayoutEffect(() => setOverflow(measureOverflow(frame.current!, vertical)));
  return [frame, overflow] as const;
}

/** A diagram keeps the minimum width set by its own stylesheet. In a narrower column it scrolls inside this frame
 * instead of shrinking its labels. While the diagram fits, the frame adds no Tab stop and paints nothing. */
export function FigureScroll({ label, className, vertical = false, children }: { label: string; className?: string; vertical?: boolean; children: ReactNode }) {
  const [frame, overflow] = useFrameOverflow<HTMLDivElement>(vertical);
  return <div ref={frame} className={className ? `figure-scroll ${className}` : 'figure-scroll'} {...overflowAttributes(overflow, label)}>{children}</div>;
}
