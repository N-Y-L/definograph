import { createElement, isValidElement, type ReactElement, type ReactNode } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { FeatureBoundary, FIGURE_FAILURE, FigureBoundary } from './FeatureBoundary';

function ThrowingFigure(): ReactNode { throw new Error('This figure fails while drawing.'); }

type BoundaryProps = ConstructorParameters<typeof FeatureBoundary>[0];

/** React's server renderer, the only renderer these Node tests have, does not run error boundaries.
 * This drives the boundary through the two steps the browser renderer takes when a child throws:
 * getDerivedStateFromError, then render. Returns what the boundary then draws in place of its children. */
function drawnAfterChildThrows(element: ReactElement<BoundaryProps>): ReactNode {
  const boundary = new FeatureBoundary(element.props);
  boundary.state = { ...boundary.state, ...FeatureBoundary.getDerivedStateFromProps(element.props, boundary.state) };
  boundary.state = { ...boundary.state, ...FeatureBoundary.getDerivedStateFromError() };
  boundary.state = { ...boundary.state, ...FeatureBoundary.getDerivedStateFromProps(element.props, boundary.state) };
  return boundary.render();
}

describe('figure error boundary', () => {
  it('a figure that throws takes the whole render down when nothing catches it', () => {
    expect(() => renderToStaticMarkup(createElement('div', null, createElement(ThrowingFigure), createElement('p', null, 'Next figure'))))
      .toThrow('This figure fails while drawing.');
  });

  it('draws its figure unchanged while nothing fails', () => {
    const html = renderToStaticMarkup(createElement(FigureBoundary, null, createElement('svg', { 'aria-label': 'A working figure' })));
    expect(html).toBe('<svg aria-label="A working figure"></svg>');
  });

  it('replaces only the failed figure with a short note and keeps its neighbours', () => {
    const element = FigureBoundary({ children: createElement(ThrowingFigure) });
    expect(isValidElement(element) && element.type).toBe(FeatureBoundary);
    const replacement = drawnAfterChildThrows(element as ReactElement<BoundaryProps>);
    const html = renderToStaticMarkup(createElement('div', null, replacement, createElement('p', null, 'Next figure')));
    expect(html).toBe(`<div><p class="figure-failure" role="note">${FIGURE_FAILURE}</p><p>Next figure</p></div>`);
  });

  it('draws the figure again when anything it is drawn from changes, and not before', () => {
    const statement = {}, nextStatement = {}, sample = { x: 1 }, nextSample = { x: 2 };
    const failed = { failed: true, resetKeys: [statement, sample, 'object-a'] };
    const props = (...resetKeys: unknown[]): BoundaryProps => ({ fallback: null, children: null, resetKeys });
    // A parent passes a new array on every render; equal entries keep the failure.
    expect(FeatureBoundary.getDerivedStateFromProps(props(statement, sample, 'object-a'), failed)).toBeNull();
    for (const changed of [props(nextStatement, sample, 'object-a'), props(statement, nextSample, 'object-a'), props(statement, sample, 'object-b')])
      expect(FeatureBoundary.getDerivedStateFromProps(changed, failed)).toEqual({ failed: false, resetKeys: changed.resetKeys });
  });

  it('can name what was lost in its note', () => {
    const element = FigureBoundary({ note: 'The full visual statement could not be drawn.', children: createElement(ThrowingFigure) });
    const html = renderToStaticMarkup(createElement('div', null, drawnAfterChildThrows(element as ReactElement<BoundaryProps>)));
    expect(html).toBe('<div><p class="figure-failure" role="note">The full visual statement could not be drawn.</p></div>');
  });
});
