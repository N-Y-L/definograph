import { Component, type ReactNode } from 'react';

interface BoundaryProps {
  fallback: ReactNode;
  children: ReactNode;
  /** What the children are drawn from. When any entry changes (by identity), a failure is cleared and the
   * children are drawn again, for example for the next statement or the next sample value. */
  resetKeys?: readonly unknown[];
}
interface BoundaryState { failed: boolean; resetKeys?: readonly unknown[] }

/** Entries are compared one by one, so a parent may pass a new array on every render. */
const sameKeys = (next: readonly unknown[] = [], previous: readonly unknown[] = []) =>
  next.length === previous.length && next.every((key, index) => Object.is(key, previous[index]));

/** Optional chunks and single diagrams must never take down the current statement: a render error
 * inside replaces only this part with its fallback. React still reports the error to the console. */
export class FeatureBoundary extends Component<BoundaryProps, BoundaryState> {
  state: BoundaryState = { failed: false };
  static getDerivedStateFromError(): Partial<BoundaryState> { return { failed: true }; }
  static getDerivedStateFromProps(props: BoundaryProps, state: BoundaryState): Partial<BoundaryState> | null {
    return sameKeys(props.resetKeys, state.resetKeys) ? null : { failed: false, resetKeys: props.resetKeys };
  }
  render() { return this.state.failed ? this.props.fallback : this.props.children; }
}

export const FIGURE_FAILURE = 'This diagram could not be drawn.';

/** One diagram that throws while drawing is replaced by a short note; the diagrams and text around it stay. */
export function FigureBoundary({ resetKeys, note = FIGURE_FAILURE, children }: { resetKeys?: readonly unknown[]; note?: ReactNode; children: ReactNode }) {
  return <FeatureBoundary resetKeys={resetKeys} fallback={<p className="figure-failure" role="note">{note}</p>}>{children}</FeatureBoundary>;
}
