import { Component, type ReactNode } from 'react';

/** Optional editor/typesetting chunks must never take down the current statement. */
export class FeatureBoundary extends Component<{ fallback: ReactNode; children: ReactNode }, { failed: boolean }> {
  state = { failed: false };
  static getDerivedStateFromError() { return { failed: true }; }
  render() { return this.state.failed ? this.props.fallback : this.props.children; }
}
