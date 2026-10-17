import { createRoot } from 'react-dom/client';
import { lazy, Suspense } from 'react';
import App from './App';
import { FeatureBoundary } from './components/FeatureBoundary';
import './styles.css';

const PacketReader = lazy(() => import('./packets/PacketReader'));
const RawSourceReader = lazy(() => import('./packets/RawSourceReader'));
// The editor host always retains its versioned source/selection protocol.
const packetRoute = !window.acquireVsCodeApi && /^\/packet\/?$/.test(window.location.pathname);
const rawSourceRoute = !window.acquireVsCodeApi && /^\/source-data\/?$/.test(window.location.pathname);
// The last resort, for an error outside every inner boundary, such as one in App's own compile steps.
const stopped = <main className="app-stopped" role="alert"><h1>Definograph stopped with an error.</h1>
  <p>{window.acquireVsCodeApi ? 'Close this Definograph panel and run Definograph: Visualize Selection again.' : 'Reload the page to start again.'} The details are in the developer console.</p></main>;
createRoot(document.getElementById('root')!).render(<FeatureBoundary fallback={stopped}>{rawSourceRoute
  ? <Suspense fallback={<p>Loading the source inspector…</p>}><RawSourceReader /></Suspense>
  : packetRoute
  ? <Suspense fallback={<p>Loading the packet reader…</p>}><PacketReader /></Suspense>
  : <App />}</FeatureBoundary>);
