import { createRoot } from 'react-dom/client';
import { lazy, Suspense } from 'react';
import App from './App';
import './styles.css';

const PacketReader = lazy(() => import('./packets/PacketReader'));
const RawSourceReader = lazy(() => import('./packets/RawSourceReader'));
// The editor host always retains its versioned source/selection protocol.
const packetRoute = !window.acquireVsCodeApi && /^\/packet\/?$/.test(window.location.pathname);
const rawSourceRoute = !window.acquireVsCodeApi && /^\/source-data\/?$/.test(window.location.pathname);
createRoot(document.getElementById('root')!).render(rawSourceRoute
  ? <Suspense fallback={<p>Loading the source inspector…</p>}><RawSourceReader /></Suspense>
  : packetRoute
  ? <Suspense fallback={<p>Loading the packet reader…</p>}><PacketReader /></Suspense>
  : <App />);
