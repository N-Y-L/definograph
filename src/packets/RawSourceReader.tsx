import { useEffect, useRef, useState } from 'react';
import { parseRawSourceText, type ImportedRawSource } from './raw-import';
import { RawSourceReading } from './RawSourceReading';
import './packet-reader.css';

interface ImportState { text: string; phase: 'empty' | 'editing' | 'reading' | 'checking' | 'ready' | 'invalid'; source?: ImportedRawSource; error?: string }

/** Local-only import of a declared raw frame, independent of packet evidence. */
export default function RawSourceReader() {
  const [state, setState] = useState<ImportState>({ text: '', phase: 'empty' });
  const generation = useRef(0);
  useEffect(() => () => { generation.current++; }, []);
  async function check(text: string, ticket: number) {
    setState({ text, phase: 'checking' });
    try {
      const source = await parseRawSourceText(text);
      if (ticket === generation.current) setState({ text, phase: 'ready', source });
    } catch (error) {
      if (ticket === generation.current) setState({ text, phase: 'invalid', error: error instanceof Error ? error.message : String(error) });
    }
  }
  async function readFile(file: File) {
    const ticket = ++generation.current;
    setState({ text: '', phase: 'reading' });
    try {
      if (file.size > 16 * 1024 * 1024) throw new Error('The file exceeds the 16 MiB import limit.');
      const text = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(await file.arrayBuffer());
      if (ticket === generation.current) await check(text, ticket);
    } catch (error) {
      if (ticket === generation.current) setState({ text: '', phase: 'invalid', error: error instanceof Error ? error.message : String(error) });
    }
  }
  const busy = state.phase === 'reading' || state.phase === 'checking';
  return <div className="app-shell packet-shell"><a className="skip-link" href="#raw-source">Skip to raw source data</a>
    <header className="topbar"><a href="/" className="brand">Definograph</a><nav className="top-actions"><a className="quiet-button" href="/">Lean statement reader</a><a className="quiet-button" href="/packet">Saved packet</a></nav></header>
    <main className="workspace atlas-workspace packet-workspace"><header className="packet-heading"><h1>Inspect retained source data</h1><p>Open a raw source frame to inspect its original declarations, expression, type and metadata as ordered constructor data.</p></header>
      <details className="packet-import" open={state.phase !== 'ready'}><summary>Local source frame</summary><p>Choose UTF-8 JSON or paste the original text. The file stays local. Import checks the declared raw format and exact readback; it does not run Lean.</p>
        <label className="packet-file">Source frame JSON file<input type="file" accept=".json,application/json" onChange={event => { const file = event.currentTarget.files?.[0]; event.currentTarget.value = ''; if (file) void readFile(file); }}/></label>
        <form onSubmit={event => { event.preventDefault(); void check(state.text, ++generation.current); }}>
          <label htmlFor="raw-source-text">Original source frame text</label><textarea id="raw-source-text" spellCheck={false} value={state.text} onChange={event => { generation.current++; setState({ text: event.target.value, phase: 'editing' }); }}/>
          <button type="submit" className="toolbar-button" disabled={!state.text.trim() || busy}>Inspect source frame</button></form>
        <p className="packet-caption">Editing the source clears its displayed reading. Unsupported input remains here for inspection.</p></details>
      <div className="packet-import-status" aria-live="polite">{busy ? state.phase === 'reading' ? 'Reading the local file…' : 'Checking exact constructor readback…' : state.phase === 'editing' ? 'Source changed. Import it to display its data.' : null}</div>
      {state.error && <p className="packet-boundary" role="alert">Source frame could not be imported: {state.error}</p>}
      <div id="raw-source">{state.source ? <><div className="packet-notice" role="note"><strong>Imported raw data · no mathematical validation</strong><p>Retained references, source positions and metadata are shown exactly, including values with no valid semantic interpretation. Import establishes no producer provenance or certificate.</p></div>
        <RawSourceReading key={state.source.identity} drawing={state.source.drawing}/>
        <details className="packet-json"><summary>Source identity and format</summary><p>Canonical data identity: <code>{state.source.identity}</code></p><p>Format: <code>definograph.raw-frame.v1</code> · exact natural profile 2.</p></details></> : !busy && <p className="packet-empty">No raw source frame is displayed.</p>}</div>
    </main>
  </div>;
}
