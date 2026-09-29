import { Component, useEffect, useMemo, useReducer, useRef, useState, type ReactNode } from 'react';
import { compileReading } from '../reading/compiler';
import { StatementReadingView } from '../visual/StatementReadingView';
import { capturedPacketExpression, compilePacketRecord, type PacketRecordReading, type PacketSource } from './semantic';
import { parsePacket, type ImportedPacket, type JsonObject, type JsonValue, type RecordRole, type SelectedUse } from './packet';
import { boundedNatural, naturalText, type NaturalProfile } from './natural';
import { formatExpr, levelText, nameText, PacketSyntax, PacketSyntaxError } from './syntax';
import { buildStructuralDrawing, readStructuralDrawing, type StructuralDrawing } from './structure';
import { StructuralReading } from './StructuralReading';
import { buildRawInspection, readRawInspection } from './raw';
import { RawSourceReading } from './RawSourceReading';
import './packet-reader.css';
import { counted } from '../core/counted';

const MAX_FILE_BYTES = 16 * 1024 * 1024;
const roles: Record<RecordRole, string> = { retained: 'Retained premises', derived: 'Derived consequence' };
function json(value: unknown): string { return JSON.stringify(value, null, 2); }
function object(value: JsonValue | undefined): JsonObject {
  if (value === null || typeof value !== 'object' || Array.isArray(value)) throw new PacketSyntaxError('Expected a stored object.');
  return value;
}
function array(value: JsonValue | undefined): JsonValue[] {
  if (!Array.isArray(value)) throw new PacketSyntaxError('Expected a stored array.');
  return value;
}
function natural(value: JsonValue | undefined): number {
  if (typeof value !== 'number' || !Number.isSafeInteger(value) || value < 0) throw new PacketSyntaxError('Expected a safe natural number.');
  return value;
}
function message(error: unknown): string { return error instanceof Error ? error.message : String(error); }
function readable(value: JsonValue, render: (value: JsonValue) => string): string {
  try { return render(value); } catch (error) { return `Readable form unavailable: ${message(error)}`; }
}

/** Every edit or import invalidates the previous display. Completion is accepted
 * only for the same generation, including asynchronous file reads. */
export interface PacketImportState {
  generation: number;
  sourceText: string;
  phase: 'empty' | 'editing' | 'reading' | 'checking' | 'ready' | 'invalid';
  packet?: ImportedPacket;
  error?: string;
}
export type PacketImportAction =
  | { type: 'source'; generation: number; sourceText: string; phase: 'editing' | 'reading' | 'checking' }
  | { type: 'accepted'; generation: number; packet: ImportedPacket }
  | { type: 'failed'; generation: number; error: string };
export function packetImportReducer(state: PacketImportState, action: PacketImportAction): PacketImportState {
  if (action.type === 'source') return action.generation < state.generation ? state
    : { generation: action.generation, sourceText: action.sourceText, phase: action.phase };
  if (action.generation !== state.generation) return state;
  if (action.type === 'accepted') return action.packet.sourceText === state.sourceText
    ? { ...state, phase: 'ready', packet: action.packet, error: undefined } : state;
  return { ...state, phase: 'invalid', packet: undefined, error: action.error };
}

/** Large exact data is mounted only when requested; it is never truncated. */
function JsonDetails({ title, value }: { title: string; value: unknown }) {
  const [open, setOpen] = useState(false);
  return <details className="packet-json" onToggle={event => setOpen(event.currentTarget.open)}><summary>{title}</summary>{open && <pre>{json(value)}</pre>}</details>;
}

function UniverseDetails({ metadata }: { metadata: JsonObject }) {
  if (metadata.tag === 'available') return <p>Certificate universe instance: <code>[{array(metadata.values).map(value => readable(value, levelText)).join(', ')}]</code>{array(metadata.values).length === 0 ? ' — available empty list.' : ' — available.'}</p>;
  if (metadata.tag === 'notApplicable') return <p>Certificate universes: not applicable to this exact route.</p>;
  return <p>Certificate universes unavailable: {typeof metadata.reason === 'string' ? metadata.reason : 'no reason supplied'}.</p>;
}

interface UseScope {
  label: string; type: string; value?: string; nondep?: boolean; info: string; location: string;
}
interface CertificateReading { label: string; arguments: string[] }
export interface SelectedUseReading {
  scope: UseScope[];
  source: string;
  view: string;
  actuals: string[];
  sourceCertificate: CertificateReading;
  viewCertificate: CertificateReading;
}

/** Formatting only: labels never identify binders, records or selected uses. */
export function describeSelectedUse(recordValue: JsonValue, use: SelectedUse, profile: NaturalProfile = 1): SelectedUseReading {
  const record = object(recordValue), entry = use.entry, selected = object(entry.use);
  const scopeEntries = array(entry.scope), path = array(entry.path), ownerArity = natural(record.n);
  if (natural(entry.e) !== scopeEntries.length) throw new PacketSyntaxError('The local scope length differs from its recorded depth.');
  let owner = record.owner;
  if (owner === undefined) throw new PacketSyntaxError('The record owner is unavailable.');
  scopeEntries.forEach((raw, depth) => {
    const binding = array(raw);
    if (binding[1] !== depth) throw new PacketSyntaxError('Local binder depths do not follow this selected path.');
    if (binding[0] === 'pi' && binding.length === 4) owner = ['port', owner!, binding[2], binding[3]];
    else if (binding[0] === 'letE' && binding.length === 6) owner = ['letE', owner!, binding[2], binding[3], binding[4], binding[5]];
    else throw new PacketSyntaxError('Unsupported local binder constructor.');
  });
  const localPaths = path.flatMap((step, index) => step === 'piBody' || step === 'letBody' ? [path.slice(0, index + 1)] : []);
  if (localPaths.length !== scopeEntries.length) throw new PacketSyntaxError('The binder scope does not match its template path.');
  const syntax = new PacketSyntax(record.table, profile), bindings = syntax.owner(owner);
  if (bindings.length !== ownerArity + scopeEntries.length) throw new PacketSyntaxError('Owner and local scope arities differ.');
  const env: string[] = [], scope: UseScope[] = [];
  bindings.forEach((binding, index) => {
    const base = nameText(binding.name); let label = base;
    for (let suffix = 2; env.includes(label); suffix++) label = `${base}@${suffix}`;
    scope.push({ label, type: formatExpr(binding.type, env, profile), info: binding.info,
      value: binding.value === undefined ? undefined : formatExpr(binding.value, env, profile), nondep: binding.nondep,
      location: index < ownerArity ? `owner declaration ${index}` : `body / ${localPaths[index - ownerArity].join(' / ')}` });
    env.unshift(label);
  });
  const formatOccurrence = (value: JsonValue): string => formatExpr(syntax.occ(value, env.length), env, profile);
  const args = (value: JsonValue): string[] => syntax.args(value, env.length).map(expr => formatExpr(expr, env, profile));
  const certificate = (value: JsonValue): CertificateReading => {
    const fields = array(value);
    if (fields[0] === 'exact' && fields.length === 1) return { label: 'Exact route tag; no named certificate supplied.', arguments: [] };
    if (fields[0] !== 'classB' || fields.length !== 4) throw new PacketSyntaxError('Unsupported certificate constructor.');
    const arguments_ = args(fields[3]);
    if (arguments_.length !== natural(fields[2])) throw new PacketSyntaxError('Certificate argument count differs from its declared arity.');
    return { label: nameText(fields[1]), arguments: arguments_ };
  };
  return { scope, source: formatOccurrence(selected.src), view: formatOccurrence(selected.view), actuals: args(selected.acts),
    sourceCertificate: certificate(selected.srcCert), viewCertificate: certificate(selected.viewCert) };
}

function Certificate({ value, metadata }: { value: CertificateReading; metadata: JsonObject }) {
  return <div className="packet-certificate"><p>Certificate: <code>{value.label}</code></p><UniverseDetails metadata={metadata}/>
    <p>Explicit certificate arguments in application order:</p>{value.arguments.length ? <ol start={0}>{value.arguments.map((arg, index) => <li key={index}><code>{arg}</code></li>)}</ol> : <p>No explicit certificate arguments.</p>}</div>;
}

export function SelectedUseDetails({ packet, index, readingModel, onApplicationSelect }: { packet: ImportedPacket; index: number; readingModel?: PacketRecordReading; onApplicationSelect?: (application: SelectedUseApplication) => void }) {
  const use = packet.payload.uses[index], operation = packet.payload.results.findIndex(item => item.id === use.pair), result = packet.payload.results[operation];
  const record = result.records[use.role];
  const model = useMemo(() => { try { return { value: describeSelectedUse(record, use, packet.payload.schema) }; } catch (error) { return { error: message(error) }; } }, [record, use, packet.payload.schema]);
  const compiled = useMemo(() => readingModel ?? compilePacketRecord(packet, operation, use.role), [readingModel, packet, operation, use.role]);
  const call = useMemo(() => {
    const sourceId = selectedUseSource(compiled, use);
    try { return { value: selectedUseApplication(compiled, sourceId), hasSource: sourceId !== undefined }; }
    catch (error) { return { error: message(error), hasSource: sourceId !== undefined }; }
  }, [compiled, use]);
  const qualified = (packet.value.bindings.uses as JsonObject[])[index];
  return <section className="packet-use" aria-label="Selected use details">
    <h3>{use.pair} · {roles[use.role]} · local use {readable(use.oid, naturalText)}</h3>
    <p>Template path: <code>{Array.isArray(use.path) ? use.path.join(' / ') || '(root)' : JSON.stringify(use.path)}</code></p>
    <p className="packet-caption">Identity includes this packet, attempt, operation, record role, exact record, local use ID and path. Display labels do not identify a use.</p>
    {model.value ? <><div className="packet-route-grid">
      <section aria-label="Original source route"><h4>Original source route</h4><code className="packet-formula">{model.value.source}</code><Certificate value={model.value.sourceCertificate} metadata={use.sourceLevels}/></section>
      <section aria-label="Chosen view route"><h4>Chosen view route</h4><code className="packet-formula">{model.value.view}</code><Certificate value={model.value.viewCertificate} metadata={use.viewLevels}/></section>
    </div><h4>Owner-context arguments</h4><p className="packet-caption">These arguments instantiate the record’s owner context. Owner slot 0 is the most recent owner declaration; application arguments are listed separately below.</p>
      {model.value.actuals.length ? <ol start={0}>{model.value.actuals.map((actual, slot) => <li key={slot}><code>{actual}</code></li>)}</ol> : <p>The owner-context argument vector is empty.</p>}
      <details><summary>Owner and local binder scope</summary><ol start={0}>{model.value.scope.map((binding, slot) => <li key={slot}><code>{binding.label} : {binding.type}{binding.value === undefined ? '' : ` := ${binding.value}`}</code><p>{binding.value === undefined ? `Binder annotation: ${binding.info}.` : `Local definition; nondep=${binding.nondep}.`} <code>{binding.location}</code></p></li>)}</ol></details>
    </> : <p className="packet-boundary">Readable use unavailable: {model.error}. Exact stored use remains available.</p>}
    <section className="packet-use-call" aria-label="Application at this selected use">
      <h4>Application at this occurrence</h4>
      {call.value ? <><code className="packet-formula">{call.value.text}</code><p className="packet-caption">The full enclosing application of this selected head, with its arguments in source application order.</p><ol>{call.value.arguments.map((argument, position) => <li key={position}><code>{argument.text}</code></li>)}</ol>
        {onApplicationSelect && call.value.relationId && <button type="button" className="toolbar-button" onClick={() => onApplicationSelect(call.value!)}>Show this application in the reader</button>}
        <JsonDetails title="Exact application, ordered arguments and selected head path" value={{ application: call.value.syntax, applicationPath: call.value.path, arguments: call.value.arguments.map(({ syntax, path }) => ({ syntax, path })), selectedHeadPath: compiled.sourceById[call.value.headSourceId].path }}/>
      </> : <p>{call.error ? `Application reading unavailable: ${call.error}.` : call.hasSource ? 'This selected occurrence is not the head of an enclosing application.' : 'No exact application association is available for this selected use.'}</p>}
    </section>
    <JsonDetails title="Exact qualified use, record binding and universe metadata" value={{ packetIdentity: packet.identity, binding: qualified, use }}/>
  </section>;
}

/** A selected template path starts after the record's identified supplier let.
 * Association uses constructor positions only, never matching displayed names. */
export function selectedUseSource(model: PacketRecordReading, use: SelectedUse): string | undefined {
  const supplier = model.supplierObjectId ? model.sourceById[model.supplierObjectId] : undefined;
  if (!supplier || !Array.isArray(use.path)) return;
  const positions: Record<string, number> = { fn: 1, arg: 2, piBody: 3, lamBody: 3, letBody: 4 };
  const path = [...supplier.path, 4];
  for (const step of use.path) {
    if (typeof step !== 'string' || !Object.hasOwn(positions, step)) return;
    path.push(positions[step]);
  }
  return Object.keys(model.sourceById).find(id => {
    const candidate = model.sourceById[id].path;
    return candidate.length === path.length && candidate.every((part, index) => part === path[index]);
  });
}

export function selectedUseObject(model: PacketRecordReading, sourceId: string | undefined): string | undefined {
  const source = sourceId ? model.sourceById[sourceId] : undefined;
  if (!source) return;
  // A binder's object is attached to its introduction, while the selected use
  // retains its own occurrence path. Resolve de Bruijn scope rather than labels.
  if (Array.isArray(source.syntax) && source.syntax.length === 2 && source.syntax[0] === 'bvar') {
    let index: number;
    try { index = boundedNatural(source.syntax[1], model.profile ?? 1, source.scopeBinderIds.length); } catch { return; }
    const binderId = source.scopeBinderIds[source.scopeBinderIds.length - 1 - index];
    return model.document?.objects.find(item => item.binder?.id === binderId)?.id;
  }
  return model.document?.objects.find(item => {
    const candidate = model.sourceById[item.id];
    return candidate && candidate.path.length === source.path.length && candidate.path.every((part, index) => part === source.path[index]);
  })?.id;
}

export interface SelectedUseApplication {
  headSourceId: string;
  sourceId: string;
  syntax: JsonValue;
  path: (string | number)[];
  text: string;
  arguments: { syntax: JsonValue; path: (string | number)[]; text: string }[];
  relationId?: string;
  nodeId?: string;
}

/** Follow function children only. An application containing the selected use as
 * an argument belongs to another head and must never be selected as this call. */
export function selectedUseApplication(model: PacketRecordReading, sourceId: string | undefined): SelectedUseApplication | undefined {
  const head = sourceId ? model.sourceById[sourceId] : undefined;
  if (!head || !sourceId) return;
  const isApp = (value: JsonValue): value is JsonValue[] => Array.isArray(value) && value.length === 3 && value[0] === 'app';
  const samePath = (left: readonly (string | number)[], right: readonly (string | number)[]) => left.length === right.length && left.every((part, index) => part === right[index]);
  let largest: [string, PacketSource] | undefined;
  for (const entry of Object.entries(model.sourceById)) {
    const candidate = entry[1];
    if (!isApp(candidate.syntax) || candidate.path.length > head.path.length ||
      !candidate.path.every((part, index) => part === head.path[index]) ||
      !head.path.slice(candidate.path.length).every(part => part === 1) ||
      !samePath(candidate.scopeBinderIds, head.scopeBinderIds)) continue;
    let current = candidate.syntax as JsonValue;
    for (let depth = candidate.path.length; depth < head.path.length; depth++) {
      if (!isApp(current)) { current = null; break; }
      current = current[1];
    }
    if (JSON.stringify(current) !== JSON.stringify(head.syntax)) continue;
    if (!largest || candidate.path.length < largest[1].path.length) largest = entry;
  }
  if (!largest) return;
  const [applicationId, application] = largest;
  const binderNames = new Map(model.document?.objects.flatMap(item => item.binder ? [[item.binder.id, item.binder.name] as const] : []) ?? []);
  const env = application.scopeBinderIds.map(id => binderNames.get(id) ?? id).reverse();
  const arguments_: SelectedUseApplication['arguments'] = [];
  let current = application.syntax, path = [...application.path];
  while (isApp(current)) {
    arguments_.unshift({ syntax: current[2], path: [...path, 2], text: formatExpr(current[2], env, model.profile ?? 1) });
    current = current[1]; path = [...path, 1];
  }
  const relation = model.document?.relations.find(item => item.kind === 'application' &&
    model.sourceById[item.id] && samePath(model.sourceById[item.id].path, application.path));
  return { headSourceId: sourceId, sourceId: applicationId, syntax: application.syntax, path: application.path,
    text: formatExpr(application.syntax, env, model.profile ?? 1), arguments: arguments_, relationId: relation?.id, nodeId: relation?.nodeId };
}

function Audit({ audit }: { audit: JsonObject }) {
  const result = object(audit.result), available = result.tag === 'available';
  return <div className="packet-audit"><p>{String(audit.category)} · environment {String(audit.environment)}</p>
    {audit.association !== undefined && <p>Recorded source association: <code>{JSON.stringify(audit.association)}</code></p>}
    {available ? array(result.axioms).length ? <><p>Available audit; reported axiom dependencies:</p><ul>{array(result.axioms).map((name, index) => <li key={index}><code>{readable(name, nameText)}</code></li>)}</ul></> : <p>Available audit: no axiom dependencies reported ([]).</p> : <p>Audit unavailable: {String(result.reason)}. This is not an empty dependency list.</p>}
    <JsonDetails title="Exact audit" value={audit}/></div>;
}

interface StructuralSelection { source: PacketSource; scopeNames: Map<string, string> }
function SourceInspector({ model, selectedId, onSelect, structuralSelection }: { model: PacketRecordReading; selectedId: string; onSelect: (id: string) => void; structuralSelection?: StructuralSelection }) {
  const [limit, setLimit] = useState(100);
  const [boundaryLimit, setBoundaryLimit] = useState(30);
  const selected: PacketSource | undefined = structuralSelection?.source ?? model.sourceById[selectedId];
  const names = new Map([...(model.document?.objects.flatMap(item => item.binder ? [[item.binder.id, item.binder.name] as const] : []) ?? []), ...(structuralSelection?.scopeNames ?? [])]);
  let text: string | undefined;
  if (selected) {
    try { text = formatExpr(selected.syntax, selected.scopeBinderIds.map(id => names.get(id) ?? id).reverse(), model.profile ?? 1); }
    catch (error) { text = `Readable constructor form unavailable: ${message(error)}. The full exact value is below.`; }
  }
  const objects = model.document?.objects ?? [];
  const boundaries = model.document?.opaqueRegions ?? [];
  return <section className="packet-inspector" aria-label="Exact source inspector"><h3>Inspect the source</h3>
    <p className="packet-caption">Select an object or a statement in the reader. Every displayed application retains its complete argument list here, including inputs beyond a diagram’s display limit.</p>
    {selected ? <div className="packet-selected-source" data-source-path={JSON.stringify(selected.path)}><h4>Selected constructor</h4><code className="packet-formula">{text}</code><p>Constructor path: <code>{JSON.stringify(selected.path)}</code></p><p>Lexical binder scope, oldest first:</p>{selected.scopeBinderIds.length ? <ol>{selected.scopeBinderIds.map(id => <li key={id}><code>{names.get(id) ?? 'binder'} — {id}</code></li>)}</ol> : <p>Closed scope.</p>}<JsonDetails title="Full exact constructor value" value={selected.syntax}/></div> : <p>No source selected.</p>}
    <details><summary>All objects and application arguments ({objects.length})</summary><div className="packet-object-list">{objects.slice(0, limit).map(item => <button type="button" key={item.id} onClick={() => onSelect(item.id)} aria-pressed={selectedId === item.id}>{item.label}{item.type && <small>{item.type}</small>}</button>)}</div>{objects.length > limit && <button type="button" className="toolbar-button" onClick={() => setLimit(count => count + 100)}>Show next {counted(Math.min(100, objects.length - limit), 'object')}</button>}</details>
    {boundaries.length > 0 && <details><summary>Expressions without a supported diagram ({boundaries.length})</summary><ul>{boundaries.slice(0, boundaryLimit).map(boundary => <li key={boundary.id}><p>{boundary.reason}</p><button type="button" className="quiet-button" onClick={() => onSelect(boundary.id)}>Inspect exact expression: {boundary.label}</button></li>)}</ul>{boundaries.length > boundaryLimit && <button type="button" className="toolbar-button" onClick={() => setBoundaryLimit(count => count + 30)}>Show next {counted(Math.min(30, boundaries.length - boundaryLimit), 'boundary', 'boundaries')}</button>}</details>}
    {!!model.document?.diagnostics.length && <details><summary>Scope and display notes</summary><ul>{model.document.diagnostics.map((note, index) => <li key={index}>{note}</li>)}</ul></details>}
    <JsonDetails title="Exact stored record and complete argument references" value={model.record}/>
  </section>;
}

/** Reuses the existing guided reader. The captured outcomes remain reported data. */
export function PacketReading({ packet, initialOperationIndex = 0, initialRole = 'retained', initialView = 'guided' }: { packet: ImportedPacket; initialOperationIndex?: number; initialRole?: RecordRole; initialView?: 'guided' | 'structure' | 'raw' }) {
  const [operation, setOperation] = useState(initialOperationIndex), [role, setRole] = useState<RecordRole>(initialRole);
  const [selectedNode, setSelectedNode] = useState(''), [selectedObject, setSelectedObject] = useState(''), [selectedSource, setSelectedSource] = useState('');
  const [selectedRelation, setSelectedRelation] = useState('');
  const [view, setView] = useState<'guided' | 'structure' | 'raw'>(initialView);
  const [structuralSelection, setStructuralSelection] = useState<StructuralSelection>();
  const [useIndex, setUseIndex] = useState<number | null>(null);
  const statement = useRef<HTMLElement>(null);
  const result = packet.payload.results[operation];
  const model = useMemo(() => compilePacketRecord(packet, operation, role), [packet, operation, role]);
  const sourceCapture = useMemo(() => capturedPacketExpression(packet, operation, role, model.source.checkId), [packet, operation, role, model.source.checkId]);
  const structure = useMemo(() => {
    if (!sourceCapture) return undefined;
    const built = buildStructuralDrawing(sourceCapture.syntax, {
      sourceIdentity: `packet:${packet.identity}:check:${sourceCapture.checkId}`,
      sourcePath: sourceCapture.path, profile: packet.payload.schema,
    });
    if (!built.ok) return built;
    const readback = readStructuralDrawing(built.value);
    if (!readback.ok) return readback;
    if (JSON.stringify(readback.value.expression) !== JSON.stringify(sourceCapture.syntax))
      return { ok: false as const, error: { message: 'The drawing does not reconstruct its exact input.' } };
    return built;
  }, [packet.identity, sourceCapture]);
  const raw = useMemo(() => {
    if (!sourceCapture || packet.payload.schema !== 2) return undefined;
    const built = buildRawInspection({ family: 'expression', value: sourceCapture.syntax }, { sourceIdentity: `packet:${packet.identity}:check:${sourceCapture.checkId}`, sourcePath: sourceCapture.path });
    if (!built.ok) return built;
    const readback = readRawInspection(built.value);
    if (!readback.ok) return readback;
    if (JSON.stringify(readback.value.value) !== JSON.stringify(sourceCapture.syntax))
      return { ok: false as const, error: { message: 'The raw drawing does not reconstruct its exact input.' } };
    return built;
  }, [packet.identity, sourceCapture]);
  const reading = useMemo(() => model.document ? compileReading(model.document, { selectedNodeId: selectedNode || undefined }) : undefined, [model, selectedNode]);
  const showStructure = view === 'structure' || (view === 'guided' && !model.document);
  function resetSelection() { setSelectedNode(''); setSelectedObject(''); setSelectedSource(''); setSelectedRelation(''); setUseIndex(null); setStructuralSelection(undefined); }
  function selectStructuralSource(path: (string | number)[], drawing: StructuralDrawing) {
    const node = drawing.nodes.find(item => item.sourcePath.length === path.length && item.sourcePath.every((part, index) => part === path[index]));
    if (!node) return;
    const scopes: string[] = [], scopeNames = new Map<string, string>();
    const homes = new Map(drawing.homes.map(home => [home.id, home]));
    const declarations = new Map(drawing.declarations.map(declaration => [declaration.id, declaration]));
    const nodes = new Map(drawing.nodes.map(item => [item.id, item]));
    let home = homes.get(node.homeId);
    while (home?.declarationId) {
      scopes.unshift(home.declarationId); home = home.parentId ? homes.get(home.parentId) : undefined;
    }
    for (const id of scopes) {
      const declaration = declarations.get(id)!;
      const binder = declaration.kind === 'external' ? undefined : nodes.get(declaration.nodeId);
      const rawName = declaration.kind === 'external' ? declaration.userName : binder && 'name' in binder ? binder.name : ['anonymous'];
      const base = nameText(rawName); let label = base;
      for (let suffix = 2; [...scopeNames.values()].includes(label); suffix++) label = `${base}@${suffix}`;
      scopeNames.set(id, label);
    }
    const syntax = path.reduce<JsonValue>((value, part) => (value as JsonObject)[part], packet.value);
    setStructuralSelection({ source: { syntax, path: [...path], scopeBinderIds: scopes }, scopeNames });
  }
  function showApplication(application: SelectedUseApplication) {
    setView('guided'); setStructuralSelection(undefined);
    setSelectedSource(application.headSourceId);
    setSelectedObject(selectedUseObject(model, application.headSourceId) ?? '');
    setSelectedNode(application.nodeId ?? '');
    setSelectedRelation(application.relationId ?? '');
  }
  function selectUse(index: number) {
    const use = packet.payload.uses[index];
    setOperation(packet.payload.results.findIndex(item => item.id === use.pair)); setRole(use.role);
    resetSelection(); setUseIndex(index); setView('guided');
  }
  const relevantUses = packet.payload.uses.flatMap((use, index) => use.pair === result.id && use.role === role ? [{ use, index }] : []);
  const displayedUse = useIndex !== null && relevantUses.some(item => item.index === useIndex) ? useIndex : relevantUses[0]?.index;
  useEffect(() => {
    if (useIndex === null) return;
    const sourceId = selectedUseSource(model, packet.payload.uses[useIndex]);
    setSelectedSource(sourceId ?? '');
    setSelectedObject(selectedUseObject(model, sourceId) ?? '');
    const application = selectedUseApplication(model, sourceId);
    setSelectedNode(application?.nodeId ?? '');
    setSelectedRelation(application?.relationId ?? '');
  }, [model, packet, useIndex]);
  return <div className="packet-reading" data-packet-identity={packet.identity}>
    <div className="packet-notice" role="note"><strong>Unverified imported packet</strong><p>Its hashes and attachment bindings are consistent. Producer provenance is unverified. Reported checks are not current certification; no joint certification is established.</p></div>
    <div className="packet-pickers"><label>Operation<select value={operation} onChange={event => { setOperation(Number(event.target.value)); resetSelection(); }}>{packet.payload.results.map((item, index) => <option key={index} value={index}>{item.id}</option>)}</select></label>
      <label>Record<select value={role} onChange={event => { setRole(event.target.value as RecordRole); resetSelection(); }}><option value="retained">Retained premises</option><option value="derived">Derived consequence</option></select></label></div>
    <section className="packet-reported-status" aria-label="Reported operation status"><h2>{result.id}</h2><dl><div><dt>Reported formation</dt><dd>{result.report.formation.tag}</dd></div><div><dt>Reported evidence</dt><dd>{result.report.evidence.tag}</dd></div><div><dt>Candidate</dt><dd>{result.candidate === null ? 'Unavailable — none constructed' : 'Present'}</dd></div></dl>
      {result.report.evidence.tag === 'missing' && <p>Missing evidence does not mean the law is false.</p>}
      {(result.report.formation.tag === 'unknown' || result.report.evidence.tag === 'unknown') && <p>The reported check is unknown. Stored candidate and statement syntax remain inspectable.</p>}
      <JsonDetails title="Full reported outcomes and reasons" value={result.report}/></section>
    <section ref={statement} className="packet-statement" aria-label={roles[role]}><h2>{roles[role]}</h2><p>{role === 'retained' ? 'The input laws remain separate premises of the construction.' : 'The derived consequence is shown separately from the retained premises.'}</p>
      <p className="packet-caption">Display source: {model.source.association === 'reading' ? 'captured reading declaration' : model.source.association === 'source' ? 'captured original source statement' : 'no supported declaration association'}{model.source.checkId !== undefined && ` · check ${model.source.checkId} · reported ${model.source.outcome}`}. The diagram presents imported syntax.</p>
      {model.reason && <p className="packet-boundary">{model.reason}</p>}
      {!!model.document?.opaqueRegions.length && <p className="packet-boundary">{model.document.opaqueRegions.length} expression{model.document.opaqueRegions.length === 1 ? ' has' : 's have'} no specialized guided diagram. Open “Source structure” for their constructor roles and scopes, or inspect their exact source below.</p>}
      {sourceCapture && <div className="packet-view-picker" role="group" aria-label="Reading view"><button type="button" className="toolbar-button" aria-pressed={view === 'guided' && !showStructure} onClick={() => setView('guided')} disabled={!model.document}>Guided reading</button><button type="button" className="toolbar-button" aria-pressed={showStructure} onClick={() => setView('structure')}>Source structure</button>{packet.payload.schema === 2 && <button type="button" className="toolbar-button" aria-pressed={view === 'raw'} onClick={() => setView('raw')}>Raw source data</button>}</div>}
      {showStructure && sourceCapture && <><p className="packet-caption">Source structure uses the captured {sourceCapture.association === 'reading' ? 'reading' : 'original source'} expression · check {sourceCapture.checkId} · reported {sourceCapture.outcome}. Exact reassembly checks structure only.</p>
        {structure?.ok ? <StructuralReading key={`${packet.identity}:${sourceCapture.checkId}`} drawing={structure.value} selectedPath={structuralSelection?.source.path}
          onSourceSelect={path => selectStructuralSource(path, structure.value)}/> : <p className="packet-boundary">Source structure unavailable: {structure?.error.message ?? 'No exact drawing was produced'}. The complete captured input remains available below.</p>}
        <JsonDetails title="Complete captured expression for this structure" value={sourceCapture.syntax}/></>}
      {view === 'raw' && sourceCapture && <><p className="packet-caption">This view inspects the captured expression only. Reported operation and check outcomes remain unchanged.</p>{raw?.ok ? <RawSourceReading drawing={raw.value}/> : <p className="packet-boundary">Raw source data unavailable: {raw?.error.message ?? 'This source has no declared raw-compatible encoding.'}</p>}<JsonDetails title="Complete captured expression for raw inspection" value={sourceCapture.syntax}/></>}
      {view === 'guided' && model.document && reading && <StatementReadingView key={`${packet.identity}:${operation}:${role}`} document={model.document} reading={reading} selectedObjectId={selectedObject || undefined} selectedRelationId={selectedRelation || undefined}
        onObjectSelect={id => { setSelectedObject(id); setSelectedSource(id); }} onNodeSelect={id => { setSelectedRelation(''); setSelectedNode(id); setSelectedSource(id); }}/>}</section>
    <div className="packet-secondary"><SourceInspector key={`${operation}:${role}`} model={model} selectedId={selectedSource} structuralSelection={showStructure ? structuralSelection : undefined} onSelect={id => { setStructuralSelection(undefined); setSelectedObject(id); setSelectedSource(id); }}/>
      <section aria-label="Qualified selected uses"><h3>Selected uses</h3><p className="packet-caption">Navigate by operation and record role; local use numbers can repeat.</p>
        {packet.payload.uses.length ? <label>Qualified selected use<select value={displayedUse ?? ''} onChange={event => selectUse(Number(event.target.value))}><option value="" disabled>No use in this record</option>{packet.payload.uses.map((use, index) => <option value={index} key={index}>{use.pair} / {roles[use.role]} / local {readable(use.oid, naturalText)} / use {index + 1}</option>)}</select></label> : <p>No qualified selected uses were recorded.</p>}
        {displayedUse === undefined ? <p>No selected use is available for this operation and record role.</p> : <SelectedUseDetails key={displayedUse} packet={packet} index={displayedUse} readingModel={model} onApplicationSelect={application => { showApplication(application); statement.current?.scrollIntoView({ block: 'start' }); }}/>}</section>
      <details className="packet-coherence"><summary>Reported coordination between the operations</summary><p>Exact-reference coherence: <strong>{String(packet.payload.coherence.value)}</strong>.</p><p>{packet.payload.coherence.value ? 'The packet reports coherence of its exact input references. This does not jointly certify the operations.' : 'The packet reports that exact-reference coherence failed. This does not establish mathematical inequality.'}</p><p>Separate local structural admissions: <code>{JSON.stringify(packet.payload.coherence.admissions)}</code>.</p><JsonDetails title="Exact coordination and separate bank evidence" value={{ coherence: packet.payload.coherence, bankExactEvidence: packet.payload.bank.exactEvidence, joint: packet.payload.joint }}/></details>
      <details className="packet-checks"><summary>Reported checks and dependency audits ({counted(model.checks.length, 'check')})</summary><p>Outcomes below are imported reports about specific declarations and environments.</p>{model.checks.map(check => {
        const audits = packet.payload.audits.filter(audit => audit.checkId === check.id);
        return <details key={check.id}><summary>Check {check.id} · {check.label} · {check.outcome.tag}</summary><p>Environment {check.envBefore} → {check.envAfter}; recorded heartbeat bound {check.heartbeatBound === undefined ? 'unavailable' : readable(check.heartbeatBound, naturalText)}.</p><JsonDetails title="Exact check subject, declaration and outcome" value={check}/>{audits.length ? audits.map((audit, index) => <Audit key={index} audit={audit}/>) : <p>No audit was recorded for this check. A missing audit is not an empty axiom list.</p>}</details>;
      })}</details>
      <details><summary>Source audits across the packet</summary>{packet.payload.audits.some(audit => audit.checkId == null) ? packet.payload.audits.filter(audit => audit.checkId == null).map((audit, index) => <Audit key={index} audit={audit}/>) : <p>No source audit was recorded.</p>}</details>
      <JsonDetails title="Exact attempted inputs, candidate and context" value={{ inputs: packet.payload.inputs[operation], candidate: result.candidate, context: packet.payload.context }}/>
      <JsonDetails title="Packet identity, request and checking basis" value={{ identity: packet.identity, request: packet.value.request, basis: packet.value.basis }}/>
    </div>
  </div>;
}

class PacketDisplayBoundary extends Component<{ children: ReactNode }, { error?: string }> {
  state: { error?: string } = {};
  static getDerivedStateFromError(error: unknown) { return { error: message(error) }; }
  render() {
    return this.state.error ? <p className="packet-boundary" role="alert">This unverified imported packet could not be displayed: {this.state.error}. Its original text remains in Local packet source.</p> : this.props.children;
  }
}

export default function PacketReader() {
  const [state, dispatch] = useReducer(packetImportReducer, { generation: 0, sourceText: '', phase: 'empty' });
  const generation = useRef(0);
  useEffect(() => () => { generation.current++; }, []);
  async function check(sourceText: string, ticket: number) {
    dispatch({ type: 'source', generation: ticket, sourceText, phase: 'checking' });
    try { const packet = await parsePacket(sourceText); if (ticket === generation.current) dispatch({ type: 'accepted', generation: ticket, packet }); }
    catch (error) { if (ticket === generation.current) dispatch({ type: 'failed', generation: ticket, error: message(error) }); }
  }
  async function readFile(file: File) {
    const ticket = ++generation.current;
    dispatch({ type: 'source', generation: ticket, sourceText: '', phase: 'reading' });
    try {
      if (file.size > MAX_FILE_BYTES) throw new Error('The file exceeds the 16 MiB import limit. The original file remains on your device.');
      // Preserve any BOM in the original text so the exact JSON decoder, rather
      // than the file loader, decides whether those bytes are acceptable.
      const sourceText = new TextDecoder('utf-8', { fatal: true, ignoreBOM: true }).decode(await file.arrayBuffer());
      if (ticket === generation.current) await check(sourceText, ticket);
    } catch (error) { if (ticket === generation.current) dispatch({ type: 'failed', generation: ticket, error: message(error) }); }
  }
  const busy = state.phase === 'reading' || state.phase === 'checking';
  return <div className="app-shell packet-shell"><a className="skip-link" href="#packet-statement">Skip to the packet reading</a>
    <header className="topbar"><a href="/" className="brand">Definograph</a><nav className="top-actions"><a className="quiet-button" href="/">Lean statement reader</a><a className="quiet-button" href="/source-data">Source data</a></nav></header>
    <main className="workspace atlas-workspace packet-workspace"><header className="packet-heading"><h1>Read a saved composition</h1><p>Open an exact packet locally and follow its retained premises and derived consequence through the existing visual reader.</p></header>
      <details className="packet-import" open={state.phase !== 'ready'}><summary>Local packet source</summary><p>Choose UTF-8 JSON or paste the original text. Import checks structural consistency; it does not run Lean or contact a service.</p>
        <label className="packet-file">JSON file<input type="file" accept=".json,application/json" onChange={event => { const file = event.currentTarget.files?.[0]; event.currentTarget.value = ''; if (file) void readFile(file); }}/></label>
        <form onSubmit={event => { event.preventDefault(); void check(state.sourceText, ++generation.current); }}><label htmlFor="packet-source">Original packet text</label><textarea id="packet-source" spellCheck={false} value={state.sourceText} onChange={event => dispatch({ type: 'source', generation: ++generation.current, sourceText: event.target.value, phase: 'editing' })}/>
          <button type="submit" className="toolbar-button" disabled={!state.sourceText.trim() || busy}>Import packet</button></form>
        <p className="packet-caption">Editing the source clears the displayed reading until that source has been imported again. Unsupported or invalid text stays here for inspection.</p></details>
      <div aria-live="polite" className="packet-import-status">{busy ? state.phase === 'reading' ? 'Reading the local file…' : 'Checking packet consistency…' : state.phase === 'editing' ? 'Source changed. Import it to display a reading.' : null}</div>
      {state.error && <p role="alert" className="packet-boundary">Packet could not be imported: {state.error}</p>}
      <div id="packet-statement">{state.packet ? <PacketDisplayBoundary key={`${state.generation}:${state.packet.identity}`}><PacketReading packet={state.packet}/></PacketDisplayBoundary> : !busy && <p className="packet-empty">No packet reading is displayed. The Lean statement reader remains available from the link above.</p>}</div>
    </main></div>;
}
