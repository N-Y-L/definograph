import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import PacketReader, { describeSelectedUse, PacketReading, packetImportReducer, selectedUseSource, selectedUseObject, selectedUseApplication, SelectedUseDetails, type PacketImportState } from './PacketReader';
import { parsePacket, type ImportedPacket, type JsonObject, type JsonValue } from './packet';
import { compilePacketRecord, type PacketRecordReading } from './semantic';
import { compileReading } from '../reading/compiler';
import { compileReadingCues } from '../reading/cues';

// The reducer needs only sourceText; this stand-in makes no packet-validation claim.
const packetForState = (sourceText: string): ImportedPacket => ({ sourceText }) as ImportedPacket;
const empty: PacketImportState = { generation: 0, sourceText: '', phase: 'empty' };

describe('local packet import state', () => {
  it('invalidates a successful display immediately when its source changes', () => {
    let state = packetImportReducer(empty, { type: 'source', generation: 1, sourceText: 'first', phase: 'checking' });
    state = packetImportReducer(state, { type: 'accepted', generation: 1, packet: packetForState('first') });
    expect(state.phase).toBe('ready');
    state = packetImportReducer(state, { type: 'source', generation: 2, sourceText: 'changed', phase: 'editing' });
    expect(state).toEqual({ generation: 2, sourceText: 'changed', phase: 'editing' });
    expect(packetImportReducer(state, { type: 'accepted', generation: 1, packet: packetForState('first') })).toBe(state);
  });

  it('keeps the latest success when older file or parser promises finish later', () => {
    let state = packetImportReducer(empty, { type: 'source', generation: 1, sourceText: '', phase: 'reading' });
    state = packetImportReducer(state, { type: 'source', generation: 2, sourceText: 'new packet', phase: 'checking' });
    state = packetImportReducer(state, { type: 'accepted', generation: 2, packet: packetForState('new packet') });
    for (const late of [
      { type: 'source', generation: 1, sourceText: 'old file', phase: 'checking' },
      { type: 'failed', generation: 1, error: 'old failure' },
      { type: 'accepted', generation: 1, packet: packetForState('old file') },
    ] as const) expect(packetImportReducer(state, late)).toBe(state);
    expect(state.packet?.sourceText).toBe('new packet');
    expect(state.error).toBeUndefined();
  });

  it('retains invalid original text and prevents mismatched success from appearing', () => {
    const sourceText = '{"schema":1.0,"unavailable":"original text"}';
    let state = packetImportReducer(empty, { type: 'source', generation: 3, sourceText, phase: 'checking' });
    expect(packetImportReducer(state, { type: 'accepted', generation: 3, packet: packetForState('different') })).toBe(state);
    state = packetImportReducer(state, { type: 'failed', generation: 3, error: 'integer required' });
    expect(state).toEqual({ generation: 3, sourceText, phase: 'invalid', packet: undefined, error: 'integer required' });
    state = packetImportReducer(state, { type: 'source', generation: 4, sourceText: '', phase: 'reading' });
    expect(state.error).toBeUndefined();
    expect(state.packet).toBeUndefined();
  });

  it('offers local file and original text input with a route back to the existing reader', () => {
    const html = renderToStaticMarkup(createElement(PacketReader));
    expect(html).toContain('type="file"');
    expect(html).toContain('id="packet-source"');
    expect(html).toContain('href="/"');
    expect(html).toContain('does not run Lean or contact a service');
    expect(html).not.toContain('data-reading-step');
  });
});

describe('selected head application association', () => {
  const constant = (name: string): JsonValue => ['const', ['str', ['anonymous'], name], []];
  const f = constant('f'), g = constant('g'), x = constant('x'), y = constant('y');
  const withSources = (sourceById: PacketRecordReading['sourceById']): PacketRecordReading => ({
    record: null, source: { label: 'constructed source', association: 'reading' }, checks: [], sourceById,
  });

  it('recovers the complete function spine even without intermediate application source entries', () => {
    const syntax: JsonValue = ['app', ['app', f, x], y];
    const model = withSources({
      application: { syntax, path: ['value'], scopeBinderIds: [] },
      head: { syntax: f, path: ['value', 1, 1], scopeBinderIds: [] },
    });
    const call = selectedUseApplication(model, 'head')!;
    expect(call.text).toBe('(f x y)');
    expect(call.arguments.map(argument => argument.text)).toEqual(['x', 'y']);
    expect(call.arguments.map(argument => argument.path)).toEqual([['value', 1, 2], ['value', 2]]);
    expect(call.path).toEqual(['value']);
    expect(call.headSourceId).toBe('head');
    expect(call.relationId).toBeUndefined();
  });

  it('stops before an argument parent and never treats a selected argument as its caller', () => {
    const inner: JsonValue = ['app', g, x], outer: JsonValue = ['app', f, inner];
    const model = withSources({
      outer: { syntax: outer, path: ['value'], scopeBinderIds: [] },
      inner: { syntax: inner, path: ['value', 2], scopeBinderIds: [] },
      head: { syntax: g, path: ['value', 2, 1], scopeBinderIds: [] },
      argument: { syntax: x, path: ['value', 2, 2], scopeBinderIds: [] },
    });
    expect(selectedUseApplication(model, 'head')).toMatchObject({ sourceId: 'inner', text: '(g x)', path: ['value', 2] });
    expect(selectedUseApplication(model, 'argument')).toBeUndefined();
    expect(selectedUseApplication(model, undefined)).toBeUndefined();
  });

  it('requires matching exact head syntax and lexical scope as well as a path prefix', () => {
    const model = withSources({
      call: { syntax: ['app', f, x], path: ['value'], scopeBinderIds: [] },
      head: { syntax: g, path: ['value', 1], scopeBinderIds: [] },
    });
    expect(selectedUseApplication(model, 'head')).toBeUndefined();
    model.sourceById.head = { syntax: f, path: ['value', 1], scopeBinderIds: ['different-scope'] };
    expect(selectedUseApplication(model, 'head')).toBeUndefined();
  });
});

const root = process.env.DEFINOGRAPH_PACKET_FIXTURES;
describe.skipIf(!root)('packet reader on external checked-composition exports', () => {
  const load = (name: string, controls = false): Promise<ImportedPacket> => parsePacket(readFileSync(join(root!, controls ? 'import-controls' : 'worker-packets', `${name}${controls ? '' : '.packet'}.json`), 'utf8'));

  it.each(['certified-route-universe', 'let-context', 'missing', 'incoherent', 'refused', 'timeout'])('renders %s using the guided reader and distinct reported status', async name => {
    const packet = await load(name);
    const html = renderToStaticMarkup(createElement(PacketReading, { packet }));
    expect(html).toContain('Unverified imported packet');
    expect(html).toContain('no joint certification is established');
    expect(html).toContain('aria-label="Reported operation status"');
    expect(html).toContain('Reported formation');
    expect(html).toContain('Reported evidence');
    expect(html).toContain('Retained premises');
    expect(html).toContain('Derived consequence');
    expect(html).not.toContain('DGRAPH_PACKET=');
    if (name === 'refused') {
      expect(html).toContain('Unavailable — none constructed');
      expect(html).not.toContain('class="statement-reading-view"');
      const other = renderToStaticMarkup(createElement(PacketReading, { packet, initialOperationIndex: 1 }));
      expect(other).toContain('class="statement-reading-view"');
      expect(other).toContain('aria-label="Guided visual sequence"');
    } else {
      expect(html).toContain('class="statement-reading-view"');
      expect(html).toContain('Whole statement');
      expect(html).toContain('Full visual statement');
    }
    if (name === 'missing') expect(html).toContain('Missing evidence does not mean the law is false');
    if (name === 'timeout') expect(html).toContain('The reported check is unknown');
    if (name === 'incoherent') expect(html).toContain('does not establish mathematical inequality');
    if (name === 'let-context') {
      expect(html).toContain('seed');
      expect(html).toContain('Define');
    }
  });

  it('keeps original source, chosen view, explicit certificate arguments and universes separate', async () => {
    const packet = await load('certified-route-universe'), use = packet.payload.uses[0];
    const model = describeSelectedUse(packet.payload.results[0].records.retained, use);
    expect(model.source).toContain('addAlias');
    expect(model.view).toContain('addOp');
    expect(model.source).not.toBe(model.view);
    expect(model.sourceCertificate.label).toContain('genericRefl');
    expect(model.sourceCertificate.arguments).toHaveLength(2);
    expect(model.sourceCertificate.arguments[0]).toContain('Operation');
    expect(model.sourceCertificate.arguments[1]).toContain('addOp');
    expect(model.viewCertificate.arguments).toEqual([]);
    expect(model.scope.map(binding => binding.label)).toEqual(['i', 'x', 'y']);
    const html = renderToStaticMarkup(createElement(SelectedUseDetails, { packet, index: 0 }));
    expect(html).toContain('aria-label="Original source route"');
    expect(html).toContain('aria-label="Chosen view route"');
    expect(html).toContain('succ(0)');
    expect(html).toContain('not applicable to this exact route');
    expect(html).not.toContain('"table"'); // Assertions above inspect readable UI, not hidden raw packet data.
  });

  it('renders the derived consequence through its own captured declaration and supplier', async () => {
    const packet = await load('certified-route-universe');
    const retained = compilePacketRecord(packet, 0, 'retained'), derived = compilePacketRecord(packet, 0, 'derived');
    expect(derived.source.checkId).not.toBe(retained.source.checkId);
    expect(derived.supplierObjectId).toBeDefined();
    expect(derived.supplierObjectId).not.toBe(retained.supplierObjectId);
    const html = renderToStaticMarkup(createElement(PacketReading, { packet, initialRole: 'derived' }));
    expect(html).toContain('aria-label="Derived consequence"');
    expect(html).toContain('aria-label="Guided visual sequence"');
    expect(html).toContain(`check ${derived.source.checkId} · reported accepted`);
    expect(html).toContain('data-reading-node=');
  });

  it('preserves qualified local paths and distinct binder scope under renaming', async () => {
    const packet = await load('renamed-with-repeated-labels', true), result = packet.payload.results[0];
    const uses = packet.payload.uses.filter(use => use.pair === result.id && use.role === 'retained');
    const first = describeSelectedUse(result.records.retained, uses[0]), second = describeSelectedUse(result.records.retained, uses[1]);
    expect(new Set(first.scope.map(binding => binding.label)).size).toBe(first.scope.length);
    expect(first.scope.map(binding => binding.location)).not.toEqual(second.scope.map(binding => binding.location));
    const model = compilePacketRecord(packet, 0, 'retained');
    const sourceA = selectedUseSource(model, uses[0]), sourceB = selectedUseSource(model, uses[1]);
    expect(sourceA).toBeDefined(); expect(sourceB).toBeDefined(); expect(sourceA).not.toBe(sourceB);
    expect(model.sourceById[sourceA!].scopeBinderIds).not.toEqual(model.sourceById[sourceB!].scopeBinderIds);
    expect(selectedUseObject(model, sourceA)).toBe(model.supplierObjectId);
    expect(selectedUseObject(model, sourceB)).toBe(model.supplierObjectId);
  });

  it('links all three derived occurrences to their shared local supplier without merging source paths', async () => {
    const packet = await load('certified-route-universe'), model = compilePacketRecord(packet, 0, 'derived');
    const uses = packet.payload.uses.filter(use => use.pair === packet.payload.results[0].id && use.role === 'derived');
    const sources = uses.map(use => selectedUseSource(model, use));
    expect(sources).toHaveLength(3);
    expect(sources.every(id => id !== undefined)).toBe(true);
    expect(new Set(sources).size).toBe(3);
    expect(new Set(sources.map(id => selectedUseObject(model, id)))).toEqual(new Set([model.supplierObjectId]));
    expect(new Set(sources.map(id => JSON.stringify(model.sourceById[id!].scopeBinderIds))).size).toBe(1);
  });

  it('distinguishes calls with the same supplier and scope from their empty owner-context vectors', async () => {
    const packet = await load('certified-route-universe'), model = compilePacketRecord(packet, 0, 'derived');
    const uses = packet.payload.uses.flatMap((use, index) => use.pair === packet.payload.results[0].id && use.role === 'derived' ? [{ use, index }] : []);
    const calls = uses.map(({ use }) => selectedUseApplication(model, selectedUseSource(model, use))!);
    expect(calls.map(call => call.text)).toEqual(['(h i (DefinographFixtures.addOp i x y))', '(h i x)', '(h i y)']);
    expect(calls.map(call => call.arguments.map(argument => argument.text))).toEqual([['i', '(DefinographFixtures.addOp i x y)'], ['i', 'x'], ['i', 'y']]);
    expect(uses.map(({ use }) => describeSelectedUse(model.record, use).actuals)).toEqual([[], [], []]);
    expect(new Set(calls.map(call => selectedUseObject(model, call.headSourceId)))).toEqual(new Set([model.supplierObjectId]));
    expect(new Set(calls.map(call => JSON.stringify(model.sourceById[call.headSourceId].scopeBinderIds))).size).toBe(1);
    expect(new Set(calls.map(call => JSON.stringify(call.path))).size).toBe(3);
    expect(new Set(calls.map(call => call.relationId)).size).toBe(3);
    const document = model.document!, cues = compileReadingCues(compileReading(document), document);
    calls.forEach((call, index) => {
      const relation = document.relations.find(item => item.id === call.relationId)!;
      expect(relation.kind).toBe('application');
      expect(relation.nodeId).toBe(call.nodeId);
      expect(model.sourceById[relation.id].path).toEqual(call.path);
      expect(relation.ports.filter(port => port.role.startsWith('input ')).map(port => document.objects.find(item => item.id === port.objectId)!.label)).toEqual(call.arguments.map(argument => argument.text));
      expect(cues.cues.some(cue => cue.stage.relationId === call.relationId)).toBe(true);
      const html = renderToStaticMarkup(createElement(SelectedUseDetails, { packet, index: uses[index].index, readingModel: model, onApplicationSelect: () => {} }));
      expect(html).toContain('Owner-context arguments');
      expect(html).toContain('The owner-context argument vector is empty.');
      expect(html).toContain(`<code class="packet-formula">${call.text}</code>`);
      expect(html).toContain(`<ol>${call.arguments.map(argument => `<li><code>${argument.text}</code></li>`).join('')}</ol>`);
      expect(html).toContain('Show this application in the reader');
      expect(html).not.toContain('All arguments are retained');
    });
  });

  it('keeps an unused owner let and the lifted actual at the selected use', async () => {
    const packet = await load('let-context'), result = packet.payload.results[0];
    const model = describeSelectedUse(result.records.retained, packet.payload.uses[0]);
    expect(model.scope[0]).toMatchObject({ label: 'seed', value: '0', location: 'owner declaration 0' });
    expect(model.actuals).toEqual(['seed']);
    expect(model.scope.slice(1).map(binding => binding.label)).toEqual(['i', 'x', 'y']);
  });

  it('distinguishes unavailable audit metadata from an available empty dependency list', async () => {
    const packet = await load('timeout');
    const html = renderToStaticMarkup(createElement(PacketReading, { packet }));
    expect(html).toContain('Audit unavailable:');
    expect(html).toContain('This is not an empty dependency list');
    expect(html).toContain('Available audit: no axiom dependencies reported ([])');
  });

  it('retains explicit unavailable and available-empty certificate universe states', async () => {
    const original = await load('certified-route-universe');
    // Presentation-only controls: no claim that this modified wrapper was imported.
    const packet = structuredClone(original);
    packet.payload.uses[0].sourceLevels = { tag: 'available', values: [] };
    packet.payload.uses[0].viewLevels = { tag: 'unavailable', reason: 'not captured' };
    const html = renderToStaticMarkup(createElement(SelectedUseDetails, { packet, index: 0 }));
    expect(html).toContain('available empty list');
    expect(html).toContain('Certificate universes unavailable: not captured');
  });

  it('uses exact fallback for unknown constructors and malformed readable-use data', async () => {
    const packet = structuredClone(await load('certified-route-universe'));
    // A UI-boundary control, deliberately not represented as a validated new packet.
    const record = packet.payload.results[0].records.retained!;
    record.table = { rows: [], homes: [] };
    (packet.payload.uses[0].entry as JsonObject).scope = 'unknown future scope';
    const html = renderToStaticMarkup(createElement(SelectedUseDetails, { packet, index: 0 }));
    expect(html).toContain('Readable use unavailable');
    expect(html).toContain('Exact stored use remains available');
  });

  it('discloses an unsupported projection inside a defining value with exact-source inspection', async () => {
    const packet = structuredClone(await load('certified-route-universe'));
    // Presentation-only modified capture: no kernel or packet acceptance claim.
    const check = packet.payload.checks.find(item => item.pair === packet.payload.results[0].id && item.subject.target === 'laws.reading is a proposition')!;
    const value = check.declaration.value as JsonValue[];
    expect(value[0]).toBe('letE');
    value[3] = ['proj', ['str', ['anonymous'], 'UnfamiliarStructure'], 2, ['const', ['str', ['anonymous'], 'unfamiliarOwner'], []]];
    check.subject.declaration = structuredClone(check.declaration);
    const model = compilePacketRecord(packet, 0, 'retained');
    expect(model.document?.opaqueRegions.some(region => region.reason.includes('proj'))).toBe(true);
    const html = renderToStaticMarkup(createElement(PacketReading, { packet }));
    expect(html).toContain('no specialized guided diagram');
    expect(html).toContain('Inspect exact expression:');
    expect(html).toContain('proj');
    expect(html).toContain('Scope and display notes');
    const structure = renderToStaticMarkup(createElement(PacketReading, { packet, initialView: 'structure' }));
    expect(structure).toContain('aria-label="Exact source structure"');
    expect(structure).toContain('data-constructor="proj"');
    expect(structure).toContain('Projected value');
    expect(structure).toContain('UnfamiliarStructure');
    expect(structure).not.toContain('Source structure unavailable');
  });
});
