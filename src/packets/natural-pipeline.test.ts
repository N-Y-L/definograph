import { createHash } from 'node:crypto';
import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import { encodeNatural, naturalText, readNatural } from './natural';
import { parsePacket, type ImportedPacket, type JsonObject, type JsonValue } from './packet';
import { capturedPacketExpression, compilePacketRecord } from './semantic';
import { formatExpr, PacketSyntax, validateExpr } from './syntax';
import { buildStructuralDrawing, readStructuralDrawing } from './structure';
import { describeSelectedUse, PacketReading, selectedUseApplication, selectedUseObject, selectedUseSource } from './PacketReader';

// Production exports and their independently recorded identities stay external.
// Missing fixtures skip this gate; they never count as verified backend output.
const directory = process.env.DEFINOGRAPH_V2_PACKET_FIXTURES;
interface ProductionEntry { mode: string; identity: string; schema: number; origin: string; bytes: number }
const modes = ['certified-route-universe', 'let-context', 'missing', 'incoherent', 'refused', 'timeout'] as const;
function canonical(value: JsonValue): string {
  if (value === null || typeof value !== 'object') return JSON.stringify(value);
  if (Array.isArray(value)) return `[${value.map(canonical).join(',')}]`;
  const keys = Object.keys(value).sort((left, right) => Buffer.compare(Buffer.from(left), Buffer.from(right)));
  return `{${keys.map(key => `${JSON.stringify(key)}:${canonical(value[key])}`).join(',')}}`;
}

describe.skipIf(!directory)('actual v2 packet pipeline', () => {
  const manifest = directory ? JSON.parse(readFileSync(join(directory, 'production.json'), 'utf8')) as ProductionEntry[] : [];
  const loaded = new Map<string, Promise<ImportedPacket>>();
  function load(mode: string): Promise<ImportedPacket> {
    if (!loaded.has(mode)) loaded.set(mode, parsePacket(readFileSync(join(directory!, `${mode}.packet.json`), 'utf8')));
    return loaded.get(mode)!;
  }

  it.each(modes)('imports %s with exactly the backend identity and canonical bytes', async mode => {
    const entry = manifest.find(item => item.mode === mode)!;
    expect(entry).toBeDefined(); expect(entry.schema).toBe(2);
    const bytes = readFileSync(join(directory!, `${mode}.packet.json`));
    const packet = await load(mode), encoded = Buffer.from(canonical(packet.value), 'utf8');
    expect(bytes.byteLength).toBe(entry.bytes);
    expect(encoded.equals(bytes)).toBe(true);
    expect(createHash('sha256').update(bytes).digest('hex')).toBe(entry.identity);
    expect(packet.identity).toBe(entry.identity);
    expect(packet.sourceText).toBe(bytes.toString('utf8'));
    expect(packet.value.schema).toBe(2); expect(packet.payload.schema).toBe(2);
    expect(Object.keys(packet).sort()).toEqual(['identity', 'payload', 'sourceText', 'value']);
    expect(packet).not.toHaveProperty('origin'); expect(packet).not.toHaveProperty('producerProvenance');
    expect(packet).not.toHaveProperty('currentlyCertified'); expect(packet).not.toHaveProperty('jointlyCertified');
    expect(packet.payload.joint).toEqual({ formation: 'notChecked', evidence: 'notConstructed' });
    for (const check of packet.payload.checks) {
      expect(readNatural(check.heartbeatBound, 2)).toEqual(check.heartbeatBound);
      expect(typeof check.id).toBe('number'); expect(typeof check.envBefore).toBe('number');
    }
  });

  it.each(modes)('preserves %s contextual syntax, semantic reading and independent structural readback', async mode => {
    const packet = await load(mode);
    for (let operation = 0; operation < packet.payload.results.length; operation++) for (const role of ['retained', 'derived'] as const) {
      const record = packet.payload.results[operation].records[role];
      const model = compilePacketRecord(packet, operation, role), source = capturedPacketExpression(packet, operation, role);
      expect(model.profile).toBe(2);
      if (record === null) {
        expect(mode).toBe('refused'); expect(operation).toBe(0);
        expect(model.document).toBeUndefined(); expect(source).toBeUndefined();
        continue;
      }
      const syntax = new PacketSyntax(record.table, 2), arity = record.n as number;
      const owner = syntax.owner(record.owner);
      expect(owner).toHaveLength(arity);
      validateExpr(syntax.occ(record.nodeTy, arity), arity, 2);
      validateExpr(syntax.occ(record.sup, arity), arity, 2);
      expect(model.document, model.reason).toBeDefined(); expect(source).toBeDefined();
      const drawing = buildStructuralDrawing(source!.syntax, {
        sourceIdentity: `${packet.identity}:${operation}:${role}`, sourcePath: source!.path, profile: 2,
      });
      expect(drawing.ok, JSON.stringify(drawing)).toBe(true);
      if (!drawing.ok) continue;
      expect(drawing.value.schema).toBe('definograph.structure.v2');
      expect(readStructuralDrawing(drawing.value)).toEqual({ ok: true, value: { expression: source!.syntax, externalContext: [] } });
      expect(model.document!.source).toBe(formatExpr(source!.syntax, [], 2));
      const bound = drawing.value.nodes.filter(node => node.kind === 'bvar');
      expect(bound.length).toBeGreaterThan(0);
      for (const reference of bound) {
        if (reference.kind !== 'bvar') continue;
        expect(Number.isSafeInteger(reference.index)).toBe(true);
        const original = reference.sourcePath.reduce<JsonValue>((value, part) => Array.isArray(value) ? value[Number(part)] : (value as JsonObject)[String(part)], packet.value);
        expect(original).toEqual(['bvar', encodeNatural(reference.index, 2)]);
        expect(drawing.value.declarations.some(declaration => declaration.id === reference.declarationId)).toBe(true);
      }
    }
  });

  it('keeps qualified use identity, certificate routes and call scope distinct in actual v2 data', async () => {
    const packet = await load('certified-route-universe');
    const bindings = packet.value.bindings.uses as JsonObject[];
    expect(bindings).toHaveLength(10);
    expect(new Set(bindings.map(binding => canonical(binding.id))).size).toBe(10);
    for (const use of packet.payload.uses) expect(naturalText(use.oid, 2)).toMatch(/^[0-9]+$/);
    const retainedUse = packet.payload.uses.find(use => use.pair === packet.payload.results[0].id && use.role === 'retained')!;
    const retained = describeSelectedUse(packet.payload.results[0].records.retained, retainedUse, 2);
    expect(retained.source).toContain('addAlias'); expect(retained.view).toContain('addOp');
    expect(retained.sourceCertificate.label).toContain('genericRefl');
    expect(retained.sourceCertificate.arguments).toHaveLength(2);
    expect(retained.sourceCertificate.arguments[0]).toContain('Operation');
    expect(retained.sourceCertificate.arguments[1]).toContain('addOp');
    expect(retained.viewCertificate.arguments).toEqual([]);
    expect(retained.scope.map(binding => binding.label)).toEqual(['i', 'x', 'y']);
    const model = compilePacketRecord(packet, 0, 'derived');
    const uses = packet.payload.uses.filter(use => use.pair === packet.payload.results[0].id && use.role === 'derived');
    const heads = uses.map(use => selectedUseSource(model, use)!);
    expect(uses.map(use => naturalText(use.oid, 2))).toEqual(['0', '1', '2']);
    expect(new Set(heads).size).toBe(3);
    expect(new Set(heads.map(head => selectedUseObject(model, head)))).toEqual(new Set([model.supplierObjectId]));
    expect(new Set(heads.map(head => JSON.stringify(model.sourceById[head].scopeBinderIds))).size).toBe(1);
    expect(heads.map(head => selectedUseApplication(model, head)?.arguments.map(argument => argument.text)))
      .toEqual([['i', '(DefinographFixtures.addOp i x y)'], ['i', 'x'], ['i', 'y']]);
  });

  it('retains the owner let and its owner-context argument without confusing either with a call argument', async () => {
    const packet = await load('let-context'), result = packet.payload.results[0];
    const use = packet.payload.uses.find(item => item.pair === result.id && item.role === 'retained')!;
    const detail = describeSelectedUse(result.records.retained, use, 2);
    expect(detail.scope[0]).toMatchObject({ label: 'seed', value: '0', location: 'owner declaration 0' });
    expect(detail.actuals).toEqual(['seed']);
    const model = compilePacketRecord(packet, 0, 'retained'), head = selectedUseSource(model, use);
    const call = selectedUseApplication(model, head);
    expect(call).toBeDefined();
    expect(call!.arguments.map(argument => argument.text)).not.toEqual(detail.actuals);
    expect(model.sourceById[head!].scopeBinderIds).toHaveLength(5);
  });

  it.each([
    ['certified-route-universe', ['formed', 'formed'], ['certified', 'certified'], true],
    ['let-context', ['formed', 'formed'], ['certified', 'certified'], true],
    ['missing', ['formed', 'formed'], ['missing', 'certified'], true],
    ['incoherent', ['formed', 'formed'], ['certified', 'certified'], false],
    ['refused', ['refused', 'formed'], ['notFormed', 'certified'], true],
    ['timeout', ['unknown', 'unknown'], ['notFormed', 'notFormed'], true],
  ] as const)('keeps %s reports unverified while both presentation choices remain available', async (mode, formation, evidence, coherent) => {
    const packet = await load(mode);
    expect(packet.payload.results.map(result => result.report.formation.tag)).toEqual(formation);
    expect(packet.payload.results.map(result => result.report.evidence.tag)).toEqual(evidence);
    expect(packet.payload.coherence.value).toBe(coherent);
    for (const initialView of ['guided', 'structure'] as const) {
      const html = renderToStaticMarkup(createElement(PacketReading, { packet, initialView, initialOperationIndex: mode === 'refused' ? 1 : 0 }));
      expect(html).toContain('Unverified imported packet');
      expect(html).toContain('no joint certification is established');
      expect(html).not.toContain('Readable use unavailable');
      expect(html).not.toContain('Source structure unavailable');
      if (initialView === 'structure') expect(html).toContain('aria-label="Exact source structure"');
      else expect(html).toContain('aria-label="Guided visual sequence"');
    }
  });
});
