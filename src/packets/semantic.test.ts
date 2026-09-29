import { readFileSync } from 'node:fs';
import { join } from 'node:path';
import { describe, expect, it } from 'vitest';
import type { Expr, StatementNode } from '../core/types';
import { compileTypedConstruction } from '../constructions/model';
import { compileReading } from '../reading/compiler';
import { applicationFlow } from '../semantic/application-flow';
import { expressionKey, formatExpression } from '../semantic/expression';
import type { SemanticDocument } from '../semantic/types';
import { parsePacket, type CheckReceipt, type ImportedPacket, type JsonObject, type JsonValue, type PacketEnvelope, type PacketPayload, type RecordRole } from './packet';
import { capturedPacketExpression, compilePacketRecord, type PacketRecordReading } from './semantic';

const name = (...parts: string[]): JsonValue => parts.reduce<JsonValue>((parent, part) => ['str', parent, part], ['anonymous']);
const constant = (...parts: string[]): JsonValue => ['const', name(...parts), []];
const variable = (index: number): JsonValue => ['bvar', index];
const app = (fn: JsonValue, ...args: JsonValue[]): JsonValue => args.reduce<JsonValue>((fn, arg) => ['app', fn, arg], fn);
const forall = (label: string, type: JsonValue, body: JsonValue, info = 'default'): JsonValue => ['forallE', name(label), type, body, info];
const letExpr = (label: string, type: JsonValue, value: JsonValue, body: JsonValue, nondep = false): JsonValue => ['letE', name(label), type, value, body, nondep];
const NAT = constant('Nat'), zero: JsonValue = ['lit', ['natVal', 0]];
const eq = (left: JsonValue, right: JsonValue): JsonValue => app(['const', name('Eq'), [['succ', ['zero']]]], NAT, left, right);
const and = (left: JsonValue, right: JsonValue): JsonValue => app(constant('And'), left, right);
const clone = <T,>(value: T): T => structuredClone(value);

/** Synthetic constructor/association controls bypass the transport validator.
 * Their statements are intentionally not claims of successful Lean checking. */
function modelPacket(raw: JsonValue, source?: JsonValue): ImportedPacket {
  const record = { n: 0, owner: ['nil'], table: { rows: [], homes: [] }, uses: [] };
  const checks: CheckReceipt[] = [];
  for (const role of ['retained', 'derived'] as const) {
    for (const association of ['reading', 'source'] as const) {
      if (association === 'source' && source === undefined) continue;
      const id = checks.length, label = `${role === 'retained' ? 'laws' : 'law'}.${association}`;
      const declaration: JsonObject = { kind: 'defnDecl', name: name('Capture', String(id)), type: ['sort', ['zero']], value: association === 'reading' ? raw : source! };
      checks.push({ id, pair: 'unfamiliar-operation', label, declaration, subject: { target: `${label} is a proposition`, pair: 'unfamiliar-operation', sequence: id, attempt: 'constructor-control', declaration },
        envBefore: 0, envAfter: 0, outcome: { tag: 'unknown' } });
    }
  }
  const payload: PacketPayload = { schema: 1, attempt: 'constructor-control', mode: 'synthetic', bank: {}, context: {},
    inputs: [{ id: 'unfamiliar-operation', F: null, G: null }], checks, uses: [], audits: [],
    coherence: { value: false, inputs: [], admissions: [] }, joint: { formation: 'notChecked', evidence: 'notConstructed' },
    results: [{ id: 'unfamiliar-operation', candidate: null, records: { retained: clone(record), derived: clone(record) }, report: { formation: { tag: 'unknown' }, evidence: { tag: 'notFormed' }, checks: [] } }] };
  const value: PacketEnvelope = { schema: 1, request: { id: 'constructor-control', documentRevision: 'revision', sourceSnapshot: 'snapshot' }, basis: {}, payload, bindings: {}, digest: 'unverified-test-data' };
  return { value, payload, identity: 'constructor-control', sourceText: JSON.stringify(value) };
}
function document(packet: ImportedPacket, role: RecordRole = 'derived'): SemanticDocument {
  const result = compilePacketRecord(packet, 0, role);
  expect(result.reason).toBeUndefined(); expect(result.document).toBeDefined(); return result.document!;
}
function sourceAt(packet: ImportedPacket, path: (string | number)[]): JsonValue {
  return path.reduce<JsonValue>((value, key) => (value as JsonObject)[key], packet.value);
}
function topology(document: SemanticDocument): unknown {
  const nodeShape = (node: StatementNode): unknown => [node.kind, node.binder?.role, node.children.map(nodeShape)];
  const indices = new Map(document.objects.map((object, index) => [object.id, index]));
  return { tree: nodeShape(document.tree), objects: document.objects.map(object => [object.kind, object.binder?.role]),
    relations: document.relations.map(relation => [relation.kind, relation.ports.map(port => [port.role, indices.get(port.objectId)])]),
    choices: document.choices.map(choice => [choice.role, choice.dependsOn.length, choice.availableObjectIds.length]) };
}
function allExpressions(expression: Expr): Expr[] {
  if (expression.kind === 'app') return [expression, ...allExpressions(expression.fn), ...expression.args.flatMap(allExpressions)];
  if (expression.kind === 'forall' || expression.kind === 'lambda') return [expression, ...(expression.binderType ? allExpressions(expression.binderType) : []), ...allExpressions(expression.body)];
  return [expression];
}

describe('direct imported packet semantic documents', () => {
  it('retains uniquely attached exact source independently of specialized diagram coverage', () => {
    const raw: JsonValue = ['mdata', {}, zero];
    const packet = modelPacket(raw);
    expect(compilePacketRecord(packet, 0, 'derived').document).toBeUndefined();
    const captured = capturedPacketExpression(packet, 0, 'derived')!;
    expect(captured.syntax).toEqual(raw);
    expect(captured.association).toBe('reading');
    expect(captured.outcome).toBe('unknown');
    expect(sourceAt(packet, captured.path)).toEqual(raw);
    const ambiguous = clone(packet);
    ambiguous.payload.checks.push(clone(ambiguous.payload.checks[1]));
    expect(capturedPacketExpression(ambiguous, 0, 'derived')).toBeUndefined();
  });
  it('preserves all application inputs and exact source paths without inferred metadata', () => {
    const raw = forall('x', NAT, eq(app(constant('Unfamiliar', 'combine'), variable(0), zero, NAT, constant('opaqueEvidence'), zero), variable(0)));
    const packet = modelPacket(raw), reading = compilePacketRecord(packet, 0, 'derived'), doc = reading.document!;
    const relation = doc.relations.find(relation => relation.kind === 'application')!;
    expect(relation.ports.map(port => port.role)).toEqual(['function', 'input 1', 'input 2', 'input 3', 'input 4', 'input 5', 'output']);
    expect(applicationFlow(relation)?.inputIds).toHaveLength(5);
    expect(doc.relations.find(relation => relation.kind === 'equality')?.ports.map(port => port.role)).toEqual(['type', 'left', 'right']);
    for (const expression of allExpressions(doc.tree.expression)) {
      expect(expression.exactIdentity).toBeTruthy(); expect(expression.displayText).toBeTruthy();
      expect(expression).not.toHaveProperty('typeDescriptor'); expect(expression).not.toHaveProperty('argumentKinds');
      expect(expression).not.toHaveProperty('operator'); expect(expression).not.toHaveProperty('canonical');
    }
    for (const item of [...doc.objects, ...doc.relations, ...doc.scopes.map(scope => ({ id: scope.nodeId }))]) {
      const source = reading.sourceById[item.id]; expect(source).toBeDefined(); expect(sourceAt(packet, source.path)).toEqual(source.syntax);
    }
    expect(doc.relations.every(relation => relation.provenance.origin === 'imported-packet')).toBe(true);
    expect(doc.relations.find(relation => relation.kind === 'equality')?.provenance.expressionPath).toBe('expression');
    expect(compileReading(doc).panels).toHaveLength(1);
  });

  it('keeps equal printed names in separate conjuncts bound to distinct identities', () => {
    const body = forall('x', NAT, eq(variable(0), variable(0)));
    const reading = compilePacketRecord(modelPacket(and(body, body)), 0, 'retained'), doc = reading.document!;
    const choices = doc.choices;
    expect(choices).toHaveLength(2); expect(new Set(choices.map(choice => choice.binderId)).size).toBe(2);
    expect(doc.objects.filter(object => object.binder).map(object => object.label)).toEqual(['x', 'x']);
    const equalities = doc.relations.filter(relation => relation.kind === 'equality');
    expect(equalities).toHaveLength(2);
    for (let index = 0; index < 2; index++) {
      const equality = equalities[index];
      expect(equality.ports.filter(port => port.role !== 'type').map(port => port.objectId)).toEqual([choices[index].objectId, choices[index].objectId]);
      expect(reading.sourceById[equality.id].scopeBinderIds).toEqual([choices[index].binderId]);
      expect(doc.scopes.find(scope => scope.id === equality.scopeId)?.objectIds).not.toContain(choices[1 - index].objectId);
    }
  });

  it('preserves constructor topology after unfamiliar global and local renaming', () => {
    const raw = forall('input', constant('Space'), eq(app(constant('Transform'), variable(0)), app(constant('Transform'), variable(0))));
    const renamed = forall('renamed', constant('Qxz'), eq(app(constant('AnotherMap'), variable(0)), app(constant('AnotherMap'), variable(0))));
    expect(topology(document(modelPacket(raw)))).toEqual(topology(document(modelPacket(renamed))));
  });

  it('distinguishes a global constant from a local binder with the same spelling', () => {
    const doc = document(modelPacket(forall('item', NAT, eq(variable(0), constant('item')))));
    const equality = doc.relations.find(relation => relation.kind === 'equality')!;
    const left = doc.objects.find(object => object.id === equality.ports.find(port => port.role === 'left')!.objectId)!;
    const right = doc.objects.find(object => object.id === equality.ports.find(port => port.role === 'right')!.objectId)!;
    expect(left.id).not.toBe(right.id); expect(left.expression.kind).toBe('var'); expect(right.expression.kind).toBe('const');
    expect(formatExpression(left.expression)).toBe('item'); expect(formatExpression(right.expression)).toBe('global(item)');
    expect(expressionKey(left.expression)).not.toBe(expressionKey(right.expression));
    const reused = document(modelPacket(and(eq(constant('item'), zero), forall('item', NAT, eq(variable(0), constant('item'))))));
    const globalObject = reused.objects.find(object => object.expression.kind === 'const' && object.expression.name === 'global(item)');
    expect(globalObject?.label).toBe('global(item)');
    expect(globalObject?.provenance.length).toBeGreaterThan(1);
  });

  it('keeps shared composite labels unambiguous across different shadowing scopes', () => {
    const globalTerm = app(constant('f'), constant('x'), constant('y'));
    const raw = and(app(constant('P'), globalTerm), and(
      forall('x', NAT, app(constant('R'), globalTerm, app(constant('f'), variable(0), constant('y')))),
      forall('y', NAT, app(constant('R'), globalTerm, app(constant('f'), constant('x'), variable(0))))));
    const doc = document(modelPacket(raw));
    const relations = doc.relations.filter(relation => relation.kind === 'application' && relation.label === 'R');
    const globalObjects = relations.map(relation => doc.objects.find(object => object.id === relation.ports.find(port => port.role === 'input 1')!.objectId)!);
    expect(globalObjects[0].id).toBe(globalObjects[1].id);
    expect(globalObjects[0].label).toBe('(f global(x) global(y))');
    for (const relation of relations) {
      const inputs = relation.ports.filter(port => port.role.startsWith('input')).map(port => doc.objects.find(object => object.id === port.objectId)!);
      expect(inputs[0].label).not.toBe(inputs[1].label);
      expect(formatExpression(inputs[0].expression)).toBe(inputs[0].label);
    }
  });

  it('recognizes only the exact built-in Names and both term and universe arities', () => {
    for (const raw of [
      app(['const', name('User', 'Eq'), [['zero']]], NAT, zero, zero),
      app(['const', ['num', ['anonymous'], 7], [['zero']]], NAT, zero, zero),
      app(['const', name('Eq'), []], NAT, zero, zero),
      app(['const', name('Eq'), [['zero']]], NAT, zero, zero, zero),
    ]) expect(document(modelPacket(raw)).relations.some(relation => relation.kind === 'equality')).toBe(false);
    expect(document(modelPacket(app(constant('User', 'And'), constant('P'), constant('Q')))).tree.kind).toBe('predicate');
    expect(document(modelPacket(eq(zero, zero))).relations[0].kind).toBe('equality');
  });

  it('keeps lets as definitions and their exact value and nondep flag in identity', () => {
    const raw = letExpr('seed', NAT, zero, forall('x', NAT, eq(variable(1), variable(0))));
    const doc = document(modelPacket(raw)), other = document(modelPacket(letExpr('seed', NAT, ['lit', ['natVal', 1]], fields(raw)[4])));
    expect(doc.tree.kind).toBe('definition'); expect(doc.tree.binder?.role).toBe('definition');
    expect(doc.tree.binder?.definition?.value).toMatchObject({ kind: 'literal', value: 0 });
    expect(doc.tree.binder?.definition?.nondep).toBe(false);
    expect(doc.choices.map(choice => choice.role)).toEqual(['definition', 'universal']);
    expect(expressionKey(doc.tree.expression)).not.toBe(expressionKey(other.tree.expression));
    const nondep = document(modelPacket(letExpr('seed', NAT, zero, fields(raw)[4], true)));
    expect(expressionKey(doc.tree.expression)).not.toBe(expressionKey(nondep.tree.expression));
    const reading = compileReading(doc);
    expect(reading.root.binder?.role).toBe('definition');
    expect(reading.root.phrase.toLowerCase()).toContain('define');
  });

  it('does not infer implication or hypotheses from a forall domain', () => {
    const doc = document(modelPacket(forall('proof', constant('Prop'), eq(zero, zero))));
    expect(doc.tree.kind).toBe('forall'); expect(doc.tree.binder?.role).toBe('universal');
    expect(doc.scopes.every(scope => scope.assumptionNodeIds.length === 0)).toBe(true);
  });

  it('keeps nested lets and projections as exact, selectable boundaries', () => {
    const nested = letExpr('nested', NAT, zero, variable(0));
    const projection: JsonValue = ['proj', name('User', 'Record'), 2, constant('owner')];
    const packet = modelPacket(app(constant('F'), nested, projection));
    const result = compilePacketRecord(packet, 0, 'derived'), doc = result.document!;
    expect(doc.choices).toHaveLength(0); expect(doc.tree.kind).toBe('predicate');
    expect(doc.relations).toHaveLength(1); expect(doc.opaqueRegions).toHaveLength(2);
    expect(doc.coverage[0].status).toBe('partial');
    expect(doc.opaqueRegions.map(region => result.sourceById[region.id].syntax)).toEqual([nested, projection]);
    expect(doc.opaqueRegions.every(region => /exact source/.test(region.reason))).toBe(true);
    const appExpr = doc.tree.expression;
    expect(appExpr.kind).toBe('app');
    if (appExpr.kind === 'app') expect(appExpr.args.map(arg => arg.kind)).toEqual(['opaque', 'opaque']);
    const definingValue = document(modelPacket(letExpr('fixed', NAT, projection, eq(variable(0), variable(0)))));
    expect(definingValue.opaqueRegions).toHaveLength(1);
    expect(definingValue.opaqueRegions[0].nodeId).toBe(definingValue.tree.id);
    expect(definingValue.diagnostics.join(' ')).toMatch(/proj constructor.*exact-source/);
    expect(definingValue.choices.map(choice => choice.role)).toEqual(['definition']);
  });

  it('preserves universe and binder annotation distinctions in exact identities', () => {
    const a = document(modelPacket(forall('a', ['sort', ['zero']], app(['const', name('C'), [['zero']]], variable(0)), 'implicit')));
    const b = document(modelPacket(forall('a', ['sort', ['zero']], app(['const', name('C'), [['succ', ['zero']]]], variable(0)), 'implicit')));
    const c = document(modelPacket(forall('a', ['sort', ['zero']], app(['const', name('C'), [['zero']]], variable(0)), 'default')));
    expect(expressionKey(a.tree.expression)).not.toBe(expressionKey(b.tree.expression));
    expect(expressionKey(a.tree.expression)).not.toBe(expressionKey(c.tree.expression));
  });

  it('does not invent a nondependent signature when a parameter type contains an opaque dependency', () => {
    const projection: JsonValue = ['proj', name('Pair'), 0, variable(0)];
    const type = forall('x', constant('U'), forall('y', projection, NAT));
    const doc = document(modelPacket(forall('f', type, constant('True'))));
    const reading = compileReading(doc), construction = compileTypedConstruction(doc, reading.quantifierGroups[0].binders);
    expect(construction.signatures).toHaveLength(0); expect(construction.maps).toHaveLength(0);
    expect(construction.unknowns).toHaveLength(1);
  });

  it('associates by bound protocol subjects and never by display label', () => {
    const packet = modelPacket(eq(zero, zero));
    packet.payload.checks.forEach(check => { check.label = 'renamed display label'; });
    expect(compilePacketRecord(packet, 0, 'derived').source.association).toBe('reading');
    const bad = clone(packet); bad.payload.checks.forEach(check => { check.subject.pair = 'another operation'; });
    expect(compilePacketRecord(bad, 0, 'derived').document).toBeUndefined();
    const mismatch = clone(packet); mismatch.payload.checks.forEach(check => { check.subject.declaration = { ...check.declaration, value: constant('Other') }; });
    expect(compilePacketRecord(mismatch, 0, 'derived').document).toBeUndefined();
  });

  it('discloses exact source fallback and refuses to pick an ambiguous reading', () => {
    const packet = modelPacket(eq(constant('View'), zero), eq(constant('Original'), zero));
    const readingCheck = packet.payload.checks.find(check => check.subject.target === 'law.reading is a proposition')!;
    const duplicate = clone(readingCheck); duplicate.id = packet.payload.checks.length; duplicate.subject.sequence = duplicate.id; packet.payload.checks.push(duplicate);
    const result = compilePacketRecord(packet, 0, 'derived');
    expect(result.source.association).toBe('source'); expect(result.reason).toMatch(/ambiguous association/);
    expect(result.document?.objects.some(object => object.expression.kind === 'const' && object.expression.name === 'Original')).toBe(true);
    expect(result.document?.objects.some(object => object.expression.kind === 'const' && object.expression.name === 'View')).toBe(false);
    expect(result.supplierObjectId).toBeUndefined();
  });

  it('retains unknown constructor syntax without flattening it into a supported reading', () => {
    const unknown: JsonValue = ['futureConstructor', ['forallE', name('x'), NAT, variable(0), 'default']];
    const result = compilePacketRecord(modelPacket(unknown), 0, 'derived');
    expect(result.document).toBeUndefined(); expect(result.reason).toMatch(/cannot be diagrammed/);
    expect(Object.values(result.sourceById).some(source => sameSource(source.syntax, unknown))).toBe(true);
  });

  it('does not create a record from receipts when formation retained no record', () => {
    const packet = modelPacket(eq(zero, zero)); packet.payload.results[0].records.derived = null;
    const result = compilePacketRecord(packet, 0, 'derived');
    expect(result.document).toBeUndefined(); expect(result.record).toBeNull(); expect(result.checks).toHaveLength(2);
    expect(compilePacketRecord(packet, -1, 'derived').document).toBeUndefined();
  });
});
function fields(value: JsonValue): JsonValue[] { return value as JsonValue[]; }
function sameSource(a: JsonValue, b: JsonValue): boolean { return JSON.stringify(a) === JSON.stringify(b); }

const fixtureRoot = process.env.DEFINOGRAPH_PACKET_FIXTURES;
async function fixture(mode: string): Promise<ImportedPacket> {
  return parsePacket(readFileSync(join(fixtureRoot!, 'worker-packets', `${mode}.packet.json`), 'utf8'));
}
const modes = ['certified-route-universe', 'let-context', 'missing', 'incoherent', 'refused', 'timeout'];
describe.skipIf(!fixtureRoot)('actual producer records in the existing reader model', () => {
  it('preserves topology in the independently retained renamed packet with repeated labels', async () => {
    const original = await parsePacket(readFileSync(join(fixtureRoot!, 'import-controls', 'ordinary-canonical.json'), 'utf8'));
    const renamed = await parsePacket(readFileSync(join(fixtureRoot!, 'import-controls', 'renamed-with-repeated-labels.json'), 'utf8'));
    expect(original.payload.results).toHaveLength(renamed.payload.results.length);
    for (let index = 0; index < original.payload.results.length; index++) for (const role of ['retained', 'derived'] as const) {
      const before = compilePacketRecord(original, index, role), after = compilePacketRecord(renamed, index, role);
      expect(before.document).toBeDefined(); expect(after.document).toBeDefined();
      expect(topology(after.document!)).toEqual(topology(before.document!));
      expect(after.source.association).toBe(before.source.association);
    }
  });

  it.each(modes)('preserves record availability, captured outcome and usable diagrams in %s', async mode => {
    const packet = await fixture(mode);
    for (let index = 0; index < packet.payload.results.length; index++) {
      for (const role of ['retained', 'derived'] as const) {
        const result = compilePacketRecord(packet, index, role), stored = packet.payload.results[index].records[role];
        expect(result.record).toBe(stored);
        if (stored === null) { expect(result.document).toBeUndefined(); expect(result.reason).toMatch(/no retained or derived record/); continue; }
        expect(result.reason).toBeUndefined(); expect(result.source.association).toBe('reading'); expect(result.supplierObjectId).toBeDefined();
        expect(result.source.outcome).toBe(mode === 'timeout' ? 'unknown' : 'accepted');
        expect(result.document!.relations.filter(relation => relation.kind === 'equality')).toHaveLength(role === 'retained' ? 2 : 1);
        expect(result.document!.relations.some(relation => applicationFlow(relation))).toBe(true);
        expect(compileReading(result.document!).panels).toHaveLength(role === 'retained' ? 2 : 1);
        expect(result.document!.diagnostics.join(' ')).toMatch(/does not establish.*currently checked/);
        expect(result.document!.scenes).toHaveLength(0);
      }
    }
  });

  it('keeps sibling retained locals distinct, derived locals shared, and all suppliers separate', async () => {
    const packet = await fixture('certified-route-universe');
    const readings: PacketRecordReading[] = [];
    for (let index = 0; index < 2; index++) for (const role of ['retained', 'derived'] as const) readings.push(compilePacketRecord(packet, index, role));
    expect(new Set(readings.map(reading => reading.supplierObjectId)).size).toBe(4);
    const retained = readings[0], doc = retained.document!, equalities = doc.relations.filter(relation => relation.kind === 'equality');
    const scopes = equalities.map(relation => retained.sourceById[relation.id].scopeBinderIds);
    expect(scopes[0]).toHaveLength(4); expect(scopes[1]).toHaveLength(4);
    expect(scopes[0][0]).toBe(scopes[1][0]); expect(scopes[0].slice(1).some(id => scopes[1].slice(1).includes(id))).toBe(false);
    const derived = readings[1], supplier = derived.document!.objects.find(object => object.id === derived.supplierObjectId)!;
    expect(supplier.binder?.role).toBe('definition'); expect(supplier.binder?.name).toBe('h');
    const applications = derived.document!.relations.filter(relation => applicationFlow(relation)?.functionId === derived.supplierObjectId);
    expect(applications).toHaveLength(3);
    expect(new Set(applications.map(relation => applicationFlow(relation)!.inputIds[0])).size).toBe(1);
    expect(new Set(applications.map(relation => JSON.stringify(derived.sourceById[relation.id].scopeBinderIds))).size).toBe(1);
  });

  it('retains the owner let and supplier as distinct fixed definitions', async () => {
    const packet = await fixture('let-context'), result = compilePacketRecord(packet, 0, 'derived'), doc = result.document!;
    expect(doc.tree.kind).toBe('definition'); expect(doc.tree.binder?.name).toBe('seed');
    expect(doc.tree.binder?.definition).toMatchObject({ value: { kind: 'literal', value: 0 }, nondep: false });
    expect(doc.tree.children[0].kind).toBe('definition');
    expect(doc.choices.filter(choice => choice.role === 'definition')).toHaveLength(2);
    const supplier = doc.objects.find(object => object.id === result.supplierObjectId)!;
    expect(supplier.binder?.id).toBe(doc.tree.children[0].binder?.id);
    const equality = doc.relations.find(relation => relation.kind === 'equality')!;
    expect(result.sourceById[equality.id].scopeBinderIds).toHaveLength(5);
    expect(result.sourceById[equality.id].scopeBinderIds.slice(0, 2)).toEqual([doc.tree.binder!.id, supplier.binder!.id]);
  });

  it('shows the original source when chosen reading association is unavailable', async () => {
    const packet = clone(await fixture('certified-route-universe'));
    packet.payload.checks.filter(check => check.pair === packet.payload.results[0].id && check.subject.target === 'laws.reading is a proposition')
      .forEach(check => { check.subject.target = 'unavailable reading'; });
    const reading = compilePacketRecord(packet, 0, 'retained');
    expect(reading.source.association).toBe('source'); expect(reading.supplierObjectId).toBeUndefined();
    expect(reading.document!.tree.kind).toBe('and');
    expect(reading.document!.objects.some(object => object.expression.kind === 'const' && object.expression.name === 'DefinographFixtures.addAlias')).toBe(true);
    expect(reading.document!.objects.some(object => object.binder?.role === 'definition')).toBe(false);
    expect(reading.reason).toMatch(/exact captured source statement/);
  });
});
