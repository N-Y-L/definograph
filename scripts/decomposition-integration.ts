/** Fresh user records exercise generic reflection and shared primitives, with
 * no record-specific semantic plugin or rendering rule. */
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createElement, type ComponentType } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { createServer } from 'vite';
import { structureFixtures, type StructureFixture } from '../corpus/structures.ts';
import { analyzeEditorContext } from '../server/editor-context.ts';
import type { Analysis, Expr, StatementNode } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/compiler.ts';
import { compileReading, compileReadingCues } from '../src/reading/index.ts';
import { compileStructuralObject } from '../src/decomposition/compiler.ts';
import type { StructuralObjectModel } from '../src/decomposition/types.ts';
import type { StructuralObjectFigureProps } from '../src/decomposition/StructuralObjectFigure.tsx';
import type { StatementReadingViewProps } from '../src/visual/StatementReadingView.tsx';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const config = JSON.parse(await readFile(path.join(rootDir, '.local/config.json'), 'utf8')) as { leanPath: string[]; contextExecutable: string; workerExecutable: string };
const hash = async (file: string) => createHash('sha256').update(await readFile(file)).digest('hex');
const hashes = async () => Promise.all([hash(config.contextExecutable), hash(config.workerExecutable)]);
const originalHashes = await hashes();
const temporary = await mkdtemp(path.join(os.tmpdir(), 'statementlens-decomposition-'));
const snapshots = new Map<string, string>(), prior = new Map<string, unknown>();
const ssr = await createServer({ configFile: false, root: rootDir, appType: 'custom', server: { middlewareMode: true, watch: null, hmr: false, ws: false } });
let StructuralObjectFigure: ComponentType<StructuralObjectFigureProps>;
let StatementReadingView: ComponentType<StatementReadingViewProps>;
const allNodes = (tree: StatementNode): StatementNode[] => [tree, ...tree.children.flatMap(allNodes)];
const position = (source: string, offset: number) => { const lines = source.slice(0, offset).split('\n'); return { line: lines.length - 1, character: lines.at(-1)!.length }; };
const expressionHead = (expression: Expr): string => expression.kind === 'app' ? expressionHead(expression.fn) : expression.kind === 'const' ? expression.name : expression.kind;
function vars(expression: Expr): string[] {
  if (expression.kind === 'var') return [expression.id];
  if (expression.kind === 'app') return [...vars(expression.fn), ...expression.args.flatMap(vars)];
  if (expression.kind === 'forall' || expression.kind === 'lambda') return [...(expression.binderType ? vars(expression.binderType) : []), ...vars(expression.body)];
  return [];
}

/** Compare checked mathematical syntax with user names removed. */
function fingerprint(model: StructuralObjectModel): unknown {
  const reflection = model.object.binder!.structure!;
  const names = new Map(reflection.fields.map((field, index) => [field.projection, `field:${index}`]));
  names.set(reflection.name, 'record');
  reflection.fields.forEach((field, fieldIndex) => field.typeExpansion?.constants.forEach((name, aliasIndex) => names.set(name, `alias:${fieldIndex}:${aliasIndex}`)));
  const localIds = new Map<string, number>();
  function shape(expression: Expr): unknown {
    if (expression.kind === 'var') { if (!localIds.has(expression.id)) localIds.set(expression.id, localIds.size); return ['var', localIds.get(expression.id)]; }
    if (expression.kind === 'const') return ['const', names.get(expression.name) ?? expression.name];
    if (expression.kind === 'app') return ['app', shape(expression.fn), expression.args.map(shape)];
    if (expression.kind === 'forall' || expression.kind === 'lambda') {
      if (!localIds.has(expression.binder.id)) localIds.set(expression.binder.id, localIds.size);
      return [expression.kind, localIds.get(expression.binder.id), expression.binderType && shape(expression.binderType), shape(expression.body)];
    }
    if (expression.kind === 'literal') return ['literal', expression.value];
    if (expression.kind === 'sort') return ['sort', expression.name];
    if (expression.kind === 'opaque') return ['opaque', expression.text];
    throw new Error('Unexpected expression shape');
  }
  const fields = reflection.fields.map(field => [field.kind, shape(field.typeExpansion?.expression ?? field.typeExpression), field.dependsOn.map(name => reflection.fields.findIndex(candidate => candidate.name === name))]);
  const fieldId = (id: string) => model.fields.findIndex(field => field.object.id === id);
  const typeId = (id: string) => model.construction.types.findIndex(type => type.id === id);
  return { fields, maps: model.construction.maps.map(map => [fieldId(map.objectId), typeId(map.domainId), typeId(map.codomainId)]),
    members: model.construction.members.map(member => [fieldId(member.objectId), member.kind, typeId(member.typeId)]),
    signatures: model.construction.signatures.map(signature => [fieldId(signature.objectId), signature.kind, signature.inputs.length, signature.inputs.map(input => input.dependsOn), signature.resultDependsOn]),
    laws: model.fields.filter(field => field.kind === 'law').map(field => field.lawDocument?.relations.map(relation => relation.kind).sort()) };
}

function renderModel(model: StructuralObjectModel): string {
  const warnings: string[] = [], originalError = console.error;
  console.error = (...items: unknown[]) => { warnings.push(items.map(String).join(' ')); };
  try {
    const html = renderToStaticMarkup(createElement(StructuralObjectFigure, { model, onObjectSelect: () => undefined,
      renderLaw: field => field.lawDocument && field.lawReading ? createElement(StatementReadingView, { document: field.lawDocument, reading: field.lawReading, onObjectSelect: () => undefined }) : null }));
    assert.deepEqual(warnings, [], 'Generic structure and ordinary law reader must render without React errors');
    return html;
  } finally { console.error = originalError; }
}

function checkModel(fixture: StructureFixture, model: StructuralObjectModel): void {
  const reflection = model.object.binder!.structure!;
  assert.equal(reflection.name, fixture.structureName);
  assert.equal(reflection.kernelChecked, true);
  assert.deepEqual(reflection.limits, { maxFields: 16, maxFieldNodes: 120, maxDepth: 24 });
  assert.ok(reflection.fields.length <= reflection.limits.maxFields);
  assert.ok(Buffer.byteLength(JSON.stringify(reflection), 'utf8') <= 131072, 'Native reflection exceeds its advertised payload bound');
  assert.equal(new Set(reflection.fields.map(field => field.projection)).size, reflection.fields.length);
  if (fixture.fields.length) assert.deepEqual(reflection.fields.map(field => ({ name: field.name, kind: field.kind })), fixture.fields);
  if (fixture.declaredAlias) assert.ok(model.object.type.includes(fixture.declaredAlias), 'The original alias name disappeared');
  if (fixture.ownerRole) assert.equal(model.object.binder!.role, fixture.ownerRole);
  for (const [index, field] of reflection.fields.entries()) {
    assert.equal(expressionHead(field.expression), field.projection, 'Each reflected value must be the exact declared projector');
    assert.ok(vars(field.expression).includes(model.object.binder!.id), 'A field must belong to the actual introduced owner');
    for (const dependency of field.dependsOn) assert.ok(reflection.fields.slice(0, index).some(candidate => candidate.name === dependency), 'A field dependency must precede it');
    const composed = model.fields.find(candidate => candidate.projection === field.projection)!;
    assert.ok(composed);
    if (field.kind === 'law') {
      assert.ok(field.law && composed.lawDocument && composed.lawReading, 'A proof field needs its exported law and shared logical reader');
      assert.ok(allNodes(field.law!).every(node => !node.binder?.structure), 'Law reflection must not recursively expand nested records');
      const document = composed.lawDocument!, reading = composed.lawReading!;
      assert.deepEqual(document.diagnostics, []);
      assert.equal(document.scenes.length, 0, 'Generic reflection must not invent numerical coordinates');
      const objectIds = new Set(document.objects.map(object => object.id));
      for (const relation of document.relations) relation.ports.forEach(port => assert.ok(objectIds.has(port.objectId), 'A law port lost its exact object'));
      const cues = compileReadingCues(reading, document);
      assert.equal(cues.truncated, false);
      for (const cue of cues.cues) assert.deepEqual(cue.assumptionNodeIds, document.scopes.find(scope => scope.id === cue.scopeId)!.assumptionNodeIds);
      assert.ok(document.choices.some(choice => choice.objectId === model.object.id), 'A supplementary law must retain its owner as explicit local context');
      if (fixture.ownerRole === 'assumption') assert.ok(document.choices.some(choice => choice.objectId === model.object.id && choice.role === 'assumption'), 'A proof-record law must retain the hypothesis that supplies it');
    }
  }
  const html = renderModel(model);
  assert.ok(html.includes(`data-structural-object="${model.object.id}"`));
  assert.ok(html.includes('within the statement’s current quantifiers and assumptions'));
  for (const field of model.fields.filter(field => field.kind === 'data')) assert.ok(html.includes(`data-reading-object="${field.object.id}"`), `Data field ${field.name} disappeared from the figure`);
  const laws = model.fields.filter(field => field.kind === 'law');
  if (laws.length) {
    assert.ok(html.includes(`data-structural-law="${laws[0]!.projection}"`));
    assert.ok(html.includes('Law of this object'));
    for (const law of laws) assert.ok(html.includes(law.name), 'Every law must remain selectable');
  }
  if (fixture.fieldCount !== undefined) {
    assert.equal(reflection.fields.length, 16);
    assert.equal(reflection.omittedFields, fixture.fieldCount - reflection.fields.length);
    assert.equal(model.omittedFields, reflection.omittedFields);
    assert.ok(reflection.stopReason && html.includes(`${model.omittedFields} further fields remain`));
  } else assert.equal(reflection.omittedFields, 0);

  if (fixture.id === 'unseen-restricted-record' || fixture.id === 'unseen-aliased-record') {
    assert.equal(model.construction.maps.length, 2, 'Two arbitrary-named function fields must become ordinary map primitives');
    assert.equal(model.construction.members.filter(member => member.kind === 'set').length, 2, 'The checked Set alias must become the same set primitive');
    const tag = model.fields.find(field => field.name === 'tag')!;
    assert.ok(model.construction.members.some(member => member.objectId === tag.object.id), 'An unused scalar field must remain part of the record');
    const roundTrip = model.fields.find(field => field.name === 'roundTrip')!;
    assert.ok(roundTrip.lawDocument!.relations.some(relation => relation.kind === 'equality'));
    assert.ok(roundTrip.lawDocument!.relations.some(relation => relation.kind === 'membership'));
    assert.equal(roundTrip.lawDocument!.relations.filter(relation => relation.kind === 'application').length, 2, 'The two field-map applications must compose through generic application primitives');
    assert.ok(roundTrip.lawDocument!.scopes.some(scope => scope.assumptionNodeIds.length > 0), 'The inverse law must retain its set-membership premise');
  }
  if (fixture.id === 'unseen-algebra-record') {
    const carrier = model.fields.find(field => field.name === 'Carrier')!, combine = model.fields.find(field => field.name === 'combine')!, seed = model.fields.find(field => field.name === 'seed')!;
    assert.ok(model.construction.types.some(type => type.objectId === carrier.object.id), 'The internal carrier must retain its field identity');
    const signature = model.construction.signatures.find(signature => signature.objectId === combine.object.id)!;
    assert.ok(signature && signature.inputs.length === 2, 'A binary operation requires a two-input generic signature');
    const member = model.construction.members.find(member => member.objectId === seed.object.id)!;
    assert.equal(model.construction.types.find(type => type.id === member.typeId)!.objectId, carrier.object.id, 'The element and operation must not split their shared projected carrier');
    const associate = model.fields.find(field => field.name === 'associate')!;
    assert.equal(associate.lawDocument!.relations.filter(relation => relation.kind === 'application').length, 4);
    assert.ok(associate.lawDocument!.relations.some(relation => relation.kind === 'equality'));
  }
  if (fixture.opaqueLawHead) {
    const law = model.fields.find(field => field.kind === 'law')!;
    assert.ok(law.lawDocument!.opaqueRegions.some(region => expressionHead(region.expression) === fixture.opaqueLawHead), 'An opaque predicate must not acquire invented mathematical meaning');
    assert.ok(html.includes(fixture.opaqueLawHead));
    const hidden = model.fields.find(field => field.name === 'unexplained')!;
    assert.equal(hidden.type, 'HiddenCarrier');
    assert.ok(html.includes('HiddenCarrier') && html.includes(`data-reading-object="${hidden.object.id}"`));
  }
}

let passed = 0, failed = 0;
try {
  const toolchain = path.join(temporary, 'lean-toolchain');
  await writeFile(toolchain, 'leanprover/lean4:v4.28.0\n'); snapshots.set(toolchain, 'leanprover/lean4:v4.28.0\n');
  ({ StructuralObjectFigure } = await ssr.ssrLoadModule('/src/decomposition/StructuralObjectFigure.tsx'));
  ({ StatementReadingView } = await ssr.ssrLoadModule('/src/visual/StatementReadingView.tsx'));
  for (const fixture of structureFixtures) {
    try {
      const fileName = path.join(temporary, `${fixture.id}.lean`), saved = '-- Saved fixture intentionally differs from the submitted buffer.\n';
      await writeFile(fileName, saved); snapshots.set(fileName, saved);
      const offset = fixture.source.lastIndexOf(fixture.selection);
      assert.ok(offset >= 0);
      const response = await analyzeEditorContext({ engineDirectory: rootDir, fileName, source: fixture.source, selection: { start: position(fixture.source, offset), end: position(fixture.source, offset + fixture.selection.length) }, workspaceTrusted: true, libraryPaths: config.leanPath.filter(entry => !entry.includes('/leantex/')) });
      assert.equal(response.ok, true, JSON.stringify(response));
      const analysis = response as unknown as Analysis, primaryTree = JSON.stringify(analysis.tree);
      assert.ok(!analysis.diagnostics.some(diagnostic => diagnostic && typeof diagnostic === 'object' && 'severity' in diagnostic && diagnostic.severity === 'error'));
      const document = compileSemanticDocument(analysis), reading = compileReading(document);
      assert.deepEqual(document.diagnostics, []);
      const owners = document.objects.filter(object => object.binder?.structure?.name === fixture.structureName);
      if (fixture.reflectionMayBeUnavailable && !owners.length) {
        const retained = document.objects.find(object => object.binder?.type.includes(fixture.declaredAlias ?? fixture.structureName));
        assert.ok(retained, 'Unavailable reflection must retain its declared object');
        assert.ok(JSON.stringify(analysis).length < 262144, 'A deep or recursive input must remain bounded');
        if (fixture.id === 'deep-user-alias') {
          assert.ok(retained.binder!.structureOmission, 'The type-head expansion limit must be explicit');
          const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, onObjectSelect: () => undefined }));
          assert.ok(html.includes('sd-remaining') && html.includes(fixture.declaredAlias!), 'The production reader must show the inspection boundary and original type');
        }
      } else {
        assert.equal(owners.length, fixture.owners ?? 1, 'Generic inspection failed to expose an unfamiliar record');
        const models = owners.map(owner => { const model = compileStructuralObject(document, owner); assert.ok(model, 'A checked unfamiliar record needs a generic composition'); return model; });
        models.forEach(model => checkModel(fixture, model));
        for (const owner of owners) {
          const introduction = reading.nodes.find(node => node.binder?.objectId === owner.id)!;
          assert.ok(introduction, 'The original reading must retain the structure owner introduction');
          const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading: compileReading(document, { selectedNodeId: introduction.id }), onObjectSelect: () => undefined }));
          assert.ok(html.includes(`data-structural-object="${owner.id}"`), 'The production statement reader must expose the generic object diagram');
          for (const panel of reading.panels) assert.ok(html.includes(`data-reading-node="${panel.nodeId}"`), 'Supplementary laws must not replace original clauses');
          const scope = document.scopes.find(scope => scope.id === owner.scopeId)!;
          const model = models.find(model => model.object.id === owner.id)!;
          for (const field of model.fields) assert.ok(scope.objectIds.includes(field.object.id), 'Fields must become available in the same scope as their owner');
        }
        if (fixture.compareRenameWith) {
          assert.ok(prior.has(fixture.compareRenameWith), 'The renaming baseline must pass before comparison');
          assert.deepEqual(fingerprint(models[0]!), prior.get(fixture.compareRenameWith), 'Renaming the record and all fields changed common primitive topology');
        }
        prior.set(fixture.id, fingerprint(models[0]!));
        if (models.length > 1) {
          assert.equal(new Set(models.flatMap(model => model.fields.map(field => field.object.id))).size, models.reduce((total, model) => total + model.fields.length, 0), 'Same-named sibling owners cannot share field identities');
          for (const owner of owners) {
            const scope = document.scopes.find(scope => scope.id === owner.scopeId)!;
            assert.ok(owners.filter(other => other.id !== owner.id).every(other => !scope.objectIds.includes(other.id)));
            const cue = compileReadingCues(reading, document).cues.find(cue => cue.binders.some(binder => binder.objectId === owner.id))!;
            assert.ok(cue.roles.includes('negated') && cue.roles.includes('alternative') && cue.roles.includes('witness'));
            const ownModel = models.find(model => model.object.id === owner.id)!;
            const foreignIds = new Set(models.filter(model => model.object.id !== owner.id).flatMap(model => [model.object.id, ...model.fields.map(field => field.object.id)]));
            for (const field of ownModel.fields.filter(field => field.lawDocument)) assert.ok(field.lawDocument!.objects.every(object => !foreignIds.has(object.id)), 'A sibling record or projected field leaked into this supplementary law');
          }
        }
      }
      assert.equal(JSON.stringify(analysis.tree), primaryTree, 'Supplementary laws must not mutate the selected statement tree');
      passed++; console.log(`PASS ${fixture.title}`);
    } catch (error) { failed++; console.error(`FAIL ${fixture.title}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  for (const [file, source] of snapshots) assert.equal(await readFile(file, 'utf8'), source, 'Private fixture source/configuration changed');
  assert.deepEqual(await hashes(), originalHashes, 'Native binaries changed during the generic audit; rerun after builds finish');
  console.log(`${passed}/${structureFixtures.length} unseen user-record → common primitives → production renderer checks passed. Private source/configuration remained unchanged.`);
  process.exitCode = failed ? 1 : 0;
} finally { await ssr.close(); await rm(temporary, { recursive: true, force: true }); }
