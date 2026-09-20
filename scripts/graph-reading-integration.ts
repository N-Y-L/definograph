import assert from 'node:assert/strict';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createElement, type ComponentType } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { createServer } from 'vite';
import { createWorkerBackend } from '../server/worker.ts';
import type { Analysis } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import type { SemanticDocument, SemanticRelation } from '../src/semantic/types.ts';
import { compileReading, compileReadingCues, type ReadingDocument, type ReadingCuePlan } from '../src/reading/index.ts';
import { compileGraphConstraint } from '../src/graphs/model.ts';
import type { StatementReadingViewProps } from '../src/visual/StatementReadingView.tsx';

const rootDir = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
const backend = createWorkerBackend({ rootDir });
// Compile the actual browser renderer and styles in-process, without a browser
// or a listening development server.
const ssr = await createServer({ configFile: false, root: rootDir, appType: 'custom', server: { middlewareMode: true, watch: null, hmr: false, ws: false } });
interface Compiled { analysis: Analysis; document: SemanticDocument; reading: ReadingDocument; cues: ReadingCuePlan; html: string }
interface Case { name: string; source: string; check: (result: Compiled) => void }
let StatementReadingView: ComponentType<StatementReadingViewProps>;
const graphRelations = (document: SemanticDocument, kind?: string) => document.relations.filter(relation => kind ? relation.kind === kind : relation.pluginId === 'graphs');
const port = (relation: SemanticRelation, role: string) => relation.ports.find(port => port.role === role)!.objectId;

function render(document: SemanticDocument, selectedNodeId?: string): string {
  const reading = compileReading(document, { selectedNodeId });
  const warnings: string[] = [], originalError = console.error;
  console.error = (...items: unknown[]) => { warnings.push(items.map(String).join(' ')); };
  try {
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
    assert.equal(warnings.length, 0, `React could not faithfully render the graph reader: ${warnings[0]?.slice(0, 260)}`);
    return html;
  } finally { console.error = originalError; }
}
function activeGuide(html: string): string {
  const start = html.indexOf('<section class="reading-guide"');
  const end = html.indexOf('<details class="sr-complete-reading"', start);
  assert.ok(start >= 0 && end > start, 'The complete reader must include its guide and full statement');
  return html.slice(start, end);
}
function figure(html: string, relation: SemanticRelation): string {
  const marker = html.indexOf(`data-graph-relation="${relation.id}"`);
  assert.ok(marker >= 0, `Missing graph figure for ${relation.id}`);
  const start = html.lastIndexOf('<figure', marker), end = html.indexOf('</figure>', marker);
  assert.ok(start >= 0 && end > marker);
  return html.slice(start, end + '</figure>'.length);
}
function assertBinder(result: Compiled, relation: SemanticRelation): void {
  assert.equal(relation.provenance.expressionPath, 'binder.type');
  const node = result.reading.nodes.find(node => node.id === relation.nodeId)!;
  assert.ok(node.binder);
  assert.equal(relation.scopeId, node.scopeId);
  const scope = result.document.scopes.find(scope => scope.id === relation.scopeId)!;
  const valueId = port(relation, relation.kind === 'graph-coloring' ? 'coloring' : 'map');
  assert.equal(valueId, node.binder!.objectId);
  assert.ok(scope.objectIds.includes(valueId));
  const cue = result.cues.cues.find(cue => cue.sourceNodeIds.includes(node.id))!;
  assert.equal(cue.intent, 'introduce');
  assert.ok(cue.focusRelationIds.includes(relation.id), 'Bundled properties belong to the binder introduction');
  assert.ok(cue.binders.some(binder => binder.objectId === valueId));
  const rendered = activeGuide(render(result.document, node.id));
  assert.ok(figure(rendered, relation).includes(`data-graph-scope="${relation.scopeId}"`));
  for (const position of cue.branchPath.filter(position => !['body', 'result'].includes(position.edge.role))) {
    assert.ok(rendered.includes(`data-logic-role="${position.edge.role}"`), 'A binder annotation lost its enclosing logical role');
  }
}
async function compile(source: string): Promise<Compiled> {
  const response = await backend.analyze(source);
  assert.equal(response.ok, true, String(response.error ?? 'Native Lean rejected graph reading fixture'));
  const analysis = response as unknown as Analysis;
  const document = compileSemanticDocument(analysis), reading = compileReading(document), cues = compileReadingCues(reading, document);
  const html = render(document);
  assert.equal(cues.truncated, false);
  assert.ok(graphRelations(document).length > 0);
  for (const relation of graphRelations(document)) {
    assert.ok(compileGraphConstraint(document, relation), `Graph relation has no scoped model: ${relation.id}`);
    const isIntroduction = relation.provenance.expressionPath === 'binder.type';
    const isClauseRoot = reading.panels.some(panel => panel.rootRelationIds.includes(relation.id));
    if (isIntroduction || isClauseRoot) figure(html, relation);
    else assert.ok(cues.cues.some(cue => cue.stage.relationId === relation.id), 'An inner graph construction must remain available as a scoped guide stage');
  }
  for (const panel of reading.panels) assert.ok(html.includes(`data-reading-node="${panel.nodeId}"`), 'An atomic clause disappeared from the static statement');
  assert.ok(html.includes('Whole statement'));
  assert.ok(!html.includes('type="range"') && !html.includes('type="number"'), 'The graph reader must not require sampled coordinates');
  return { analysis, document, reading, cues, html };
}

const cases: Case[] = [
  { name: 'typed colorings retain introduction scope and precede their inequality', source: '∀ (V C : Type) (G : SimpleGraph V) (c : G.Coloring C) (u v : V), G.Adj u v → c u ≠ c v', check: result => {
    const colorings = graphRelations(result.document, 'graph-coloring');
    assert.equal(colorings.length, 3);
    const binder = colorings.find(relation => relation.provenance.expressionPath === 'binder.type')!;
    assertBinder(result, binder);
    const applications = colorings.filter(relation => relation.ports.some(port => port.role === 'vertex'));
    const clause = result.reading.panels.find(panel => applications.some(relation => relation.nodeId === panel.nodeId))!;
    const stages = result.cues.cues.filter(cue => cue.panelId === clause.id);
    assert.deepEqual(stages.map(cue => cue.stage.relationKind), ['graph-coloring', 'graph-coloring', 'equality']);
    assert.deepEqual(stages.map(cue => cue.stage.kind), ['construction', 'construction', 'clause']);
    const root = result.document.relations.find(relation => relation.id === clause.rootRelationIds[0])!;
    assert.equal(root.label, '≠');
    for (const application of applications) {
      assert.ok(root.ports.some(argument => argument.objectId === port(application, 'color')));
      assert.match(result.document.objects.find(object => object.id === port(application, 'color'))!.label, /^c\([uv]\)$/);
      assert.ok(clause.groups[0]!.connections.some(connection => connection.fromRelationId === application.id && connection.toRelationId === root.id && connection.kind === 'feeds'));
      assert.equal(stages.find(cue => cue.stage.relationId === application.id)!.assumptionNodeIds.length, 1);
    }
    const rendered = activeGuide(render(result.document, clause.nodeId));
    assert.ok(rendered.includes('data-logic-role="conclusion"'));
    assert.ok(rendered.includes('Constructing part of'));
    assert.ok(rendered.includes('source application'));
    const introduction = activeGuide(render(result.document, binder.nodeId));
    assert.ok(introduction.includes('class="typed-construction"'), 'Removing a coloring annotation must not invalidate the remaining carrier/vertex introduction');
  } },
  { name: 'graph homomorphism images feed target adjacency without acquiring injectivity', source: '∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : SimpleGraph.Hom G H) (u v : V), G.Adj u v → H.Adj (f u) (f v)', check: result => {
    const maps = graphRelations(result.document, 'graph-map');
    assert.equal(maps.length, 3);
    const binder = maps.find(relation => relation.provenance.expressionPath === 'binder.type')!;
    assertBinder(result, binder);
    assert.ok(maps.every(relation => relation.graphMapKind === 'homomorphism'));
    const target = graphRelations(result.document, 'graph-adjacency').find(relation => result.document.scopes.find(scope => scope.id === relation.scopeId)!.assumptionNodeIds.length)!;
    const stages = result.cues.cues.filter(cue => cue.nodeId === target.nodeId);
    assert.deepEqual(stages.map(cue => cue.stage.relationKind), ['graph-map', 'graph-map', 'graph-adjacency']);
    const application = maps.find(relation => relation.id === stages[0]!.stage.relationId)!;
    const guide = activeGuide(render(result.document, target.nodeId));
    assert.ok(guide.includes('data-logic-role="conclusion"') && guide.includes('Constructing part of'));
    assert.ok(figure(guide, application).includes(`data-graph-scope="${application.scopeId}"`));
    assert.match(result.document.objects.find(object => object.id === port(application, 'target vertex'))!.label, /^f\([uv]\)$/);
    assert.ok(figure(result.html, binder).includes('injectivity is not required'));
    assert.ok(!figure(result.html, binder).includes('if and only if'));
  } },
  { name: 'embeddings retain reflected adjacency and injectivity at their introduction', source: '∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : SimpleGraph.Embedding G H) (u : V), f u = f u', check: result => {
    const maps = graphRelations(result.document, 'graph-map');
    assert.equal(maps.length, 2);
    assert.ok(maps.every(relation => relation.graphMapKind === 'embedding'));
    const binder = maps.find(relation => relation.provenance.expressionPath === 'binder.type')!;
    assertBinder(result, binder);
    const rendered = figure(result.html, binder);
    assert.ok(rendered.includes('preserved and reflected') && rendered.includes('distinct vertices have distinct images'));
    assert.ok(!rendered.includes('surjective'));
  } },
  { name: 'existential colorings remain inside negation and their disjunction alternative', source: '∀ (V C : Type) (G : SimpleGraph V), ¬ ((∃ c : G.Coloring C, True) ∨ G.Colorable 4)', check: result => {
    const binder = graphRelations(result.document, 'graph-coloring')[0]!;
    assertBinder(result, binder);
    const intro = result.cues.cues.find(cue => cue.focusRelationIds.includes(binder.id))!;
    assert.equal(intro.role, 'witness');
    assert.deepEqual(intro.roles, ['negated', 'alternative', 'witness']);
    const alternative = graphRelations(result.document, 'graph-colorable')[0]!;
    const coloringId = port(binder, 'coloring');
    assert.ok(!result.document.scopes.find(scope => scope.id === alternative.scopeId)!.objectIds.includes(coloringId));
    const rightGuide = activeGuide(render(result.document, alternative.nodeId));
    assert.ok(rightGuide.includes('data-logic-role="negated"') && rightGuide.includes('data-logic-role="alternative"'));
    assert.ok(!rightGuide.includes(`data-reading-object="${coloringId}"`), 'A sibling existential witness leaked into the other branch');
  } },
  { name: 'same-identity adjacency uses one source vertex and preserves negation', source: '∀ (V : Type) (G : SimpleGraph V) (u : V), ¬ G.Adj u u', check: result => {
    const adjacency = graphRelations(result.document, 'graph-adjacency')[0]!;
    assert.equal(port(adjacency, 'left vertex'), port(adjacency, 'right vertex'));
    const rendered = activeGuide(render(result.document, adjacency.nodeId));
    assert.ok(rendered.includes('data-logic-role="negated"'));
    const graph = figure(rendered, adjacency);
    assert.equal((graph.match(/data-graph-endpoint=/g) ?? []).length, 1);
    assert.ok(graph.includes('same vertex occurs at both endpoints'));
  } },
  { name: 'a zero-color existence condition draws no vertex or color witnesses', source: '∀ (V : Type) (G : SimpleGraph V), G.Colorable 0', check: result => {
    const relation = graphRelations(result.document, 'graph-colorable')[0]!;
    const model = compileGraphConstraint(result.document, relation)!;
    assert.equal(model.palette!.count, '0');
    assert.equal(model.coloring, undefined);
    const rendered = figure(activeGuide(render(result.document, relation.nodeId)), relation);
    assert.ok(rendered.includes('Empty vertex type required') && rendered.includes('edge rule is vacuous'));
    assert.ok(!rendered.includes('data-graph-endpoint=') && !rendered.includes('data-palette-label='));
  } },
  { name: 'finite palettes are allowed labels and templates are never semantic vertex identities', source: '∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 4)), True', check: result => {
    const relation = graphRelations(result.document, 'graph-coloring')[0]!;
    assertBinder(result, relation);
    const rendered = figure(activeGuide(render(result.document, relation.nodeId)), relation);
    assert.equal((rendered.match(/data-palette-label=/g) ?? []).length, 4);
    assert.equal((rendered.match(/data-endpoint-role="arbitrary-slot"/g) ?? []).length, 2);
    assert.ok(rendered.includes('do not instantiate vertices') && rendered.includes('not colors assigned to the displayed endpoint slots'));
    assert.ok(!rendered.includes('data-reading-object="slot:'));
  } },
  { name: 'an unknown proposition wrapper stays above its contained coloring condition', source: '∀ (V : Type) (G : SimpleGraph V) (F : Prop → Prop), F (G.Colorable 4)', check: result => {
    const relation = graphRelations(result.document, 'graph-colorable')[0]!;
    const panel = result.reading.panels.find(panel => panel.nodeId === relation.nodeId)!;
    const root = result.document.relations.find(candidate => candidate.id === panel.rootRelationIds[0])!;
    assert.equal(root.kind, 'predicate');
    assert.equal(root.label, 'F');
    assert.notEqual(root.id, relation.id);
    const stages = result.cues.cues.filter(cue => cue.nodeId === relation.nodeId);
    assert.equal(stages[0]!.stage.kind, 'clause');
    const contained = stages.find(cue => cue.stage.relationId === relation.id)!;
    assert.equal(contained.stage.kind, 'contained');
    assert.ok(contained.detail.includes('not a separate assertion'));
    const rendered = activeGuide(render(result.document, relation.nodeId));
    assert.ok(rendered.includes('Inside this expression') && rendered.includes('not separate assertions'));
    assert.ok(rendered.indexOf('Inside this expression') < rendered.indexOf(`data-graph-relation="${relation.id}"`));
  } },
];

let passed = 0, failed = 0;
try {
  ({ StatementReadingView } = await ssr.ssrLoadModule('/src/visual/StatementReadingView.tsx'));
  for (const test of cases) {
    try { const result = await compile(test.source); test.check(result); passed++; console.log(`PASS ${test.name}`); }
    catch (error) { failed++; console.error(`FAIL ${test.name}: ${error instanceof Error ? error.message : String(error)}`); }
  }
  console.log(`${passed}/${cases.length} native Lean → graph semantics → guided reader SSR checks passed.`);
  process.exitCode = failed ? 1 : 0;
} finally { backend.close?.(); await ssr.close(); }
