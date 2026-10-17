import assert from 'node:assert/strict';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { compileReading } from '../reading/compiler';
import { compileReadingCues, type ReadingCue } from '../reading/cues';
import { planReadingPresentation, type ReadingRegion } from '../reading/presentation';
import type { RootStanding } from '../reading/roles';
import type { ReadingDocument } from '../reading/types';
import type { SemanticDocument } from '../semantic/types';
import { createReadingCueSelection } from './reading-cue-selection';
import { readFigureRoles, type FigureRole } from './role-readback';
import { regionEdges, renderReading } from './statement-skeleton.test-fixtures';
import { StatementReadingView } from './StatementReadingView';

/** What a framed figure must say, written here from the region tree alone and apart from the renderer: its own walk of
 * the edges, its own copy of the labels and marks, and its own rule for ⊢. A frame that printed "Given" on a negation,
 * or a leaf that printed ⊢ under a hypothesis, would otherwise read back as a well-formed chain. */
const LABELS: Record<string, (index: number) => string> = {
  assumption: () => 'Given', conclusion: () => 'Then', negated: () => '¬ Not',
  alternative: index => `∨ Alternative ${index + 1}`, side: index => `↔ Side ${index + 1}`, part: index => `⋯ Part ${index + 1}`,
};
const TRANSPARENT = new Set(['body', 'conjunct']);
const BINDER_MARKS: Record<string, string> = { universal: '∀', existential: '∃', parameter: '↦', lambda: '↦', assumption: '⇒', definition: ':=', auxiliary: '·' };
export type ExpectedChain = { role: string; index: number }[];

/** Each source node's region and that region's chain of role edges, outermost first. */
export function expectedRoles(document: SemanticDocument, reading: ReadingDocument) {
  const component = document.presentation?.kind === 'component' && document.presentation.targetNodeId;
  const root = planReadingPresentation(reading, { boundaryNodeIds: component ? [component] : [] }).root;
  const regions = new Map<string, { region: ReadingRegion; chain: ExpectedChain }>();
  const visit = (region: ReadingRegion, chain: ExpectedChain): void => {
    region.sourceNodeIds.forEach(id => regions.set(id, { region, chain }));
    regionEdges(region).forEach((child, position) => visit(child.region,
      TRANSPARENT.has(child.edge) ? chain : [...chain, { role: child.edge, index: child.edge === 'conclusion' ? 0 : position }]));
  };
  visit(root, []);
  return { standing: document.presentation?.kind === 'component' ? 'expression' : 'statement', of: (nodeId: string) => regions.get(nodeId) ?? assert.fail(`No region holds ${nodeId}.`) };
}
const required = (standing: string, leaf: string, chain: ExpectedChain) => standing === 'statement' && leaf === 'clause' && chain.every(position => position.role === 'conclusion');

/** The kind of leaf a step's figure is drawn in, from the step's stage alone and apart from CueFigure: a binder's
 * introduction, a whole clause, a part of one (a construction or a contained relation), or, on a connective, the laws
 * its hypotheses carry. A connective step inside a selected expression shows the expression. */
export function expectedLeaf(cue: ReadingCue): string {
  switch (cue.stage.kind) {
    case 'introduction': return 'binder';
    case 'construction': case 'contained': return 'part';
    case 'logic': return cue.intent === 'logic' ? 'law' : 'clause';
    default: return 'clause';
  }
}
/** The kinds of leaf each region can hold, for a leaf whose step is not known. */
const leavesOf = (region: ReadingRegion): readonly string[] => region.kind === 'binders' ? ['binder'] : region.kind === 'clause' ? ['clause', 'part'] : ['law', 'clause'];

/** What a caller knows beyond the markup: the step the guide shows, and the standing the view was given. */
export interface RoleExpectation { readonly cue?: ReadingCue; readonly standing?: RootStanding }

/** Require every leaf read back from the markup to stand where the region tree puts it: its chain, each frame's label,
 * its kind, its mark and whether it is marked required. Given the step the guide shows, the leaf's kind is the one that
 * step draws, so a whole clause drawn as a part or a law cannot hide its ⊢. A leaf of a field law read inside a figure
 * starts its own chain and is never required. */
export function assertFigureRoles(document: SemanticDocument, reading: ReadingDocument, figures: readonly FigureRole[], { cue, standing }: RoleExpectation = {}): void {
  const expected = expectedRoles(document, reading), rootStanding = standing ?? expected.standing;
  for (const figure of figures) {
    for (const frame of figure.chain) assert.equal(frame.label, LABELS[frame.role]?.(frame.index), `The ${frame.role} frame around ${figure.nodeId} prints the wrong label.`);
    if (figure.depth > 0) {
      assert.equal(figure.standing, 'law', `A reading nested in a figure of ${figure.nodeId} is not marked as a law.`);
      assert.equal(figure.required, false, `A law of a type is marked as required at ${figure.nodeId}.`);
      if (figure.leaf !== 'binder') assert.equal(figure.mark, undefined, `The figure of ${figure.nodeId} in a law prints a mark.`);
      continue;
    }
    assert.equal(figure.standing, rootStanding, 'The reading root carries the wrong standing.');
    const { region, chain } = expected.of(figure.nodeId);
    assert.deepEqual(figure.chain.map(({ role, index }) => ({ role, index })), chain, `The figure of ${figure.nodeId} is drawn under the wrong role frames.`);
    assert.ok(leavesOf(region).includes(figure.leaf), `The figure of ${figure.nodeId} is drawn as a ${figure.leaf}, which a ${region.kind} region does not hold.`);
    const leaf = cue ? expectedLeaf(cue) : figure.leaf;
    if (cue) {
      assert.ok(cue.sourceNodeIds.includes(figure.nodeId), `Step ${cue.id} draws a figure of another node, ${figure.nodeId}.`);
      assert.equal(figure.leaf, leaf, `Step ${cue.id} draws its figure as a ${figure.leaf}, not as a ${leaf}.`);
    }
    const isRequired = required(rootStanding, leaf, chain);
    assert.equal(figure.required, isRequired, `The figure of ${figure.nodeId} is ${isRequired ? 'not ' : ''}marked as required.`);
    const mark = isRequired ? '⊢' : leaf === 'binder' ? BINDER_MARKS[region.node.binder?.role ?? ''] : undefined;
    assert.equal(figure.mark, mark, `The figure of ${figure.nodeId} prints the wrong mark.`);
  }
}
/** Read the markup back and require it to agree with the region tree. Throws on a mismatch. */
export function assertFigureRolesReadBack(document: SemanticDocument, reading: ReadingDocument, html = renderReading(document, reading), expectation: RoleExpectation = {}): FigureRole[] {
  const figures = readFigureRoles(html);
  assertFigureRoles(document, reading, figures, expectation);
  return figures;
}

const attribute = (text: string): string => text.replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/"/g, '&quot;').replace(/'/g, '&#x27;');
/** The step the guide shows in this markup, found by the step ID on its stage, or undefined when no guide is drawn. A
 * reading nested in a figure has its own guide inside the outer stage, so the first stage is the outer one. */
export function shownStep(document: SemanticDocument, reading: ReadingDocument, html: string): ReadingCue | undefined {
  const stage = /<div class="rg-stage" data-role-surface="" data-cue-id="([^"]*)"/.exec(html);
  if (!stage) return undefined;
  return compileReadingCues(reading, document).cues.find(cue => attribute(cue.id) === stage[1]) ?? assert.fail(`The guide shows a step that is not in the plan: ${stage[1]}.`);
}
/** Read the markup back against the region tree and against the step its guide shows: each leaf is the kind of figure
 * that step draws, and a step that is not on a connective draws exactly one. Returns the step and every leaf. */
export function assertStageReadsBack(document: SemanticDocument, reading: ReadingDocument, html: string, expectation: Pick<RoleExpectation, 'standing'> = {}): { cue?: ReadingCue; figures: FigureRole[] } {
  const cue = shownStep(document, reading, html);
  const figures = assertFigureRolesReadBack(document, reading, html, { ...expectation, cue });
  const outer = figures.filter(figure => figure.depth === 0);
  if (!cue) assert.equal(outer.length, 0, 'A figure is framed although no step is shown.');
  else if (cue.stage.kind === 'logic') assert.ok(outer.length <= 1, `Step ${cue.id} draws ${outer.length} leaves.`);
  else assert.equal(outer.length, 1, `Step ${cue.id} draws ${outer.length} leaves.`);
  return { cue, figures };
}

/** Draw every step of the reading in turn, as the guide shows it, and require each step's figure to read back to the
 * region tree, to the kind of figure its step draws and to its cue's own chain. The server-rendered view draws only the
 * active step, so each is selected in turn: by its node, and by the cue itself. Returns each step with the leaves of
 * its own reading. */
export function assertEveryStepReadsBack(document: SemanticDocument, { rootStanding }: { rootStanding?: RootStanding } = {}): { cue: ReadingCue; html: string; figures: FigureRole[] }[] {
  const plan = compileReadingCues(compileReading(document), document);
  return plan.cues.map(cue => {
    const reading = compileReading(document, { selectedNodeId: cue.nodeId });
    const html = renderToStaticMarkup(createElement(StatementReadingView, { document, reading, rootStanding, selectedCue: createReadingCueSelection(document, cue), onObjectSelect: () => undefined, onNodeSelect: () => undefined }));
    const shown = assertStageReadsBack(document, reading, html, { standing: rootStanding });
    assert.equal(shown.cue?.id, cue.id, `The guide does not show step ${cue.id} when it is selected.`);
    const figures = shown.figures.filter(figure => figure.depth === 0);
    for (const figure of figures) assert.deepEqual(figure.chain.map(({ role, index }) => ({ role, index })), cue.roleChain.map(({ edge, index }) => ({ role: edge, index })), `Step ${cue.id} is not framed by its own chain.`);
    return { cue, html, figures };
  });
}
