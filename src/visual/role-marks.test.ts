import { readFileSync } from 'node:fs';
import { createElement } from 'react';
import { renderToStaticMarkup } from 'react-dom/server';
import { describe, expect, it } from 'vitest';
import type { Binder, Expr, StatementNode } from '../core';
import { compileStructuralObject } from '../decomposition/compiler';
import { scopedFixture } from '../reading/scoped-graph.test-fixtures';
import { compileSemanticDocument } from '../semantic';
import type { SemanticDocument } from '../semantic/types';
import { readFigureRoles, type FigureRole } from './role-readback';
import { assertEveryStepReadsBack, assertFigureRolesReadBack } from './role-marks.test-fixtures';
import { framed, RoleLeaf } from './role-marks';
import { StatementReadingView } from './StatementReadingView';
import type { SkeletonRow } from './skeleton-readback';
import { assertSkeletonReadsBack } from './statement-skeleton.test-fixtures';
import { compileReading } from '../reading';

const constant = (name: string): Expr => ({ kind: 'const', name });
const binder = (id: string, type = 'ℝ', role: Binder['role'] = 'universal'): Binder => ({ id, name: id, type, role, dependsOn: [] });
const variable = (b: Binder): Expr => ({ kind: 'var', id: b.id, name: b.name, type: b.type });
const app = (name: string, args: Expr[]): Expr => ({ kind: 'app', fn: constant(name), args, argumentKinds: args.map(() => 'value') });
const clause = (id: string, lean: string, expression: Expr = app('Unknown.condition', [constant(id)])): StatementNode => ({ id, kind: 'predicate', label: id, lean, expression, children: [] });
const node = (id: string, kind: StatementNode['kind'], children: StatementNode[], binding?: Binder): StatementNode => ({ id, kind, label: id, lean: `${id} source`, expression: constant('True'), children, binder: binding });
const semantic = (tree: StatementNode): SemanticDocument => compileSemanticDocument({ source: 'test', tree, expression: tree.expression });
const member = (id: string, set: Binder, element: Binder) => clause(id, `${element.name} ∈ ${set.name}`, app('Set.Mem', [variable(set), variable(element)]));
const labels = (figure: FigureRole) => figure.chain.map(frame => frame.label);
const limits = { maxFields: 16, maxFieldNodes: 120, maxDepth: 24 } as const;
/** A binder whose type is a reflected structure with one data field and one law about it, the law read as `lawId`. */
function lawful(owner: Binder, lawId: string): Binder {
  const field = (name: string, kind: 'data' | 'law', type: string, law?: StatementNode) => ({ name, projection: `Lawful.${name}`, expression: app(`Lawful.${name}`, [variable(owner)]), type, typeExpression: constant(type), typeDescriptor: { kind: kind === 'law' ? 'proposition' as const : 'unknown' as const, lean: type }, kind, dependsOn: [], ...law ? { law } : {} });
  const law = clause(lawId, `Bounded ${owner.name}.value`, app('Unknown.bounded', [app('Lawful.value', [variable(owner)])]));
  return { ...owner, structure: { name: 'Lawful', typeExpression: constant('Lawful'), omittedFields: 0, kernelChecked: true, limits, fields: [field('value', 'data', 'Hidden'), field('bounded', 'law', law.lean, law)] } };
}
/** The law's own reading of the structure `owner` carries, drawn alone as a law, and read back. */
function lawReadAlone(document: SemanticDocument, owner: string) {
  const object = document.objects.find(candidate => candidate.binder?.id === owner)!;
  const law = compileStructuralObject(document, object)!.fields.find(field => field.kind === 'law')!;
  const html = renderToStaticMarkup(createElement(StatementReadingView, { document: law.lawDocument!, reading: law.lawReading!, rootStanding: 'law' }));
  return assertFigureRolesReadBack(law.lawDocument!, law.lawReading!, html, { standing: 'law' });
}
/** The distinct leaves, as their reading would draw them alone. A law is drawn in the step and again in the closed full
 * reading, so the same leaf can occur more than once. */
const shapes = (figures: readonly FigureRole[]) => [...new Set(figures.map(figure => JSON.stringify({ nodeId: figure.nodeId, leaf: figure.leaf, mark: figure.mark, required: figure.required, chain: figure.chain, standing: figure.standing })))];
/** The leaf of the outer reading that each step draws, by the step's node. */
const stepsOf = (document: SemanticDocument) => {
  const steps = assertEveryStepReadsBack(document);
  return { steps, at: (nodeId: string) => steps.filter(step => step.cue.nodeId === nodeId && step.cue.stage.kind === 'clause').map(step => step.figures[0]!) };
};

/** The guided stage of a server-rendered view, as one element. */
function stage(html: string): string {
  const start = html.indexOf('<div class="rg-stage"');
  let depth = 0;
  for (const tag of html.slice(start).matchAll(/<(\/?)div\b[^>]*>/g)) {
    depth += tag[1] ? -1 : 1;
    if (!depth) return html.slice(start, start + tag.index! + tag[0].length);
  }
  throw new Error('The guided stage is not closed.');
}
/** The markup with every role frame and leaf taken away, their labels and marks with them; the figures stay. */
function withoutRoleMarks(html: string): string {
  // Each open element is kept, unwrapped (a frame or leaf: its tags go, its contents stay), or dropped with its contents.
  const open: ('keep' | 'unwrap' | 'drop' | 'inside')[] = [];
  let out = '', from = 0, dropping = 0;
  for (const tag of html.matchAll(/<(\/?)([a-zA-Z][\w-]*)((?:\s[^<>]*?)?)(\/?)>/g)) {
    if (!dropping) out += html.slice(from, tag.index);
    from = tag.index! + tag[0].length;
    const [, closing, , source = '', selfClosing] = tag;
    if (closing) {
      const kind = open.pop();
      if (kind === 'drop') dropping -= 1;
      if (kind === 'keep') out += tag[0];
    } else if (selfClosing) { if (!dropping) out += tag[0]; }
    else if (dropping) open.push('inside');
    else if (/data-role-(?:label|mark)=/.test(source)) { open.push('drop'); dropping += 1; }
    else if (/data-role-(?:frame|leaf)=|class="role-figure"/.test(source)) open.push('unwrap');
    else { open.push('keep'); out += tag[0]; }
  }
  return out + html.slice(from);
}

describe('role marks on the guided figure', () => {
  it('tells an assumed figure of a clause from a required one by its frames and mark alone', () => {
    // ∀ (A : Set ℝ) (x : ℝ), x ∈ A → x ∈ A: one clause, assumed and then required.
    const A = binder('A', 'Set ℝ'), x = binder('x');
    const document = semantic(node('all-A', 'forall', [node('all-x', 'forall', [node('if', 'implies', [member('clause-one', A, x), member('clause-two', A, x)])], x)], A));
    const { steps, at } = stepsOf(document);
    const [assumed] = at('clause-one'), [required] = at('clause-two');
    expect([labels(assumed!), assumed!.required]).toEqual([['Given'], false]);
    expect([labels(required!), required!.required, required!.mark]).toEqual([['Then'], true, '⊢']);
    // Take the role frames and the leaf away, and name the two clauses alike: the two figures are the same markup.
    const drawn = (id: string) => stage(steps.find(step => step.cue.nodeId === id && step.cue.stage.kind === 'clause')!.html);
    const plain = (id: string) => withoutRoleMarks(drawn(id)).replaceAll(id, 'clause-N');
    expect(plain('clause-one')).toContain('<figure class="sr-relation-figure sr-figure-membership">');
    expect(plain('clause-one')).toBe(plain('clause-two'));
    expect(drawn('clause-one').replaceAll('clause-one', 'clause-N')).not.toBe(drawn('clause-two').replaceAll('clause-two', 'clause-N'));
  });

  it('draws a figure under a negation inside a dashed Not frame and never marks it required', () => {
    // ∀ (A : Set ℝ) (x : ℝ), ¬ (x ∈ A ∧ P x), the shape of the restricted-alternative example.
    const A = binder('A', 'Set ℝ'), x = binder('x');
    const document = semantic(node('all-A', 'forall', [node('all-x', 'forall', [node('not', 'not', [node('both', 'and', [member('region', A, x), clause('round-trip', 'P x')])])], x)], A));
    const { steps } = stepsOf(document);
    const under = steps.filter(step => step.cue.sourceNodeIds.some(id => ['region', 'round-trip'].includes(id)));
    expect(under.length).toBeGreaterThanOrEqual(2);
    for (const { figures } of under) for (const figure of figures) {
      expect(figure.chain[0]).toMatchObject({ role: 'negated', label: '¬ Not' });
      expect(figure.required).toBe(false);
    }
    // The binders above the negation are introduced with their own mark and no frame.
    expect(steps[0]!.figures).toMatchObject([{ leaf: 'binder', mark: '∀', chain: [], required: false }]);
    expect(stage(under[0]!.html)).toContain('<div class="role-frame" data-role-frame="" data-role="negated" data-role-index="0"><span class="role-label" data-role-label="">¬ Not</span>');
  });

  it('frames a curried hypothesis as the skeleton draws it: the second Given of one chain', () => {
    // ∀ (A B : Set ℝ) (x : ℝ), A ⊆ B → x ∈ A → x ∈ B, the sets example.
    const A = binder('A', 'Set ℝ'), B = binder('B', 'Set ℝ'), x = binder('x');
    const tree = node('all-A', 'forall', [node('all-B', 'forall', [node('all-x', 'forall', [node('if', 'implies', [clause('inclusion', 'A ⊆ B', app('Set.Subset', [variable(A), variable(B)])), node('then', 'implies', [member('member-A', A, x), member('member-B', B, x)])])], x)], B)], A);
    const document = semantic(tree), { at } = stepsOf(document);
    expect(at('inclusion').map(labels)).toEqual([['Given']]);
    expect(at('member-A').map(labels)).toEqual([['Given']]);
    expect(at('member-B').map(figure => [labels(figure), figure.mark])).toEqual([[['Then'], '⊢']]);
    // The skeleton reads back to the same edges for each clause, transparent ones left out.
    const skeleton = assertSkeletonReadsBack(document, compileReading(document));
    const path = (row: SkeletonRow, id: string, chain: { role: string; index: number }[] = []): { role: string; index: number }[] | undefined => {
      if (row.nodeIds.includes(id)) return chain;
      for (const [position, child] of row.children.entries()) {
        const found = path(child.row, id, ['body', 'conjunct'].includes(child.edge) ? chain : [...chain, { role: child.edge, index: child.edge === 'conclusion' ? 0 : position }]);
        if (found) return found;
      }
    };
    for (const id of ['inclusion', 'member-A', 'member-B']) expect(at(id).map(figure => figure.chain.map(({ role, index }) => ({ role, index }))), id).toEqual([path(skeleton, id)]);
    expect(at('member-A')[0]!.chain).toEqual([{ role: 'assumption', index: 1, label: 'Given' }]);
  });

  it('puts ⊢ on a clause the statement requires through any number of conclusions, and on no part of a clause', () => {
    // ∀ c ε, 0 < ε → ∀ P, P ∈ S → Q P, the shape of the ε-ball example; and a clause standing alone.
    const S = binder('S', 'Set ℝ'), P = binder('P');
    const nested = semantic(node('all-c', 'forall', [node('positive', 'implies', [clause('ε-positive', '0 < ε'), node('all-P', 'forall', [node('inside', 'implies', [member('in-S', S, P), clause('near', 'Q P')])], P)])], binder('c')));
    const { at } = stepsOf(nested);
    expect(at('ε-positive').map(figure => [labels(figure), figure.required])).toEqual([[['Given'], false]]);
    expect(at('in-S').map(figure => [labels(figure), figure.required])).toEqual([[['Then', 'Given'], false]]);
    expect(at('near').map(figure => [labels(figure), figure.required])).toEqual([[['Then', 'Then'], true]]);
    expect(stepsOf(semantic(clause('alone', 'Q 0'))).at('alone').map(figure => [labels(figure), figure.mark])).toEqual([[[], '⊢']]);
    // A construction inside a required clause is a part of it, labelled so, and never required.
    const image = app('Set.image', [constant('f'), constant('T')]);
    const parts = assertEveryStepReadsBack(semantic(clause('member', 'x ∈ f \'\' T', app('Set.Mem', [image, constant('x')]))));
    expect(parts.map(({ cue, figures }) => [cue.stage.kind, figures[0]!.leaf, figures[0]!.mark])).toEqual([['construction', 'part', undefined], ['clause', 'clause', '⊢']]);
    // The step's own sentence says it is a part, quoting the clause in Lean; no word is printed under a frame label.
    expect(parts[0]!.html).toContain('<p class="rg-construction-context">Constructing part of <code title="x ∈ f &#x27;&#x27; T">x ∈ f &#x27;&#x27; T</code></p>');
  });

  it('reads back at every step through alternatives, equivalence sides, nested premises, structures and binders under a Given', () => {
    const t = binder('t', 'ℝ', 'existential');
    const tree = node('all-a', 'forall', [node('if', 'implies', [node('premise', 'implies', [clause('p', 'p'), clause('q', 'q')]), node('all-b', 'forall', [node('same', 'iff', [node('either', 'or', [node('no', 'not', [clause('r', 'r')]), node('some-t', 'exists', [clause('s', 's t')], t)]), { ...node('wrapped', 'predicate', [clause('u', 'u'), clause('v', 'v')]), lean: 'F u v' }])], binder('b'))])], binder('a'));
    const { at } = stepsOf(semantic(tree));
    expect(at('p').map(labels)).toEqual([['Given', 'Given']]);
    expect(at('q').map(labels)).toEqual([['Given', 'Then']]);
    expect(at('r').map(labels)).toEqual([['Then', '↔ Side 1', '∨ Alternative 1', '¬ Not']]);
    expect(at('s').map(labels)).toEqual([['Then', '↔ Side 1', '∨ Alternative 2']]);
    expect(at('u').map(labels)).toEqual([['Then', '↔ Side 2', '⋯ Part 1']]);
    expect(at('v').map(labels)).toEqual([['Then', '↔ Side 2', '⋯ Part 2']]);
    // The scoped-graph fixture: a witness, a conjunction and a hypothesis under binders.
    expect(assertEveryStepReadsBack(scopedFixture().document).length).toBeGreaterThan(5);
  });

  it('marks nothing as required in a selected expression, which does not assert a theorem', () => {
    const document = semantic(node('all-x', 'forall', [node('if', 'implies', [clause('p', 'p'), clause('q', 'q')])], binder('x')));
    const component = { ...document, presentation: { kind: 'component' as const, target: 'term' as const, logicalRootNodeId: 'all-x' } };
    const steps = assertEveryStepReadsBack(component);
    const figures = steps.flatMap(step => step.figures);
    expect(figures.length).toBeGreaterThan(0);
    expect(figures.every(figure => figure.standing === 'expression' && !figure.required)).toBe(true);
    expect(steps.find(step => step.cue.nodeId === 'q')!.figures.map(labels)).toEqual([['Then']]);
  });

  it('marks no law of a type as required: a field law read inside a figure starts its own chain as a law', () => {
    const r = lawful(binder('r', 'Lawful'), 'law-bounded');
    const document = semantic(node('all-r', 'forall', [clause('claim', 'claim r', app('Unknown.claim', [variable(r)]))], r));
    const steps = assertEveryStepReadsBack(document);
    const introduction = steps.find(step => step.cue.intent === 'introduce')!;
    expect(introduction.html).toContain('data-role-root="law"');
    const laws = introduction.html.slice(introduction.html.indexOf('data-role-root="law"'));
    expect(laws).toContain('data-role-leaf="clause"');
    expect(laws).not.toContain('data-role-mark="" role="img" aria-label="Required"');
    // The law nested in the figure reads back exactly as the law's own reading drawn alone, one reading deeper.
    const nested = readFigureRoles(introduction.html).filter(figure => figure.depth === 1);
    expect(nested.length).toBeGreaterThan(0);
    expect(shapes(nested)).toEqual(shapes(lawReadAlone(document, 'r')));
    // The statement's own claim is still required.
    expect(steps.find(step => step.cue.nodeId === 'claim')!.figures.map(figure => figure.mark)).toEqual(['⊢']);
  });

  it('frames the laws a hypothesis carries on the step of its implication, as a law and never as required', () => {
    // ∀ x, (h : Lawful) → claim x, where the hypothesis h carries a law: the implication's step draws that law.
    const h = lawful(binder('h', 'Lawful', 'assumption'), 'law-of-h');
    const document = semantic(node('all-x', 'forall', [node('if', 'implies', [clause('premise', 'Lawful', constant('Lawful')), clause('claim', 'claim x', app('Unknown.claim', [variable(binder('x'))]))], h)], binder('x')));
    const steps = assertEveryStepReadsBack(document);
    const logic = steps.find(step => step.cue.stage.kind === 'logic')!;
    expect(logic.figures).toEqual([{ nodeId: 'if', leaf: 'law', required: false, chain: [], standing: 'statement', depth: 0 }]);
    expect(logic.html).toContain('Under these hypotheses, the following laws are available in the conclusion.');
    // Its law is a reading of its own, one reading deeper, the same as the law drawn alone.
    const nested = readFigureRoles(logic.html).filter(figure => figure.depth === 1);
    expect(nested.length).toBeGreaterThan(0);
    expect(nested.every(figure => figure.standing === 'law' && !figure.required)).toBe(true);
    expect(shapes(nested)).toEqual(shapes(lawReadAlone(document, 'h')));
    // Under a negation the same step is framed by its chain.
    const denied = semantic(node('all-x', 'forall', [node('no', 'not', [node('if', 'implies', [clause('premise', 'Lawful', constant('Lawful')), clause('claim', 'claim x', app('Unknown.claim', [variable(binder('x'))]))], h)])], binder('x')));
    expect(assertEveryStepReadsBack(denied).find(step => step.cue.nodeId === 'if' && step.cue.stage.kind === 'logic')!.figures.map(labels)).toEqual([['¬ Not']]);
  });

  it('marks nothing as required in a premise that a construction retains', () => {
    const document = semantic(node('all-x', 'forall', [node('if', 'implies', [clause('p', 'p'), clause('q', 'q')])], binder('x')));
    const figures = assertEveryStepReadsBack(document, { rootStanding: 'premise' }).flatMap(step => step.figures);
    expect(figures.some(figure => figure.nodeId === 'q' && figure.leaf === 'clause')).toBe(true);
    expect(figures.every(figure => figure.standing === 'premise' && !figure.required && figure.mark !== '⊢')).toBe(true);
  });

  it('names the required mark for assistive technology and draws one frame per position of the chain', () => {
    const html = renderToStaticMarkup(framed([{ edge: 'conclusion', index: 0, regionId: 'if' }, { edge: 'negated', index: 0, regionId: 'no' }], createElement(RoleLeaf, { leaf: 'clause', required: true, nodeId: 'p', children: 'figure' })));
    expect(html).toBe('<div class="role-frame" data-role-frame="" data-role="conclusion" data-role-index="0"><span class="role-label" data-role-label="">Then</span>'
      + '<div class="role-frame" data-role-frame="" data-role="negated" data-role-index="0"><span class="role-label" data-role-label="">¬ Not</span>'
      + '<div class="role-leaf" data-role-leaf="clause" data-role-node="p"><span class="role-mark role-required" data-role-mark="" role="img" aria-label="Required">⊢</span><div class="role-figure">figure</div></div></div></div>');
  });
});

// The words of a figure describe its condition and never assert it: the frames around it say where it stands. This
// scan reads the text of the figure sources, comments removed. "required" is caught on its own, except in "not required"
// and in an identifier such as 'required-empty'; "required" and "must" are allowed with "for this condition to hold" or
// "by this condition", which tie them to the condition.
const source = (file: string) => readFileSync(new URL(file, import.meta.url), 'utf8').replace(/\/\*[\s\S]*?\*\/|\/\/[^\n]*/g, '');
const ASSERTING = /(?<!not )\brequired\b(?!-)| must |belongs to/;
function asserting(text: string): string[] {
  return text.split(/['"`<>]/).filter(segment => ASSERTING.test(segment) && !/for this condition to hold|by this condition/.test(segment)).map(segment => segment.trim());
}
describe('figure words', () => {
  it('describe the condition and never assert it', () => {
    const reading = source('./StatementReadingView.tsx');
    const figures = reading.slice(reading.indexOf('const MEMBERSHIP_CAPTION'), reading.indexOf('function FieldLawReading'));
    expect(figures.length).toBeGreaterThan(10_000);
    const files = [figures, source('../set-constructions/SetConstructionFigure.tsx'), source('../graphs/model.ts'), source('../graphs/GraphConstraintFigure.tsx')];
    expect(files.flatMap(asserting)).toEqual([]);
    // The scan finds the captions this replaced.
    expect(asserting("'Membership condition · the named element belongs to the region'; 'The displayed expressions are required to satisfy this relation'; 'At least one highlighted region must contain a distinguishing element; no witness is chosen.'; <strong>Empty vertex type required</strong>")).toHaveLength(4);
    expect(asserting("'required-empty'; 'injectivity is not required'; 'Membership regions required to be empty by this condition'")).toEqual([]);
    expect(asserting("'The hatched membership regions must be empty for this condition to hold.'")).toEqual([]);
  });
});
