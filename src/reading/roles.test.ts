import { describe, expect, it } from 'vitest';
import type { ReadingDocument, ReadingNode } from './types';
import { planReadingPresentation } from './presentation';
import { isRequired, roleChains, type RoleChain } from './roles';

const node = (id: string, kind: ReadingNode['kind'], children: ReadingNode[] = []): ReadingNode => ({ id, kind, phrase: id, lean: id, children, scopeId: id, context: [], assumptionNodeIds: [], relationIds: [], objectIds: [], ...(['forall', 'exists'].includes(kind) ? { binder: { binderId: id, name: id, type: 'X', role: kind === 'exists' ? 'existential' as const : 'universal' as const, dependsOn: [], scopeId: id } } : {}) });
const clause = (id: string) => node(id, 'predicate');
const chains = (root: ReadingNode, boundaryNodeIds: string[] = []) => {
  const presentation = planReadingPresentation({ root } as ReadingDocument, { boundaryNodeIds });
  const all = roleChains(presentation.root);
  return (id: string) => all.get(presentation.nodeToRegionId[id]!)!.map(position => `${position.edge} ${position.index} ${position.regionId}`);
};

describe('role chains', () => {
  it('follow the region tree, so a curried hypothesis is the second Given of one chain, not a Given inside a Then', () => {
    // A ⊆ B → x ∈ A → x ∈ B, the shape of the sets example.
    const of = chains(node('all-A', 'forall', [node('if', 'implies', [clause('inclusion'), node('then', 'implies', [clause('member-A'), clause('member-B')])])]));
    expect(of('all-A')).toEqual([]);
    expect(of('inclusion')).toEqual(['assumption 0 if']);
    expect(of('member-A')).toEqual(['assumption 1 if']);
    expect(of('member-B')).toEqual(['conclusion 0 if']);
    // The implication itself, and its second node, stand where the binder body stands.
    expect(of('if')).toEqual([]);
    expect(of('then')).toEqual([]);
  });

  it('let a conjunct stand where its conjunction stands, under a negation', () => {
    // ¬ (x ∈ e.source ∧ e.symm (e x) ≠ x), the shape of the restricted-alternative example.
    const of = chains(node('for-x', 'forall', [node('not', 'not', [node('both', 'and', [clause('region'), clause('round-trip')])])]));
    expect(of('region')).toEqual(['negated 0 not']);
    expect(of('round-trip')).toEqual(['negated 0 not']);
    expect(of('both')).toEqual(['negated 0 not']);
    expect(of('not')).toEqual([]);
  });

  it('name each alternative and each side of an equivalence by its index, an alternative inside a side included', () => {
    const of = chains(node('same', 'iff', [node('either', 'or', [clause('p'), clause('q')]), node('no', 'not', [clause('r')])]));
    expect(of('p')).toEqual(['side 0 same', 'alternative 0 either']);
    expect(of('q')).toEqual(['side 0 same', 'alternative 1 either']);
    expect(of('r')).toEqual(['side 1 same', 'negated 0 no']);
  });

  it('put a binder introduced under a hypothesis under that Given, and its body there too', () => {
    // (∀ x, R x x) → ∀ x, ∃ y, R x y, the shape of the relations example.
    const of = chains(node('if', 'implies', [node('all-x', 'forall', [clause('reflexive')]), node('all-x2', 'forall', [node('some-y', 'exists', [clause('related')])])]));
    expect(of('all-x')).toEqual(['assumption 0 if']);
    expect(of('reflexive')).toEqual(['assumption 0 if']);
    expect(of('all-x2')).toEqual(['conclusion 0 if']);
    expect(of('related')).toEqual(['conclusion 0 if']);
  });

  it('keep a nested premise as two Given positions and a conclusion inside a Given as Given then Then', () => {
    const of = chains(node('outer', 'implies', [node('inner', 'implies', [clause('p'), clause('q')]), clause('r')]));
    expect(of('p')).toEqual(['assumption 0 outer', 'assumption 0 inner']);
    expect(of('q')).toEqual(['assumption 0 outer', 'conclusion 0 inner']);
    expect(of('r')).toEqual(['conclusion 0 outer']);
  });

  it('stop a hypothesis chain at a selected component\'s root, as the presentation does', () => {
    const tree = node('context', 'implies', [clause('r'), node('selected', 'implies', [clause('p'), clause('q')])]);
    const bounded = chains(tree, ['selected']), whole = chains(tree);
    expect(bounded('p')).toEqual(['conclusion 0 context', 'assumption 0 selected']);
    expect(bounded('q')).toEqual(['conclusion 0 context', 'conclusion 0 selected']);
    expect(whole('p')).toEqual(['assumption 1 context']);
  });

  it('give each part of an unread structure its own index', () => {
    // A node with children and no connective of its own is an unread structure.
    const of = chains(node('structure', 'predicate', [clause('first'), clause('second')]));
    expect(of('first')).toEqual(['part 0 structure']);
    expect(of('second')).toEqual(['part 1 structure']);
  });

  it('call a clause required only in a statement and only under conclusions', () => {
    const at = (edges: string[]): RoleChain => edges.map((edge, index) => ({ edge: edge as RoleChain[number]['edge'], index: 0, regionId: `r${index}` }));
    expect(isRequired(at([]), 'statement')).toBe(true);
    expect(isRequired(at(['conclusion', 'conclusion']), 'statement')).toBe(true);
    for (const edge of ['assumption', 'negated', 'alternative', 'side', 'part']) expect(isRequired(at(['conclusion', edge]), 'statement'), edge).toBe(false);
    // Two negations are shown as two negations; the chain is not read as a polarity.
    expect(isRequired(at(['negated', 'negated']), 'statement')).toBe(false);
    expect(isRequired(at([]), 'expression')).toBe(false);
    expect(isRequired(at([]), 'law')).toBe(false);
    expect(isRequired(at([]), 'premise')).toBe(false);
  });
});
