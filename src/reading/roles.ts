import { regionParts, type ReadingRegion, type RegionEdge } from './presentation';

/** The edges of the region tree that change where a clause stands. A binder body and a conjunct are transparent: a
 * region reached through one stands where its parent stands. */
export type RoleEdge = Exclude<RegionEdge, 'body' | 'conjunct'>;
/** One role edge on a path: its edge, its index among its parent's parts of that edge (the k-th hypothesis, the k-th
 * alternative), and the region that owns the edge. */
export interface RolePosition { readonly edge: RoleEdge; readonly index: number; readonly regionId: string }
/** The role edges on a region's path from the root of the region tree, outermost first. It is syntax, not a polarity:
 * nothing here decides that a double negation is positive or that the premise of a premise is positive. */
export type RoleChain = readonly RolePosition[];
/** What the root of a reading is. Only a statement asserts its conclusions: a fragment read in component mode does not
 * assert a theorem, a field law read inside a figure holds by the type that carries it, and a premise that a
 * construction retains is assumed by it. */
export type RootStanding = 'statement' | 'expression' | 'law' | 'premise';

/** The role chain of every region, by region ID. It follows the region tree the skeleton draws, so in a hypothesis
 * chain `P → Q → R` the clause `Q` is the second Given of one implication, as the skeleton draws it. */
export function roleChains(root: ReadingRegion): ReadonlyMap<string, RoleChain> {
  const chains = new Map<string, RoleChain>();
  const visit = (region: ReadingRegion, chain: RoleChain): void => {
    chains.set(region.id, chain);
    regionParts(region).forEach((part, position) => {
      if (part.edge === 'body' || part.edge === 'conjunct') visit(part.region, chain);
      // An implication lists its hypotheses before its one conclusion, so a hypothesis's position is its index.
      else visit(part.region, [...chain, { edge: part.edge, index: part.edge === 'conclusion' ? 0 : position, regionId: region.id }]);
    });
  };
  visit(root, []);
  return chains;
}

/** A clause is required when the reading's root is a statement and every role edge on its chain, if any, is a
 * conclusion. */
export const isRequired = (chain: RoleChain, root: RootStanding): boolean =>
  root === 'statement' && chain.every(position => position.edge === 'conclusion');
