import type { ReactElement, ReactNode } from 'react';
import type { RoleChain, RoleEdge, RolePosition } from '../reading/roles';
import './role-marks.css';

/** One mark per logical role, the same in every view. The left rail answers one question, where the clause stands:
 * no rail is required, solid is governed, double is assumed, dashed is denied, dotted is neither asserted nor denied
 * on its own. The glyph and word say which connective. No mark uses hue. role-marks.css draws `rail`. */
export const ROLE_MARKS: Record<RoleEdge, { readonly glyph: string; readonly word: (index: number) => string; readonly rail: 'solid' | 'double' | 'dashed' | 'dotted' }> = {
  assumption: { glyph: '', word: () => 'Given', rail: 'double' },
  conclusion: { glyph: '', word: () => 'Then', rail: 'solid' },
  negated: { glyph: '¬', word: () => 'Not', rail: 'dashed' },
  alternative: { glyph: '∨', word: index => `Alternative ${index + 1}`, rail: 'dotted' },
  side: { glyph: '↔', word: index => `Side ${index + 1}`, rail: 'dotted' },
  part: { glyph: '⋯', word: index => `Part ${index + 1}`, rail: 'dotted' },
};
/** The label a frame prints: its glyph, then its word. */
export function roleLabel(position: Pick<RolePosition, 'edge' | 'index'>): string {
  const mark = ROLE_MARKS[position.edge];
  return mark.glyph ? `${mark.glyph} ${mark.word(position.index)}` : mark.word(position.index);
}
/** Lean's mark for what is to be proved. A clause the statement requires carries it on its figure. */
export const REQUIRED_MARK = '⊢';

/** What the figure inside the frames shows: a whole clause, a part of one, a binder's introduction, or a law. */
export type RoleLeafKind = 'clause' | 'part' | 'binder' | 'law';

/** One frame per role edge: a rail and its label, nested like the skeleton's frames. */
export function RoleFrame({ position, children }: { position: RolePosition; children: ReactNode }): ReactElement {
  return <div className="role-frame" data-role-frame="" data-role={position.edge} data-role-index={position.index}>
    <span className="role-label" data-role-label="">{roleLabel(position)}</span>
    {children}
  </div>;
}

/** The innermost element around a figure. It prints at most one glyph: ⊢ when the statement requires the clause, or
 * a binder's own mark (∀, ∃) on its introduction. A part of a clause and a law print none, since the step's own
 * sentence ("Constructing part of …", "Under these hypotheses …") already says what they are, and a word printed under
 * a frame's label would read as one phrase with it ("¬ Not inside the clause"). The leaf's kind stays in
 * data-role-leaf for the readback. */
export function RoleLeaf({ leaf, required, nodeId, mark, children }: { leaf: RoleLeafKind; required: boolean; nodeId: string; mark?: string; children: ReactNode }): ReactElement {
  const printed = required ? REQUIRED_MARK : leaf === 'binder' ? mark : undefined;
  return <div className="role-leaf" data-role-leaf={leaf} data-role-node={nodeId}>
    {printed && <span className={`role-mark${required ? ' role-required' : ''}`} data-role-mark="" {...required ? { role: 'img', 'aria-label': 'Required' } : {}}>{printed}</span>}
    <div className="role-figure">{children}</div>
  </div>;
}

/** The leaf inside one frame per position of the chain, outermost first. */
export function framed(chain: RoleChain, leaf: ReactElement): ReactElement {
  return chain.reduceRight<ReactElement>((inner, position) => <RoleFrame position={position}>{inner}</RoleFrame>, leaf);
}
