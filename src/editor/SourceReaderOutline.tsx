/** Passive section navigation inside one mounted continuation attempt.
 *
 * The outline links to the sections the attempt reader actually renders for its
 * selected capture and step: the step reading, ordered provenance, supply reading
 * and the attempt's recorded outcomes. It reads no record, derives no
 * mathematical content, posts no host message and changes no selection,
 * disclosure, URL or history. Each destination has a return link immediately
 * before its existing section; that link is the focus landing. Identifiers are
 * namespaced by the mounted reader instance, capture and selected step (or an
 * explicit no-step key), so two mounted readers or two prefixes never share a
 * target. Only a deliberate activation scrolls within the drawer and moves focus. */
import type { MouseEvent } from 'react';
import './source-reader-outline.css';

export type OutlineSection = 'step' | 'provenance' | 'supply' | 'outcomes';
/** Document order of the four potential destinations. */
export const OUTLINE_SECTIONS: readonly OutlineSection[] = Object.freeze(['step', 'provenance', 'supply', 'outcomes'] as const);

/** The attempt and selected step an outline names. `step` is null when the attempt recorded no step. */
export interface OutlineAttempt {
  current: boolean;
  attempt: number;
  step: { number: number; title: string } | null;
  /** Whether the attempt retains outcomes of steps after the selected one; its outcome list shows them. */
  outcomesAfterStep: boolean;
}

export const outlineWording = Object.freeze({
  navigation: 'Section navigation',
  sections: Object.freeze({ step: 'Step reading', provenance: 'Ordered provenance', supply: 'Supply reading', outcomes: 'Attempt outcomes' }) as Readonly<Record<OutlineSection, string>>,
  identity(attempt: OutlineAttempt): string {
    return `${attempt.current ? 'Current' : 'Earlier'} continuation · attempt ${attempt.attempt} · ${attempt.step ? `step ${attempt.step.number} · ${attempt.step.title}` : 'no recorded step'}`;
  },
  returnLabel(attempt: OutlineAttempt): string {
    return `${attempt.current ? 'Current' : 'Earlier'} continuation · attempt ${attempt.attempt} · ${attempt.step ? `step ${attempt.step.number}` : 'no recorded step'} · section navigation`;
  },
  /** The outcome list is the whole attempt, never the selected prefix alone. */
  outcomesScope(attempt: OutlineAttempt): string {
    if (!attempt.step) return `All recorded outcomes of attempt ${attempt.attempt}.`;
    return attempt.outcomesAfterStep
      ? `All recorded outcomes of attempt ${attempt.attempt}, including outcomes of steps after step ${attempt.step.number}, which are outside the selected prefix.`
      : `All recorded outcomes of attempt ${attempt.attempt}, not only those of step ${attempt.step.number}.`;
  },
});

/** One namespace per mounted reader instance, capture and selected step; never a bare step or occurrence number. */
export function outlineNamespace(instance: string, captureId: string, stepIndex: number | null): string {
  return `${instance}-outline-${captureId}-${stepIndex === null ? 'no-step' : `step-${stepIndex}`}`;
}
export function outlineIds(namespace: string) {
  return { title: `${namespace}-title`, link: (section: OutlineSection) => `${namespace}-link-${section}`, landing: (section: OutlineSection) => `${namespace}-to-${section}` };
}
/** Destinations in document order, each present only when its existing section is rendered. */
export function outlineDestinations(rendered: Readonly<Record<OutlineSection, boolean>>): OutlineSection[] {
  return OUTLINE_SECTIONS.filter(section => rendered[section]);
}

const GAP = 12;
/** Scrolls the drawer so `start` sits just below its sticky heading, keeps `target` inside the
 * visible drawer, then moves focus to `target`. Outside a drawer the browser scrolls. */
function reveal(start: HTMLElement, target: HTMLElement): void {
  const drawer = start.closest<HTMLElement>('.atlas-drawer');
  if (drawer) {
    const heading = drawer.querySelector<HTMLElement>('.drawer-heading'), top = drawer.getBoundingClientRect().top + drawer.clientTop;
    drawer.scrollTop = Math.max(0, start.getBoundingClientRect().top - top + drawer.scrollTop - (heading?.offsetHeight ?? 0) - GAP);
    const hidden = target.getBoundingClientRect().bottom - (top + drawer.clientHeight - GAP);
    if (hidden > 0) drawer.scrollTop += hidden;
  } else start.scrollIntoView({ block: 'start' });
  target.focus({ preventScroll: true });
}
/** Follows a link only to its own namespace's element; the URL and history stay unchanged. */
function follow(event: MouseEvent<HTMLAnchorElement>, namespace: string, targetId: string): void {
  event.preventDefault();
  const target = event.currentTarget.ownerDocument.getElementById(targetId), owner = target?.closest<HTMLElement>('[data-reader-outline]');
  if (target && owner && owner.dataset.readerOutline === namespace) reveal(owner, target);
}

/** The outline itself; omitted when no destination is rendered. */
export function SourceReaderOutline({ namespace, attempt, sections }: { namespace: string; attempt: OutlineAttempt; sections: readonly OutlineSection[] }) {
  if (!sections.length) return null;
  const ids = outlineIds(namespace);
  return <nav className="reader-outline" aria-labelledby={ids.title} data-reader-outline={namespace}>
    <p className="reader-outline-title" id={ids.title}><strong>{outlineWording.navigation}</strong> · {outlineWording.identity(attempt)}</p>
    <ul>{sections.map(section => <li key={section}>
      <a id={ids.link(section)} href={`#${ids.landing(section)}`} data-reader-outline-link={section}
        onClick={event => follow(event, namespace, ids.landing(section))}>{outlineWording.sections[section]}</a>
    </li>)}</ul>
  </nav>;
}

/** The return link placed immediately before an existing section; it is that destination's focus landing.
 * The outcomes landing also states that the list is the whole attempt; it stays outside that list's disclosure. */
export function OutlineLanding({ namespace, attempt, section }: { namespace: string; attempt: OutlineAttempt; section: OutlineSection }) {
  const ids = outlineIds(namespace);
  return <div className="reader-outline-landing" data-reader-outline={namespace} data-reader-outline-landing={section}>
    <a id={ids.landing(section)} href={`#${ids.link(section)}`} onClick={event => follow(event, namespace, ids.link(section))}>{outlineWording.returnLabel(attempt)}</a>
    {section === 'outcomes' && <p data-reader-outline-scope="">{outlineWording.outcomesScope(attempt)}</p>}
  </div>;
}
