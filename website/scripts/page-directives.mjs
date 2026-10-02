// Page-level directive scan. Exempt TeX only inside the exact validated recording
// that the build inserted, using the same narrow math profile as fragment import.
import { hasClass, parseHtml } from './html.mjs';
import { validateMathFragment } from './math-fragment.mjs';

export function checkPageDirectives(source, verifiedViews) {
  const doc = parseHtml(source), errors = [];
  let scanned = source;
  for (const root of doc.elements.filter(node => hasClass(node, 'dg-view'))) {
    const view = verifiedViews.get(root.attrs.get('data-view-id'));
    if (!view?.batch.mathAssets || !view.batch.mathFiles) continue;
    const fragment = source.slice(root.start, root.end);
    if (fragment !== view.fragmentText.replace(/\s+$/, '')) {
      errors.push('recorded math fragment differs from its validated source');
      continue;
    }
    const math = validateMathFragment(parseHtml(fragment), fragment, { enabled: true });
    if (math.errors.length) { errors.push(...math.errors); continue; }
    // The profile masks only validated TeX annotation text and measurement keys,
    // retaining the original length so all subsequent source offsets stay exact.
    scanned = scanned.slice(0, root.start) + math.directiveText + scanned.slice(root.end);
  }
  if (/\{\{|\}\}/.test(scanned.replace(/<pre[\s\S]*?<\/pre>/g, ''))) errors.push('unreplaced {{…}} placeholder');
  return errors;
}
