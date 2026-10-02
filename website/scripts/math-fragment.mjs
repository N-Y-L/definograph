// A deliberately narrow HTML profile for the Product's MathLabel component and
// strict KaTeX output. It does not grant arbitrary foreignObject/HTML permission.
import { hasClass } from './html.mjs';
const XHTML = 'http://www.w3.org/1999/xhtml';
const MATHML = 'http://www.w3.org/1998/Math/MathML';
const SVG = 'http://www.w3.org/2000/svg';
const MATH_TAGS = new Set('math semantics annotation mrow mi mo mn mtext mspace msup msub msubsup mfrac msqrt mroot mover munder munderover mtable mtr mtd menclose mstyle mpadded mphantom'.split(' '));
const MATH_ATTRS = new Set('class xmlns display encoding mathvariant mathsize mathcolor mathbackground stretchy symmetric fence separator lspace rspace minsize maxsize accent accentunder movablelimits columnalign rowalign columnspacing rowspacing columnlines rowlines equalrows equalcolumns scriptlevel displaystyle width height depth voffset lspace notation linethickness bevelled'.split(' '));
const SVG_ATTRS = new Set('class xmlns width height viewbox preserveaspectratio d fill stroke stroke-width x y x1 x2 y1 y2'.split(' '));
const plain = value => typeof value === 'string' && value.trim().length > 0;
export function validateMathFragment(doc, text, { enabled = false } = {}) {
  const errors = [];
  const foreignObjects = new Set();
  const exempt = [];
  const children = node => doc.elements.filter(element => element.parent === node);
  const descendants = node => doc.elements.filter(element => element.ancestors.includes(node));
  const fail = (node, message) => errors.push(`math profile <${node.name}> on line ${node.line}: ${message}`);
  const attrs = (node, allowed) => {
    for (const name of node.attrs.keys()) if (!allowed.has(name)) fail(node, `unexpected attribute ${name}`);
  };
  // HTML children of SVG foreignObject are HTML integration points: unlike SVG,
  // a slash on a span/div does not close it in the browser. Reject that spelling.
  for (const node of doc.elements) if (['span', 'div'].includes(node.name) && node.ancestors.some(a => a.name === 'foreignobject') && /\/\s*>$/.test(text.slice(node.start, node.innerStart))) fail(node, 'HTML math elements require explicit end tags');
  const mathRoots = doc.elements.filter(node => hasClass(node, 'katex'));
  if (!enabled) {
    if (doc.elements.some(node => hasClass(node, 'rm-law-math') && !node.attrs.has('data-math-fallback'))) errors.push('inline law math requires verified math assets');
    return { errors, foreignObjects, directiveText: text };
  }
  const validKatex = new Set();
  for (const root of mathRoots) {
    const before = errors.length;
    const kids = children(root);
    if (root.name !== 'span' || kids.length !== 2 || !hasClass(kids[0], 'katex-mathml') || !hasClass(kids[1], 'katex-html')) fail(root, 'needs the actual KaTeX MathML and visual branches');
    attrs(root, new Set(['class']));
    const [accessible, visual] = kids;
    if (!accessible || !visual) continue;
    if (accessible.name !== 'span' || accessible.attrs.has('aria-hidden')) fail(accessible, 'MathML must remain accessible');
    if (visual.name !== 'span' || visual.attrs.get('aria-hidden') !== 'true') fail(visual, 'visual HTML must have aria-hidden="true"');
    attrs(accessible, new Set(['class']));
    attrs(visual, new Set(['class', 'aria-hidden']));
    const math = children(accessible);
    if (math.length !== 1 || math[0].name !== 'math' || math[0].attrs.get('xmlns') !== MATHML) fail(accessible, 'needs one MathML root with its namespace');
    const annotations = descendants(accessible).filter(node => node.name === 'annotation');
    if (annotations.length !== 1 || annotations[0].attrs.get('encoding') !== 'application/x-tex' || !plain(doc.text(annotations[0])) || children(annotations[0]).length) fail(accessible, 'needs one plain source TeX annotation');
    for (const node of descendants(accessible)) {
      if (!MATH_TAGS.has(node.name)) fail(node, 'not an approved MathML element');
      attrs(node, MATH_ATTRS);
      if (node.attrs.has('xmlns') && (node.name !== 'math' || node.attrs.get('xmlns') !== MATHML)) fail(node, 'unexpected MathML namespace boundary');
      if (node.attrs.has('encoding') && (node.name !== 'annotation' || node.attrs.get('encoding') !== 'application/x-tex')) fail(node, 'unexpected annotation encoding');
      if (node.attrs.has('class') && !/^(?:dg-s-[a-z0-9]+\s*)+$/.test(node.attrs.get('class'))) fail(node, 'unexpected MathML class');
    }
    for (const node of descendants(visual)) {
      if (node.name === 'span') {
        if (node.ancestors.some(a => a.name === 'svg' && a.ancestors.includes(visual))) fail(node, 'HTML cannot switch namespace inside a math SVG');
        attrs(node, new Set(['class', 'aria-hidden']));
      } else if (['svg', 'path', 'line'].includes(node.name)) {
        attrs(node, SVG_ATTRS);
        if (node.attrs.has('xmlns') && (node.name !== 'svg' || node.attrs.get('xmlns') !== SVG)) fail(node, 'unexpected SVG namespace');
        if (node.name !== 'svg' && !node.ancestors.some(a => a.name === 'svg' && a.ancestors.includes(visual))) fail(node, 'math path needs an inner SVG');
      } else fail(node, 'not an approved KaTeX visual element');
    }
    if (errors.length === before) {
      validKatex.add(root);
      for (const annotation of annotations) exempt.push([annotation.innerStart, annotation.innerEnd]);
    }
  }
  // Product's inline round-trip labels share the strict KaTeX validator, but
  // have no SVG measurement scaffold or cache key. Do not invent either.
  for (const host of doc.elements.filter(node => hasClass(node, 'rm-law-math'))) {
    const source = host.attrs.get('data-math-source'), content = children(host);
    attrs(host, new Set(['class', 'data-math-source', 'aria-label', 'data-math-fallback']));
    if (host.name !== 'span' || !plain(source) || host.ancestors.some(node => node.name === 'svg')) fail(host, 'requires an inline source-labelled span');
    if (host.attrs.has('data-math-fallback')) {
      if (host.attrs.get('data-math-fallback') !== 'source' || content.length || doc.text(host) !== source || host.attrs.has('aria-label')) fail(host, 'source fallback must retain only its exact plain source');
    } else {
      if (host.attrs.get('aria-label') !== source) fail(host, 'inline source and accessible label must agree');
      if (content.length !== 1 || !validKatex.has(content[0])) fail(host, 'inline law requires one validated strict KaTeX root');
    }
  }
  for (const fo of doc.elements.filter(node => node.name === 'foreignobject')) {
    const before = errors.length;
    const group = fo.parent;
    if (!group || group.name !== 'g' || !hasClass(group, 'diagram-math-label') || !group.ancestors.some(a => a.name === 'svg') || group.ancestors.some(a => a.name === 'foreignobject')) {
      fail(fo, 'foreignObject requires the Product MathLabel group'); continue;
    }
    const source = group.attrs.get('data-diagram-source');
    const groupChildren = children(group);
    const title = groupChildren.find(node => node.name === 'title');
    if (groupChildren.length !== 2 || !title || children(title).length || doc.text(title) !== source || group.attrs.get('aria-label') !== source || !plain(source)) fail(group, 'source, title and accessible label must agree');
    if (group.attrs.get('role') !== 'group' || !plain(group.attrs.get('data-diagram-label')) || !plain(group.attrs.get('data-math-label'))) fail(group, 'missing Product label metadata');
    if (!Number.isFinite(Number(group.attrs.get('data-math-baseline-y'))) || !group.attrs.has('data-math-baseline-y')) fail(group, 'invalid baseline');
    attrs(group, new Set(['class', 'data-diagram-label', 'data-diagram-source', 'data-math-label', 'data-math-baseline-y', 'role', 'aria-label']));
    attrs(fo, new Set(['x', 'y', 'width', 'height', 'overflow']));
    for (const field of ['x', 'y', 'width', 'height']) {
      const value = fo.attrs.get(field);
      if (!plain(value) || !Number.isFinite(Number(value)) || (['width', 'height'].includes(field) && Number(value) <= 0)) fail(fo, `invalid ${field}`);
    }
    if (fo.attrs.get('overflow') !== 'visible') fail(fo, 'requires the Product overflow policy');
    const content = children(fo);
    const host = content[0];
    if (content.length !== 1 || !host || host.name !== 'div' || !hasClass(host, 'diagram-math-content') || host.attrs.get('xmlns') !== XHTML) { fail(fo, 'requires one XHTML diagram-math-content host'); continue; }
    attrs(host, new Set(['class', 'xmlns']));
    const measurements = children(host);
    const measure = measurements[0];
    if (measurements.length !== 1 || !measure || measure.name !== 'span' || !hasClass(measure, 'diagram-math-measure') || measure.attrs.get('data-math-measure') !== '') { fail(host, 'requires the measured label span'); continue; }
    attrs(measure, new Set(['class', 'data-math-measure']));
    const pieces = children(measure);
    const typesets = pieces.filter(node => hasClass(node, 'diagram-math-typeset'));
    const baseline = pieces.at(-1);
    if (typesets.length !== 1 || !baseline || !hasClass(baseline, 'diagram-math-baseline') || baseline.attrs.get('data-math-baseline') !== '' || children(baseline).length || doc.text(baseline)) fail(measure, 'requires one typeset span and final empty baseline marker');
    for (const piece of pieces) {
      if (piece.name !== 'span') fail(piece, 'label pieces must be spans');
      if (piece === baseline) attrs(piece, new Set(['class', 'data-math-baseline']));
      else if (hasClass(piece, 'diagram-math-typeset')) {
        attrs(piece, new Set(['class']));
        const typeset = children(piece);
        if (typeset.length !== 1 || !validKatex.has(typeset[0])) fail(piece, 'requires one validated strict KaTeX root');
        else {
          const annotation = descendants(typeset[0]).find(node => node.name === 'annotation');
          const index = pieces.indexOf(piece);
          const prefix = index === 1 && hasClass(pieces[0], 'diagram-math-prose') ? doc.text(pieces[0]) : '';
          const suffix = index === pieces.length - 3 && hasClass(pieces[index + 1], 'diagram-math-prose') ? doc.text(pieces[index + 1]) : '';
          const expectedOrder = [...(prefix ? [pieces[0]] : []), piece, ...(suffix ? [pieces[index + 1]] : []), baseline];
          if (expectedOrder.length !== pieces.length || expectedOrder.some((node, at) => node !== pieces[at])) fail(measure, 'prose must surround the typeset span in Product order');
          const sourceFits = source?.startsWith(prefix) && source?.endsWith(suffix) && source.length >= prefix.length + suffix.length;
          const innerSource = sourceFits ? source.slice(prefix.length, suffix ? -suffix.length : undefined) : '';
          const baseKey = `${innerSource}\n${doc.text(annotation)}`;
          // withMathProse always inserts separators, including when its prose is empty.
          const expectedKeys = [`${prefix}\n${baseKey}\n${suffix}`, ...(!prefix && !suffix ? [baseKey] : [])];
          if (!sourceFits || !plain(innerSource) || !expectedKeys.includes(group.attrs.get('data-math-label'))) fail(group, 'measurement key must retain its source and TeX');
        }
      } else if (hasClass(piece, 'diagram-math-prose')) {
        attrs(piece, new Set(['class']));
        if (children(piece).length || !plain(doc.text(piece))) fail(piece, 'prose must remain plain text');
      } else fail(piece, 'unexpected label content');
    }
    if (pieces.length < 2 || pieces.length > 4 || (typesets.length === 1 && pieces.filter(p => p !== baseline && p !== typesets[0]).length > 2)) fail(measure, 'unexpected label piece count');
    if (errors.length === before) {
      foreignObjects.add(fo);
      // This key is a measurement cache key (source + TeX), not a checked Lean id.
      // Permit nested TeX braces only in this validated attribute, never directives.
      const startTag = text.slice(group.start, group.innerStart);
      const key = /\sdata-math-label=(?:"[^"]*"|'[^']*')/.exec(startTag);
      if (key) exempt.push([group.start + key.index, group.start + key.index + key[0].length]);
    }
  }
  let directiveText = text;
  for (const [from, to] of exempt) {
    if (/\{\{\s*[a-z][\w-]*\s*:/i.test(text.slice(from, to))) errors.push('math profile: site directive syntax is not allowed inside TeX');
    else directiveText = `${directiveText.slice(0, from)}${' '.repeat(to - from)}${directiveText.slice(to)}`;
  }
  return { errors, foreignObjects, directiveText };
}
