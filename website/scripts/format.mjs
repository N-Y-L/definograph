// Shared text helpers for the build, the Markdown renderer and the checks.

const ESCAPES = { '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;' };
export function escapeHtml(text) {
  return String(text).replace(/[&<>"']/g, (ch) => ESCAPES[ch]);
}

// Light marking for Lean keywords, binders and `sorry`. It only wraps tokens in
// spans; the text itself is untouched (check.mjs compares it with the file).
const LEAN_TOKEN =
  /(?<![\p{L}\p{N}_.'])(?:example|theorem|lemma|def|structure|class|instance|where|fun|by|have|show|from|let|intro|exact|obtain|sorry)(?![\p{L}\p{N}_.'])|[∀∃]/gu;

export function renderLean(text) {
  let html = '';
  let last = 0;
  for (const match of text.matchAll(LEAN_TOKEN)) {
    const token = match[0];
    const kind = token === 'sorry' ? 'sorry' : token === '∀' || token === '∃' ? 'binder' : 'key';
    html += `${escapeHtml(text.slice(last, match.index))}<span class="tok-${kind}">${escapeHtml(token)}</span>`;
    last = match.index + token.length;
  }
  return html + escapeHtml(text.slice(last));
}

// Lines start..end (1-based, inclusive) of a file, each ending in a newline.
export function excerptLines(text, start, end) {
  const lines = text.endsWith('\n') ? text.slice(0, -1).split('\n') : text.split('\n');
  if (!(start >= 1 && end >= start && end <= lines.length)) return null;
  return `${lines.slice(start - 1, end).join('\n')}\n`;
}

// Which published Lean file a code block reproduces: the whole file, or an exact run of
// its lines. `files` maps file names to their text; the first match in map order wins,
// and a whole-file match is preferred. Returns { name, lines } or null.
export function findLeanSource(code, files) {
  for (const [name, text] of files) if (text === code) return { name, lines: null };
  const wanted = code.replace(/\n$/, '').split('\n');
  for (const [name, text] of files) {
    const lines = text.replace(/\n$/, '').split('\n');
    for (let i = 0; i + wanted.length <= lines.length; i += 1) {
      if (wanted.every((line, j) => lines[i + j] === line)) return { name, lines: `${i + 1}-${i + wanted.length}` };
    }
  }
  return null;
}

// An authored SVG must be inert: no scripts, styles, event handlers or references to other
// resources. Namespace declarations are the only URLs it may contain. Returns the problems
// found and the root element's width and height attributes.
export function inspectSvg(text) {
  const rules = [
    [/<script\b/i, 'a script element'],
    [/<style\b/i, 'a style element'],
    [/\sstyle\s*=/i, 'a style attribute'],
    [/\son[a-z]+\s*=/i, 'an event handler attribute'],
    [/<foreignObject\b/i, 'foreignObject content'],
    [/<(?:image|use|feImage|a|iframe|embed|object)\b/i, 'an element that references another resource'],
    [/\s(?:xlink:)?href\s*=/i, 'an href attribute'],
    [/url\s*\(|@import/i, 'a CSS resource reference'],
    [/<!DOCTYPE|<!ENTITY|<\?xml-stylesheet/i, 'a DTD, entity or stylesheet instruction'],
    [/javascript:|data:/i, 'a script or data URL'],
  ];
  const problems = rules.filter(([pattern]) => pattern.test(text)).map(([, label]) => label);
  if (/https?:\/\//i.test(text.replace(/\sxmlns(?::[\w-]+)?="[^"]*"/g, ''))) problems.push('a URL other than a namespace declaration');
  const root = /<svg\b[^>]*>/.exec(text)?.[0];
  if (!root) problems.push('no svg root element');
  const size = (name) => Number(new RegExp(`\\s${name}="(\\d+)"`).exec(root ?? '')?.[1] ?? 0);
  return { problems, width: size('width'), height: size('height') };
}
