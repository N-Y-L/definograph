// A small reader for this site's own HTML: enough to check well-formedness, ids,
// links and a few content-model rules without third-party parsers. It expects an
// explicit end tag for every non-void element, which the site's markup follows.

export const VOID_ELEMENTS = new Set([
  'area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'source', 'track', 'wbr',
]);
const RAW_TEXT = new Set(['script', 'style', 'title', 'textarea']);
// Start tags that make a browser close an open <p>, silently changing the structure.
const CLOSES_P = new Set([
  'address', 'article', 'aside', 'blockquote', 'details', 'dialog', 'div', 'dl', 'fieldset', 'figcaption',
  'figure', 'footer', 'form', 'h1', 'h2', 'h3', 'h4', 'h5', 'h6', 'header', 'hgroup', 'hr', 'main', 'menu',
  'nav', 'ol', 'p', 'pre', 'search', 'section', 'table', 'ul',
]);
const REQUIRED_PARENT = {
  li: ['ul', 'ol', 'menu'],
  dt: ['dl', 'div'],
  dd: ['dl', 'div'],
  thead: ['table'],
  tbody: ['table'],
  tfoot: ['table'],
  caption: ['table'],
  tr: ['table', 'thead', 'tbody', 'tfoot'],
  th: ['tr'],
  td: ['tr'],
  figcaption: ['figure'],
  summary: ['details'],
};
const NAMED_ENTITIES = { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'", nbsp: ' ' };
const REFERENCE = /^&(#[xX][0-9a-fA-F]+|#[0-9]+|[a-zA-Z][a-zA-Z0-9]*);/;

export function decodeEntities(text) {
  return text.replace(/&(#[xX][0-9a-fA-F]+|#[0-9]+|[a-zA-Z][a-zA-Z0-9]*);/g, (match, body) => {
    if (body[0] === '#') {
      const hex = body[1] === 'x' || body[1] === 'X';
      return String.fromCodePoint(parseInt(body.slice(hex ? 2 : 1), hex ? 16 : 10));
    }
    return Object.hasOwn(NAMED_ENTITIES, body) ? NAMED_ENTITIES[body] : match;
  });
}

export function textContent(html) {
  return decodeEntities(html.replace(/<!--[\s\S]*?-->/g, '').replace(/<[^>]*>/g, ''));
}

export function hasClass(element, name) {
  return (element.attrs.get('class') ?? '').split(/\s+/).includes(name);
}

const TAG = /<(\/?)([a-zA-Z][a-zA-Z0-9-]*)((?:\s+[^\s"'<>/=]+(?:\s*=\s*(?:"[^"]*"|'[^']*'|[^\s"'=<>`]+))?)*)\s*(\/?)>/y;
const ATTRIBUTE = /\s+([^\s"'<>/=]+)(?:\s*=\s*(?:"([^"]*)"|'([^']*)'|([^\s"'=<>`]+)))?/y;

function checkReferences(text, report) {
  for (const match of text.matchAll(/&/g)) {
    const reference = REFERENCE.exec(text.slice(match.index));
    if (!reference) report(match.index, 'bare "&" (write &amp;)');
    else if (!reference[1].startsWith('#') && !Object.hasOwn(NAMED_ENTITIES, reference[1])) {
      report(match.index, `unknown entity &${reference[1]};`);
    }
  }
}

function parseAttributes(text, report) {
  const attrs = new Map();
  ATTRIBUTE.lastIndex = 0;
  while (ATTRIBUTE.lastIndex < text.length) {
    const start = ATTRIBUTE.lastIndex;
    const match = ATTRIBUTE.exec(text);
    if (!match) {
      report(`cannot read attributes "${text.slice(start).trim()}"`);
      break;
    }
    const name = match[1].toLowerCase();
    const value = match[2] ?? match[3] ?? match[4] ?? '';
    if (attrs.has(name)) report(`duplicate attribute "${name}"`);
    checkReferences(value, (_, message) => report(`${message} in ${name}`));
    attrs.set(name, decodeEntities(value));
  }
  return attrs;
}

// Returns { errors, elements, text(element), inner(element) }. Each element records
// its name, attributes (a Map), line, parent and the list of open ancestors.
export function parseHtml(html) {
  const errors = [];
  const elements = [];
  const stack = [];
  const lineStarts = [0];
  for (let index = 0; index < html.length; index += 1) if (html[index] === '\n') lineStarts.push(index + 1);
  const lineAt = (index) => {
    let low = 0;
    let high = lineStarts.length - 1;
    while (low < high) {
      const mid = (low + high + 1) >> 1;
      if (lineStarts[mid] <= index) low = mid;
      else high = mid - 1;
    }
    return low + 1;
  };
  const error = (index, message) => errors.push(`line ${lineAt(index)}: ${message}`);

  let i = 0;
  while (i < html.length) {
    const lt = html.indexOf('<', i);
    const textEnd = lt === -1 ? html.length : lt;
    if (textEnd > i) checkReferences(html.slice(i, textEnd), (offset, message) => error(i + offset, message));
    if (lt === -1) break;

    if (html.startsWith('<!--', lt)) {
      const close = html.indexOf('-->', lt + 4);
      if (close === -1) {
        error(lt, 'unterminated comment');
        break;
      }
      i = close + 3;
      continue;
    }
    const doctype = /^<!doctype html>/i.exec(html.slice(lt, lt + 15));
    if (doctype) {
      if (lt !== 0) error(lt, 'the doctype must come first');
      i = lt + doctype[0].length;
      continue;
    }

    TAG.lastIndex = lt;
    const tag = TAG.exec(html);
    if (!tag) {
      error(lt, 'stray "<" (write &lt;)');
      i = lt + 1;
      continue;
    }
    const [raw, slash, rawName, attrText, selfClosing] = tag;
    const name = rawName.toLowerCase();
    i = lt + raw.length;

    if (slash) {
      if (attrText.trim() || selfClosing) error(lt, `malformed end tag </${name}>`);
      if (VOID_ELEMENTS.has(name)) {
        error(lt, `end tag for void element </${name}>`);
        continue;
      }
      const depth = stack.map((open) => open.name).lastIndexOf(name);
      if (depth === -1) {
        error(lt, `unexpected </${name}>`);
        continue;
      }
      if (depth !== stack.length - 1) {
        error(lt, `</${name}> closes unclosed ${stack.slice(depth + 1).map((open) => `<${open.name}>`).join(', ')}`);
      }
      while (stack.length > depth) {
        const open = stack.pop();
        open.innerEnd = lt;
        open.end = i;
      }
      continue;
    }

    const attrs = parseAttributes(attrText, (message) => error(lt, message));
    const parent = stack.at(-1) ?? null;
    const element = { name, attrs, line: lineAt(lt), start: lt, innerStart: i, innerEnd: i, end: i, parent, ancestors: stack.slice() };
    elements.push(element);

    if (CLOSES_P.has(name) && stack.some((open) => open.name === 'p')) error(lt, `<${name}> inside <p>`);
    if (name === 'a' && stack.some((open) => open.name === 'a' || open.name === 'button')) error(lt, '<a> nested inside interactive content');
    const parents = REQUIRED_PARENT[name];
    if (parents && !(parent && parents.includes(parent.name))) {
      error(lt, `<${name}> must be a child of ${parents.map((p) => `<${p}>`).join(' or ')}`);
    } else if ((name === 'dt' || name === 'dd') && parent.name === 'div' && parent.parent?.name !== 'dl') {
      error(lt, `<${name}> inside a <div> that is not a child of <dl>`);
    }

    if (VOID_ELEMENTS.has(name)) continue;
    if (selfClosing) {
      if (name === 'svg' || stack.some((open) => open.name === 'svg')) continue;
      error(lt, `<${name}/> is not self-closing in HTML; it stays open`);
    }
    if (RAW_TEXT.has(name)) {
      const close = html.toLowerCase().indexOf(`</${name}`, i);
      if (close === -1) {
        error(lt, `<${name}> is never closed`);
        break;
      }
      const gt = html.indexOf('>', close);
      element.innerEnd = close;
      element.end = gt + 1;
      i = gt + 1;
      continue;
    }
    stack.push(element);
  }
  for (const open of stack) errors.push(`line ${open.line}: <${open.name}> is never closed`);

  const inner = (element) => html.slice(element.innerStart, element.innerEnd);
  return { errors, elements, inner, text: (element) => textContent(inner(element)) };
}
