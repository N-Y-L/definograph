// Renders the tutorial's local Markdown at build time with marked, a pinned
// devDependency. The output is deliberately constrained:
// - raw HTML may only open and close <details> answers with a plain-text <summary>;
// - links and images are rebased through an explicit map, and an unmapped one fails;
// - headings get stable, unique ids; tables stack on narrow screens and take their
//   accessible name from the heading of their section;
// - Lean code is rendered from its fence text and marked with the published file (and
//   line range) it reproduces, so the checks can compare it with that file;
// - a paragraph holding only {{view:id}}, {{capture:id}} or {{image:name}} becomes the
//   recorded figure the build supplies; such a directive anywhere else is an error;
// - a Lean code block that repeats the source of a view shown on the same page is marked as
//   that view's source, and the figure then keeps its own copy in a disclosure;
// - an optional first line <!-- description: ... --> gives the page description and is
//   not rendered.
import { Lexer, Marked } from 'marked';
import { escapeHtml, findLeanSource, renderLean } from './format.mjs';
import { textContent } from './html.mjs';

const plain = (html) => textContent(html).replace(/\s+/g, ' ').trim();

// A block directive: the whole paragraph, nothing else.
export const DIRECTIVE = /^\{\{(view|capture|image):([a-z0-9][a-z0-9-]*)\}\}$/;
export const DESCRIPTION_COMMENT = /^<!--\s*description:\s*([\s\S]*?)\s*-->[ \t]*\r?\n/;
// Two sources are the same statement if they differ at most by one final newline.
export const sameSource = (a, b) => a.replace(/\n$/, '') === b.replace(/\n$/, '');
const ANY_DIRECTIVE = /\{\{(?:view|capture|image|source):/;

export function slug(text) {
  return text.toLowerCase().trim().replace(/[^\p{L}\p{N}\s-]/gu, '').replace(/\s+/g, '-');
}

// Plain text of inline tokens, as a reader sees it.
export function inlineText(tokens = []) {
  return tokens.map((token) => {
    if (token.type === 'image') return token.text ?? '';
    if (token.type === 'br') return ' ';
    if (token.tokens) return inlineText(token.tokens);
    return token.text ?? '';
  }).join('');
}

// A page description: the file's description comment, or its first ordinary paragraph as
// whole sentences up to 160 characters, or a shortened first sentence.
export function describeMarkdown(markdown, limit = 160) {
  const declared = DESCRIPTION_COMMENT.exec(markdown);
  if (declared) return declared[1].replace(/\s+/g, ' ').trim();
  const paragraph = new Lexer({ gfm: true }).lex(markdown).find((token) => token.type === 'paragraph' && !DIRECTIVE.test(token.text.trim()));
  const text = paragraph ? inlineText(paragraph.tokens).replace(/\s+/g, ' ').trim() : '';
  if (text.length <= limit) return text;
  let kept = '';
  for (const sentence of text.split(/(?<=[.!?])\s+/)) {
    const next = kept ? `${kept} ${sentence}` : sentence;
    if (next.length > limit) break;
    kept = next;
  }
  if (kept) return kept;
  const cut = text.slice(0, limit - 1);
  return `${cut.slice(0, cut.lastIndexOf(' ')).replace(/[\s,;:]+$/, '')}…`;
}

// Visits tokens in document order, including list items, blockquotes and table cells.
function visitTokens(tokens, visit) {
  for (const token of tokens ?? []) {
    visit(token);
    visitTokens(token.tokens, visit);
    visitTokens(token.items, visit);
    if (token.type === 'table') [...token.header, ...token.rows.flat()].forEach((cell) => visitTokens(cell.tokens, visit));
  }
}

// source: the Markdown file's path, for messages; resolve(href): its published URL;
// leanFiles: Map of Lean file name to text; illustration(url): { width, height } or undefined;
// directive(kind, name, { sourceShown }): the HTML of a recorded figure (throws if there is
// none); viewSource(name): the source a view was recorded from, if the view exists.
export function renderMarkdown(markdown, { source, resolve, leanFiles, illustration, directive, viewSource = () => undefined }) {
  const headings = [];
  const ids = new Set();
  const directives = [];
  const fail = (message) => {
    throw new Error(`${source}: ${message}`);
  };
  const body = markdown.replace(DESCRIPTION_COMMENT, '');

  // Before rendering: which views this page shows, which Lean blocks repeat their sources,
  // and whether each figure's statement is already visible above it (outside a disclosure).
  const tokens = new Lexer({ gfm: true }).lex(body);
  const pageViews = [];
  visitTokens(tokens, (token) => {
    if (token.type === 'link' || token.type === 'image') token.href = resolve(token.href);
    if (token.type === 'paragraph') {
      const block = DIRECTIVE.exec(token.text.trim());
      if (block) pageViews.push(block[2]);
    }
  });
  // A figure's own copy of its source (a recorded view's or a screenshot's) is collapsed
  // (never left out) when the identical statement already appears earlier in the same
  // section: after the nearest preceding h2 or h3, in a Lean block that is not inside a hint
  // or answer.
  let section = [];
  let openDisclosures = 0;
  visitTokens(tokens, (token) => {
    if (token.type === 'heading' && token.depth <= 3) section = [];
    else if (token.type === 'html') {
      const raw = token.text.trim();
      if (raw.startsWith('<details>')) openDisclosures += 1;
      else if (raw === '</details>') openDisclosures = Math.max(0, openDisclosures - 1);
    } else if (token.type === 'code' && token.lang === 'lean' && !openDisclosures) section.push(token.text);
    else if (token.type === 'paragraph') {
      const block = DIRECTIVE.exec(token.text.trim());
      if (block?.[1] !== 'view' && block?.[1] !== 'capture') return;
      const text = viewSource(block[2]);
      token.sourceShown = text !== undefined && section.some((code) => sameSource(code, text));
    }
  });
  const viewFor = (code) => pageViews.find((name) => {
    const text = viewSource(name);
    return text !== undefined && sameSource(code, text);
  });
  const marked = new Marked({
    gfm: true,
    renderer: {
      heading({ tokens, depth }) {
        const html = this.parser.parseInline(tokens);
        const text = plain(html);
        const base = slug(text) || 'section';
        let id = base;
        for (let n = 2; ids.has(id); n += 1) id = `${base}-${n}`;
        ids.add(id);
        headings.push({ depth, id, text });
        return `<h${depth} id="${id}">${html}</h${depth}>\n`;
      },
      code({ text, lang }) {
        if (lang !== 'lean') fail(`code block in "${lang || 'no language'}"; only Lean code is rendered`);
        const code = `${text}\n`;
        const view = viewFor(text);
        const match = view ? null : findLeanSource(code, leanFiles);
        const origin = view
          ? ` data-view-source="${view}"`
          : match ? ` data-source="${escapeHtml(match.name)}"${match.lines ? ` data-lines="${match.lines}"` : ''}` : '';
        const name = view ? 'Lean statement' : match ? `Lean source: ${match.name}${match.lines ? `, lines ${match.lines.replace('-', ' to ')}` : ''}` : 'Lean code';
        return `<pre class="source" tabindex="0" role="group" aria-label="${escapeHtml(name)}"><code class="language-lean"${origin}>${renderLean(code)}</code></pre>\n`;
      },
      html({ text }) {
        const raw = text.trim();
        const open = /^<details>\s*<summary>([^<>]+)<\/summary>$/.exec(raw);
        if (open) return `<details>\n<summary>${escapeHtml(open[1].trim())}</summary>\n`;
        if (raw === '</details>') return '</details>\n';
        return fail(`raw HTML is limited to <details> answers; found ${JSON.stringify(raw.slice(0, 60))}`);
      },
      table({ header, rows }) {
        const section = headings.at(-1);
        if (!section) fail('a table needs a preceding heading to name it');
        const labels = header.map((cell) => plain(this.parser.parseInline(cell.tokens)));
        const head = header.map((cell) => `<th scope="col" role="columnheader">${this.parser.parseInline(cell.tokens)}</th>`).join('');
        const body = rows.map((row) => `<tr role="row">${row.map((cell, i) => {
          const html = this.parser.parseInline(cell.tokens);
          return i === 0 ? `<th scope="row" role="rowheader">${html}</th>` : `<td role="cell" data-label="${escapeHtml(labels[i])}">${html}</td>`;
        }).join('')}</tr>`);
        return `<table class="stack-table" role="table" aria-labelledby="${section.id}">\n<thead role="rowgroup"><tr role="row">${head}</tr></thead>\n<tbody role="rowgroup">\n${body.join('\n')}\n</tbody>\n</table>\n`;
      },
      image({ href, title, text }) {
        const figure = illustration(href);
        if (!figure) fail(`image ${href} is not a listed illustration`);
        if (!text.trim()) fail(`image ${href} has no alt text`);
        return `<img src="${escapeHtml(href)}" width="${figure.width}" height="${figure.height}" alt="${escapeHtml(text)}"${title ? ` title="${escapeHtml(title)}"` : ''}>`;
      },
      paragraph(token) {
        const { tokens, text } = token;
        const block = DIRECTIVE.exec(text.trim());
        if (block) {
          if (!directive) fail(`${block[0]} cannot be used here`);
          directives.push({ kind: block[1], name: block[2] });
          return `${directive(block[1], block[2], { sourceShown: Boolean(token.sourceShown) })}\n`;
        }
        const html = this.parser.parseInline(tokens);
        const imageOnly = tokens.some((token) => token.type === 'image') && tokens.every((token) => token.type === 'image' || (token.type === 'text' && !token.text.trim()));
        return imageOnly ? `<p class="illustration">${html}</p>\n` : `<p>${html}</p>\n`;
      },
    },
  });
  const html = marked.parser(tokens);
  // A directive left in running text, a list item or a table would be published literally.
  const leftover = html.replace(/<pre[\s\S]*?<\/pre>/g, '').replace(/<figure class="dg-figure[\s\S]*?<\/figure>/g, '');
  if (ANY_DIRECTIVE.test(leftover)) fail('a {{view:…}}, {{capture:…}} or {{image:…}} directive must be a paragraph of its own');
  const h1 = headings.filter((heading) => heading.depth === 1);
  if (h1.length !== 1 || headings[0] !== h1[0]) fail('needs exactly one level-one heading, before any other');
  return { html, headings, title: h1[0].text, directives };
}

// A published Markdown guide shown on a content page (the local setup guide): the page has its
// own <h1>, so the guide's level-one heading is left out; other headings keep ids; shell blocks
// become named, focusable listings like the site's Lean listings; links stay as written. Raw
// HTML and images are not allowed.
export function renderGuide(markdown, label) {
  const fail = (message) => {
    throw new Error(`${label}: ${message}`);
  };
  const ids = new Set();
  const marked = new Marked({
    gfm: true,
    renderer: {
      heading({ tokens, depth }) {
        if (depth === 1) return '';
        const html = this.parser.parseInline(tokens);
        const base = slug(plain(html)) || 'section';
        let id = base;
        for (let n = 2; ids.has(id); n += 1) id = `${base}-${n}`;
        ids.add(id);
        return `<h${depth} id="${id}">${html}</h${depth}>\n`;
      },
      code({ text, lang }) {
        if (lang !== 'sh') fail(`code block in "${lang || 'no language'}"; a guide shows shell commands only`);
        return `<pre class="source" tabindex="0" role="group" aria-label="Shell commands"><code class="language-sh">${escapeHtml(`${text}\n`)}</code></pre>\n`;
      },
      html({ text }) {
        return fail(`raw HTML is not allowed; found ${JSON.stringify(text.trim().slice(0, 60))}`);
      },
      image({ href }) {
        return fail(`image ${href} is not allowed`);
      },
    },
  });
  const html = marked.parse(markdown);
  if (/\{\{/.test(html)) fail('contains "{{", which the site reserves for directives');
  return html;
}
