// Recorded Definograph views: the allowlist in source-assets/views/views.json, validation of
// every file it names, and the figure that presents a view on a page.
//
// A recorded view is DOM produced by the real reader components from real reader output,
// saved as a static fragment by the views pipeline. The site publishes a fragment only if:
// - the allowlist names it and pins its SHA-256 (and the batch's views.css, source and any
//   context capture);
// - it is inert: no scripts, handlers, inline styles, links, form controls, external
//   references or interactive widget roles; every id is prefixed with the view id; every
//   in-document reference (url(#…), href="#…", aria-*) resolves inside the fragment;
// - its stylesheet only styles .dg-view and its descendants and loads nothing.
// The figure inserts the fragment bytes unchanged, labels them as recorded output with the
// recording date and Lean version, and shows the exact source the reader analysed.
import { createHash } from 'node:crypto';
import { existsSync, readFileSync } from 'node:fs';
import path from 'node:path';
import { escapeHtml, renderLean } from './format.mjs';
import { hasClass, parseHtml } from './html.mjs';
import { readPng } from './png.mjs';
import { FRAGMENT_PATTERNS, RECORDED_VIEW_PATTERNS, findPrivate } from './privacy.mjs';

export const VIEWS_DIR = 'source-assets/views';
export const VIEWS_MANIFEST = `${VIEWS_DIR}/views.json`;
// Where recorded views are explained on the site; every figure links here.
export const RECORDED_HELP = '/reference/#recorded-views';
// Sources longer than this many lines are shown in a disclosure below the figure's label.
export const LONG_SOURCE_LINES = 12;

const NAME = /^[a-z0-9][a-z0-9-]{0,63}$/;
const SHA256 = /^[0-9a-f]{64}$/;
const COMMIT = /^[0-9a-f]{40}$/;
const ISO_TIME = /^(\d{4}-\d{2}-\d{2})T\d{2}:\d{2}(?::\d{2}(?:\.\d+)?)?(?:Z|[+-]\d{2}:\d{2})$/;
const LEAN_VERSION = /^\d+\.\d+\.\d+$/;
const MAX_FRAGMENT_BYTES = 1024 * 1024;
const MAX_CSS_BYTES = 512 * 1024;

export const sha256 = (data) => createHash('sha256').update(data).digest('hex');

// Where a view's screenshot is published. No "@" in the name, which some scanners mistake for
// an email address.
export const captureOutput = (batch, id) => `images/views/${batch}/${id}-context-2x.png`;

const MONTHS = ['January', 'February', 'March', 'April', 'May', 'June', 'July', 'August', 'September', 'October', 'November', 'December'];
// 2026-09-27 → 27 September 2026, independent of the build machine's locale.
export function formatDate(isoDate) {
  const [year, month, day] = isoDate.split('-').map(Number);
  return `${day} ${MONTHS[month - 1]} ${year}`;
}

function decodeUtf8(bytes, label, errors) {
  const text = bytes.toString('utf8');
  if (!Buffer.from(text, 'utf8').equals(bytes)) errors.push(`${label}: not valid UTF-8`);
  if (text.charCodeAt(0) === 0xfeff) errors.push(`${label}: starts with a byte-order mark`);
  if (/[\u0000-\u0008\u000b\u000c\u000e-\u001f\u007f]/.test(text)) errors.push(`${label}: contains control characters`);
  return text;
}

// ---------------------------------------------------------------------------------------
// Stylesheet rules

// Removes comments outside strings; comments are kept out of the checks, not the output.
export function stripCssComments(css) {
  let out = '';
  let quote = null;
  for (let i = 0; i < css.length; i += 1) {
    const ch = css[i];
    if (quote) {
      out += ch;
      if (ch === '\\') {
        out += css[i + 1] ?? '';
        i += 1;
      } else if (ch === quote) quote = null;
      continue;
    }
    if (ch === '"' || ch === "'") {
      quote = ch;
      out += ch;
      continue;
    }
    if (ch === '/' && css[i + 1] === '*') {
      const end = css.indexOf('*/', i + 2);
      if (end === -1) return { text: out, error: 'unterminated comment' };
      out += ' ';
      i = end + 1;
      continue;
    }
    out += ch;
  }
  return { text: out, error: quote ? 'unterminated string' : null };
}

// First index at or after `from` holding one of `stops` outside strings and brackets.
function scanTo(text, from, to, stops) {
  let depth = 0;
  let quote = null;
  for (let i = from; i < to; i += 1) {
    const ch = text[i];
    if (quote) {
      if (ch === '\\') i += 1;
      else if (ch === quote) quote = null;
      continue;
    }
    if (ch === '"' || ch === "'") quote = ch;
    else if (ch === '(' || ch === '[') depth += 1;
    else if (ch === ')' || ch === ']') depth = Math.max(0, depth - 1);
    else if (depth === 0 && stops.includes(ch)) return i;
  }
  return -1;
}

function matchBrace(text, open, to) {
  let depth = 0;
  let quote = null;
  for (let i = open; i < to; i += 1) {
    const ch = text[i];
    if (quote) {
      if (ch === '\\') i += 1;
      else if (ch === quote) quote = null;
      continue;
    }
    if (ch === '"' || ch === "'") quote = ch;
    else if (ch === '{') depth += 1;
    else if (ch === '}') {
      depth -= 1;
      if (depth === 0) return i;
    }
  }
  return -1;
}

function splitTopLevel(text, separator) {
  const parts = [];
  let start = 0;
  for (;;) {
    const at = scanTo(text, start, text.length, [separator]);
    if (at === -1) {
      parts.push(text.slice(start));
      return parts;
    }
    parts.push(text.slice(start, at));
    start = at + 1;
  }
}

// A selector is scoped when it starts with the .dg-view class (not a longer class name such
// as .dg-view--kind alone), or with :where(.dg-view) or :is(.dg-view), and does not continue
// to a sibling of the view root.
const ROOT = String.raw`(?:\.dg-view(?![\w-])|:(?:where|is)\(\s*\.dg-view\s*\))`;
const SCOPED = new RegExp(`^${ROOT}`);
const ROOT_SIBLING = new RegExp(String.raw`^${ROOT}(?:(?:\.|#|:{1,2})[\w-]+(?:\([^)]*\))?|\[[^\]]*\])*\s*[+~]`);

const FORBIDDEN_CSS = [
  [/\burl\s*\(/i, 'url() (the stylesheet may not load or embed resources)'],
  [/image-set\s*\(|(?<![\w-])image\s*\(|(?<![\w-])element\s*\(|cross-fade\s*\(/i, 'an image function'],
  [/expression\s*\(|-moz-binding|(?<![\w-])behavior\s*:/i, 'a scripting extension'],
  [/javascript:/i, 'a javascript: URL'],
  [/\bposition\s*:\s*fixed\b/i, 'position: fixed (content would escape its figure)'],
];

// The batch's own product commit and tree are public repository identifiers; they may be
// cited (for example in a stylesheet comment). Any other long identifier is rejected.
function withoutPublicIds(text, allow) {
  return allow.filter(Boolean).reduce((rest, id) => rest.split(id).join(''), text);
}

// Words of the animation shorthand other than a keyframes name (CSS Animations 1 and 2).
const ANIMATION_WORDS = new Set([
  'none', 'initial', 'inherit', 'unset', 'revert', 'revert-layer', 'linear', 'ease', 'ease-in', 'ease-out', 'ease-in-out', 'step-start',
  'step-end', 'jump-start', 'jump-end', 'jump-none', 'jump-both', 'start', 'end', 'infinite', 'normal', 'reverse', 'alternate',
  'alternate-reverse', 'forwards', 'backwards', 'both', 'running', 'paused', 'auto', 'replace', 'add', 'accumulate',
]);
const ANIMATION_PROPERTY = /^(?:-webkit-|-moz-|-o-)?animation(?:-name)?$/i;

// The keyframes names an animation or animation-name value uses, in order. Function
// arguments (cubic-bezier(), steps()) are skipped; var() cannot be resolved and is reported
// by validateViewCss.
export function animationNamesIn(value) {
  let flat = value.replace(/!\s*important\s*$/i, '');
  for (let before = ''; before !== flat;) {
    before = flat;
    flat = flat.replace(/[\w-]*\([^()]*\)/g, ' ');
  }
  return flat.split(',').flatMap((single) => single.trim().split(/\s+/)).filter((word) => /^-?[_a-zA-Z][\w-]*$/.test(word) && !ANIMATION_WORDS.has(word.toLowerCase()));
}

// Returns { errors, warnings, selectors, keyframes, animations } for a recorded-view
// stylesheet; animations lists each style rule that names keyframes, as { selectors, names }.
export function validateViewCss(css, label = 'views.css', { allow = [] } = {}) {
  const errors = [];
  const warnings = [];
  const selectors = [];
  const keyframes = [];
  const animations = [];
  const report = (message) => errors.push(`${label}: ${message}`);
  if (Buffer.byteLength(css) > MAX_CSS_BYTES) report(`${Buffer.byteLength(css)} bytes; the limit is ${MAX_CSS_BYTES}`);
  for (const found of findPrivate(withoutPublicIds(css, allow), RECORDED_VIEW_PATTERNS)) report(`contains a ${found}`);
  const { text, error } = stripCssComments(css);
  if (error) report(error);
  for (const [pattern, what] of FORBIDDEN_CSS) if (pattern.test(text)) report(`contains ${what}`);

  // Returns the keyframes names the rule's animation and animation-name declarations use.
  const declarations = (from, to) => {
    const body = text.slice(from, to);
    const names = [];
    if (scanTo(body, 0, body.length, ['{']) !== -1) {
      report(`nested rules are not supported: "${body.trim().slice(0, 60)}"`);
      return names;
    }
    for (const declaration of splitTopLevel(body, ';')) {
      if (!declaration.trim()) continue;
      const parsed = /^\s*(-{0,2}[a-zA-Z][\w-]*)\s*:([\s\S]*)$/.exec(declaration);
      if (!parsed) {
        report(`cannot read declaration "${declaration.trim().slice(0, 60)}"`);
        continue;
      }
      if (!ANIMATION_PROPERTY.test(parsed[1])) continue;
      if (/var\(|["']/.test(parsed[2])) report(`${parsed[1]}: "${parsed[2].trim().slice(0, 60)}" must name its keyframes directly`);
      names.push(...animationNamesIn(parsed[2]));
    }
    return names;
  };

  const block = (from, to, context) => {
    let i = from;
    while (i < to) {
      while (i < to && /\s/.test(text[i])) i += 1;
      if (i >= to) break;
      const stop = scanTo(text, i, to, ['{', ';', '}']);
      if (stop === -1) {
        report(`unterminated rule "${text.slice(i, i + 60).trim()}"`);
        return;
      }
      const prelude = text.slice(i, stop).trim();
      if (text[stop] === '}') {
        report('unbalanced "}"');
        i = stop + 1;
        continue;
      }
      if (text[stop] === ';') {
        report(prelude.startsWith('@') ? `${prelude.split(/\s/)[0]} is not allowed` : `declaration outside a rule: "${prelude.slice(0, 60)}"`);
        i = stop + 1;
        continue;
      }
      const close = matchBrace(text, stop, to);
      if (close === -1) {
        report(`unbalanced "{" after "${prelude.slice(0, 60)}"`);
        return;
      }
      if (prelude.startsWith('@')) {
        const name = prelude.slice(1).split(/[\s({]/)[0].toLowerCase();
        if (context === 'keyframes') report(`@${name} inside @keyframes`);
        else if (['media', 'supports', 'container'].includes(name)) block(stop + 1, close, 'style');
        else if (name === 'keyframes' || name === '-webkit-keyframes') {
          const animation = prelude.slice(name.length + 1).trim();
          if (!/^[a-zA-Z_][\w-]*$/.test(animation)) report(`@keyframes ${animation}: unusual animation name`);
          else if (ANIMATION_WORDS.has(animation.toLowerCase())) report(`@keyframes ${animation}: the name is a keyword of the animation property`);
          if (!keyframes.includes(animation)) keyframes.push(animation);
          block(stop + 1, close, 'keyframes');
        } else report(`@${name} is not allowed (only @media, @supports, @container and @keyframes)`);
      } else if (context === 'keyframes') {
        for (const step of splitTopLevel(prelude, ',')) {
          if (!/^\s*(?:from|to|\d+(?:\.\d+)?%)\s*$/i.test(step)) report(`keyframe selector "${step.trim()}"`);
        }
        declarations(stop + 1, close);
      } else {
        const ruleSelectors = [];
        for (const raw of splitTopLevel(prelude, ',')) {
          const selector = raw.trim().replace(/\s+/g, ' ');
          selectors.push(selector);
          ruleSelectors.push(selector);
          if (!SCOPED.test(selector)) report(`selector "${selector}" is not scoped under .dg-view`);
          else if (ROOT_SIBLING.test(selector)) report(`selector "${selector}" reaches a sibling of the view root`);
        }
        const names = declarations(stop + 1, close);
        if (names.length) animations.push({ selectors: ruleSelectors, names });
      }
      i = close + 1;
    }
  };
  block(0, text.length, 'style');
  if (!selectors.length) warnings.push(`${label}: defines no style rules`);
  // A batch is self-contained: every animation it uses is defined in its own stylesheet.
  for (const name of new Set(animations.flatMap((rule) => rule.names))) if (!keyframes.includes(name)) report(`an animation uses "${name}", which this stylesheet does not define`);
  return { errors, warnings, selectors, keyframes, animations };
}

// A batch's animation names as published: dg-<batch>-<name>, so they cannot collide with the
// site or another batch.
export const scopedAnimation = (batch, name) => `dg-${batch}-${name}`;

// Classes a selector requires: those outside functional pseudo-classes (:not(), :is(),
// :where(), :has() and the like) and attribute selectors. A selector with escapes requires
// none, so it counts as possibly matching.
function requiredClasses(selector) {
  if (selector.includes('\\')) return [];
  let flat = selector.replace(/"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g, '""').replace(/\[[^\]]*\]/g, ' ');
  for (let before = ''; before !== flat;) {
    before = flat;
    flat = flat.replace(/\([^()]*\)/g, ' ');
  }
  return [...flat.matchAll(/\.(-?[_a-zA-Z][\w-]*)/g)].map((match) => match[1]);
}

// What publishing does with a batch's @keyframes, decided at import and recorded in
// views.json: { renamed: { name: dg-<batch>-<name> }, dropped: [name] }. A keyframes rule is
// kept, under its batch-prefixed name, when some rule that names it in animation or
// animation-name could apply to an element of one of the batch's fragments: every class that
// rule's selector requires occurs in that one fragment. This over-approximates matching, so a
// keyframes rule a recorded view uses is never dropped. Every other keyframes rule is dropped,
// and the rules that name it, which apply to no recorded element, name none instead.
// `fragmentClasses` is one Set of class names per fragment of the batch.
export function keyframePlan(css, batch, fragmentClasses) {
  const { keyframes, animations } = validateViewCss(css);
  const used = new Set();
  for (const { selectors, names } of animations) {
    const applies = selectors.some((selector) => {
      const required = requiredClasses(selector);
      return fragmentClasses.some((classes) => required.every((name) => classes.has(name)));
    });
    if (applies) names.forEach((name) => used.add(name));
  }
  const plan = { renamed: {}, dropped: [] };
  for (const name of keyframes) {
    if (used.has(name)) plan.renamed[name] = scopedAnimation(batch, name);
    else plan.dropped.push(name);
  }
  return plan;
}

export function samePlan(a, b) {
  const canonical = (plan) => JSON.stringify({
    renamed: Object.entries(plan?.renamed ?? {}).sort(([x], [y]) => x.localeCompare(y)),
    dropped: [...(plan?.dropped ?? [])].sort(),
  });
  return Boolean(a && b) && canonical(a) === canonical(b);
}

// A batch's stylesheet as published: comments removed; every selector prefixed with
// :where([data-dg-batch="<batch>"]) >, so its rules reach only the figures of that batch (each
// figure's canvas carries the attribute); @keyframes renamed or dropped by the batch's
// recorded plan (keyframePlan), with every animation and animation-name value rewritten to
// match. :where() adds no specificity, so the cascade inside the batch is unchanged. The input
// has passed validateViewCss.
export function scopeViewCss(css, batch, plan) {
  const { text } = stripCssComments(css);
  const prefix = `:where([data-dg-batch="${batch}"]) > `;
  const { keyframes } = validateViewCss(css);
  for (const name of keyframes) if (!plan?.renamed?.[name] && !plan?.dropped?.includes(name)) throw new Error(`${batch}: the keyframes plan does not say what to do with @keyframes ${name}`);
  const names = new RegExp(`(?<![\\w-])(${keyframes.map((n) => n.replace(/[-]/g, '\\-')).join('|') || '(?!)'})(?![\\w-])`, 'g');
  const declarations = (body) => splitTopLevel(body, ';').map((declaration) => {
    const parsed = /^(\s*)(-{0,2}[a-zA-Z][\w-]*)(\s*:)([\s\S]*)$/.exec(declaration);
    if (!parsed || !ANIMATION_PROPERTY.test(parsed[2])) return declaration;
    return `${parsed[1]}${parsed[2]}${parsed[3]}${parsed[4].replace(names, (name) => plan.renamed[name] ?? 'none')}`;
  }).join(';');
  const block = (from, to) => {
    let out = '';
    let i = from;
    while (i < to) {
      while (i < to && /\s/.test(text[i])) i += 1;
      if (i >= to) break;
      const stop = scanTo(text, i, to, ['{', ';', '}']);
      if (stop === -1 || text[stop] !== '{') break;
      const close = matchBrace(text, stop, to);
      const prelude = text.slice(i, stop).trim();
      if (prelude.startsWith('@')) {
        const name = prelude.slice(1).split(/[\s({]/)[0].toLowerCase();
        if (['media', 'supports', 'container'].includes(name)) out += `${prelude}{\n${block(stop + 1, close)}}\n`;
        else if (name === 'keyframes' || name === '-webkit-keyframes') {
          const animation = prelude.slice(name.length + 1).trim();
          if (plan.renamed[animation]) out += `@${name} ${plan.renamed[animation]}{${text.slice(stop + 1, close).trim()}}\n`;
        } else out += `${prelude}{${text.slice(stop + 1, close).trim()}}\n`;
      } else {
        const selectors = splitTopLevel(prelude, ',').map((selector) => `${prefix}${selector.trim()}`);
        out += `${selectors.join(',')}{${declarations(text.slice(stop + 1, close).trim())}}\n`;
      }
      i = close + 1;
    }
    return out;
  };
  return block(0, text.length);
}

// Adaptations of the reader's own styles for a static page, appended to each batch's scoped
// styles. Each keeps the recorded content whole and, apart from focus rings, its look at desktop
// widths. Keep this list short and give the reason for each rule.
export const RECORDING_ADAPTATIONS = [
  {
    // A batch paints its view root with the reader's page colour (#fbfaf7), so that a fragment
    // renders on its own. On the site the canvas has the background the view's family has in
    // the app (APP_SURFACES: a card's white, a side panel's colour, the page colour), so the
    // root stays transparent and that background shows, as it does around the view in the app.
    selector: '.dg-view',
    declarations: 'background:transparent',
  },
  {
    // The reader caps its "Whole statement" outline at the viewport height (300 px on narrow
    // screens) and keeps it in view while its page scrolls. In a recording that cap only hides
    // entries behind a scroll box that keyboard users cannot reach; the outline is shown whole.
    selector: '.dg-view .sr-overview',
    declarations: 'max-height:none;overflow:visible;position:static',
  },
  {
    // The reader draws the Structure view's map inside its own box, at most 640 px tall, that
    // scrolls. A map of more than about seven objects then showed only part of itself, and the
    // rest had to be scrolled inside the figure. In a recording the map is shown whole; the page
    // scrolls instead.
    selector: '.dg-view .sv-map-scroll',
    declarations: 'max-height:none;overflow:visible',
  },
  {
    // Every focusable element in a recording (disclosure summaries and elements with a tabindex)
    // draws its focus ring in the canvas focus colour (site.css .dg-canvas --focus, #0b57d0, at
    // least 3:1 on every view background). The reader's own ring colours are weaker on these
    // backgrounds (#859dc8 on editor summaries, 2.63:1); !important because the reader's focus
    // rules reach specificity 0,4,0.
    selector: '.dg-view :is(summary,[tabindex]):focus-visible',
    declarations: 'outline-color:var(--focus)!important',
  },
  {
    // A recorded select is an inert span shaped like the control, which clips its text to one
    // line. On narrow screens the reader's longer entries ("1. Auxiliary entry _example,
    // recorded kind auxDecl") lost their end; the recording shows the whole text instead,
    // wrapping when it does not fit. Where it fits, it looks as recorded.
    selector: '.dg-view span.dg-inert-select',
    declarations: 'white-space:normal;overflow:visible;height:auto',
  },
];

export function adaptationRules(batch) {
  return RECORDING_ADAPTATIONS.map(({ selector, declarations }) => `:where([data-dg-batch="${batch}"]) > ${selector}{${declarations}}`).join('\n');
}

// Class names that a stylesheet's selectors mention.
export function selectorClasses(css) {
  const { text } = stripCssComments(css);
  const classes = new Set();
  const scrubbed = text.replace(/"(?:\\.|[^"\\])*"|'(?:\\.|[^'\\])*'/g, '""');
  // Only selector preludes: text before each "{" back to the previous "}" or "{" or ";".
  for (const match of scrubbed.matchAll(/(?:^|[{};])([^{};]*)\{/g)) {
    for (const name of match[1].matchAll(/\.(-?[_a-zA-Z][\w-]*)/g)) classes.add(name[1]);
  }
  return classes;
}

// ---------------------------------------------------------------------------------------
// Fragment rules

// Elements a static recorded view may not contain. Controls must be recorded as inert
// elements with the same classes and text; images, media and frames would load resources.
const FORBIDDEN_ELEMENTS = new Set([
  'script', 'style', 'link', 'meta', 'base', 'head', 'body', 'html', 'iframe', 'frame', 'frameset', 'object', 'embed', 'applet', 'param',
  'form', 'input', 'button', 'select', 'option', 'optgroup', 'textarea', 'datalist', 'img', 'picture', 'source', 'video', 'audio',
  'track', 'canvas', 'noscript', 'template', 'slot', 'portal', 'dialog', 'a', 'area', 'map', 'foreignobject', 'image', 'feimage',
  'animate', 'animatemotion', 'animatetransform', 'set', 'discard', 'marquee',
]);
// Roles that promise keyboard or pointer operation, which a static figure cannot keep.
const INTERACTIVE_ROLES = new Set([
  'button', 'link', 'checkbox', 'radio', 'radiogroup', 'switch', 'tab', 'tablist', 'menu', 'menubar', 'menuitem', 'menuitemcheckbox',
  'menuitemradio', 'option', 'listbox', 'combobox', 'slider', 'spinbutton', 'textbox', 'searchbox', 'scrollbar', 'tree', 'treeitem',
  'treegrid', 'grid', 'gridcell',
]);
const STATE_ATTRIBUTES = new Set([
  'aria-pressed', 'aria-checked', 'aria-expanded', 'aria-selected', 'aria-haspopup', 'aria-disabled', 'aria-readonly', 'aria-required',
  'aria-invalid', 'aria-autocomplete', 'aria-multiselectable', 'aria-activedescendant',
]);
const FORBIDDEN_ATTRIBUTES = new Set([
  'style', 'contenteditable', 'autofocus', 'accesskey', 'popover', 'popovertarget', 'popovertargetaction', 'formtarget', 'target',
  'download', 'is', 'nonce', 'integrity', 'crossorigin', 'referrerpolicy', 'http-equiv', 'srcdoc', 'sandbox', 'allow', 'ping',
]);
const URL_ATTRIBUTES = new Set([
  'href', 'xlink:href', 'src', 'srcset', 'action', 'formaction', 'poster', 'data', 'background', 'cite', 'longdesc', 'manifest',
  'codebase', 'archive', 'profile', 'usemap', 'lowsrc', 'dynsrc', 'icon', 'imagesrcset',
]);
const IDREF_ATTRIBUTES = new Set([
  'for', 'aria-labelledby', 'aria-describedby', 'aria-controls', 'aria-owns', 'aria-details', 'aria-errormessage', 'aria-flowto',
  'headers', 'list', 'form',
]);
const NAMESPACES = new Map([
  ['xmlns', new Set(['http://www.w3.org/2000/svg', 'http://www.w3.org/1999/xhtml', 'http://www.w3.org/1998/Math/MathML'])],
  ['xmlns:xlink', new Set(['http://www.w3.org/1999/xlink'])],
]);

// The text a reader sees: character ranges of text between tags, outside comments, outside
// SVG <title> and <desc> elements (tooltips and descriptions) and outside hidden elements.
// Attribute values are never visible text.
function visibleTextRanges(text, doc) {
  const hidden = [];
  for (const element of doc.elements) {
    hidden.push([element.start, element.innerStart]);
    if (element.end > element.innerEnd) hidden.push([element.innerEnd, element.end]);
    if (element.name === 'title' || element.name === 'desc' || element.attrs.has('hidden')) hidden.push([element.innerStart, element.innerEnd]);
  }
  for (const comment of text.matchAll(/<!--[\s\S]*?-->/g)) hidden.push([comment.index, comment.index + comment[0].length]);
  hidden.sort((a, b) => a[0] - b[0]);
  const ranges = [];
  let at = 0;
  for (const [from, to] of hidden) {
    if (from > at) ranges.push([at, from]);
    at = Math.max(at, to);
  }
  if (at < text.length) ranges.push([at, text.length]);
  return ranges;
}

// Returns { errors, warnings, classes, ids, root } for one fragment.
// `displayed`: identifiers the reader itself shows in this view (for example the short id in
// "attempt 4 (eb5d6a75)", which the product derives from a fresh random UUID per capture), as
// declared by the batch. Exactly those strings are allowed, and only in the view's visible
// text; the same string in an attribute or a tooltip, and any other identifier, still fail.
export function validateFragment(text, { id, kind, label = `${id}/fragment.html`, allow = [], displayed = [] }) {
  const errors = [];
  const warnings = [];
  const report = (message) => errors.push(`${label}: ${message}`);
  const declared = displayed.filter((shown) => typeof shown === 'string' && /^[\w().:#-]+(?: [\w().:#-]+)*$/.test(shown) && shown.length >= 4 && shown.length <= 64);
  for (const shown of displayed) if (!declared.includes(shown)) report(`displayed identifier ${JSON.stringify(shown)} is not a short plain string`);
  // Blank out each declared string where it occurs within visible text; everything else,
  // attributes included, is scanned as before.
  let scanned = text;
  if (declared.length) {
    const ranges = visibleTextRanges(text, parseHtml(text));
    const inVisible = (from, to) => ranges.some(([a, b]) => from >= a && to <= b);
    for (const shown of declared) {
      let found = 0;
      for (let at = text.indexOf(shown); at !== -1; at = text.indexOf(shown, at + 1)) {
        if (!inVisible(at, at + shown.length)) continue;
        found += 1;
        scanned = `${scanned.slice(0, at)}${' '.repeat(shown.length)}${scanned.slice(at + shown.length)}`;
      }
      if (!found) report(`declares displayed identifier "${shown}", which the fragment does not show as text`);
    }
  }
  if (Buffer.byteLength(text) > MAX_FRAGMENT_BYTES) report(`${Buffer.byteLength(text)} bytes; the limit is ${MAX_FRAGMENT_BYTES}`);
  else if (Buffer.byteLength(text) > 300 * 1024) warnings.push(`${label}: ${Math.round(Buffer.byteLength(text) / 1024)} KiB is heavy for one page`);
  for (const found of findPrivate(withoutPublicIds(scanned, allow), FRAGMENT_PATTERNS)) report(`contains a ${found}`);
  if (/\{\{|\}\}/.test(text)) report('contains "{{" or "}}", which the site reserves for directives');
  if (/<!\[CDATA\[/i.test(text)) report('contains a CDATA section');
  for (const comment of text.matchAll(/<!--([\s\S]*?)-->/g)) if (comment[1].trim()) report('contains a comment; comments are not published');

  const doc = parseHtml(text);
  for (const error of doc.errors) report(error);
  const roots = doc.elements.filter((element) => element.parent === null);
  const root = roots[0];
  if (roots.length !== 1) report(`needs exactly one root element (found ${roots.length})`);
  if (root) {
    if (text.slice(0, root.start).trim() || text.slice(root.end).trim()) report('has content outside its root element');
    if (root.name !== 'div' || !hasClass(root, 'dg-view') || !hasClass(root, `dg-view--${kind}`)) report(`the root must be <div class="dg-view dg-view--${kind}">`);
    if (root.attrs.get('data-view-id') !== id) report(`the root needs data-view-id="${id}"`);
  }

  const ids = new Map();
  for (const element of doc.elements) {
    const own = element.attrs.get('id');
    if (own === undefined) continue;
    if (ids.has(own)) report(`duplicate id "${own}"`);
    ids.set(own, element);
    if (!own.startsWith(`${id}-`)) report(`id "${own}" must start with "${id}-"`);
  }
  const classes = new Set();
  const internal = (reference) => {
    const target = /^#([^\s#]+)$/.exec(reference)?.[1];
    return target !== undefined && ids.has(target);
  };

  for (const element of doc.elements) {
    const at = `<${element.name}> on line ${element.line}`;
    const inSvg = element.name === 'svg' || element.ancestors.some((a) => a.name === 'svg');
    if (FORBIDDEN_ELEMENTS.has(element.name)) report(`${at} is not allowed in a recorded view`);
    if (element.name === 'title' && !inSvg) report(`${at}: <title> is only allowed inside SVG`);
    for (const name of (element.attrs.get('class') ?? '').split(/\s+/).filter(Boolean)) classes.add(name);
    for (const [name, value] of element.attrs) {
      if (name.startsWith('on')) report(`${at}: event handler attribute ${name}`);
      else if (FORBIDDEN_ATTRIBUTES.has(name)) report(`${at}: ${name} attribute`);
      else if (name === 'draggable' && value === 'true') report(`${at}: draggable`);
      else if (NAMESPACES.has(name)) {
        if (!NAMESPACES.get(name).has(value)) report(`${at}: unexpected namespace ${name}="${value}"`);
        continue;
      } else if (name.startsWith('xmlns')) report(`${at}: namespace declaration ${name}`);
      else if (URL_ATTRIBUTES.has(name)) {
        if (!((name === 'href' || name === 'xlink:href') && inSvg && internal(value))) report(`${at}: ${name}="${value}" (only in-SVG references to ids of this view are allowed)`);
      } else if (IDREF_ATTRIBUTES.has(name)) {
        for (const reference of value.split(/\s+/).filter(Boolean)) if (!ids.has(reference)) report(`${at}: ${name} refers to "${reference}", which is not in this view`);
      } else if (STATE_ATTRIBUTES.has(name)) report(`${at}: ${name} describes an operable control; record the static state as text or a class instead`);
      else if (name === 'role' && value.split(/\s+/).some((role) => INTERACTIVE_ROLES.has(role))) report(`${at}: role="${value}" promises an operable widget`);
      else if (name === 'tabindex') {
        if (value !== '0' && value !== '-1') report(`${at}: tabindex="${value}" (only 0 or -1)`);
        else if (value === '0' && !element.attrs.get('aria-label') && !element.attrs.get('aria-labelledby')) report(`${at}: a focusable element needs an accessible name`);
      }
      // Text attributes are inert, but a recorded view has no business carrying URLs.
      if (/https?:\/\/|^\s*\/\//i.test(value)) report(`${at}: ${name} contains a URL`);
      for (const match of value.matchAll(/url\(\s*(['"]?)([^'")]*)\1\s*\)/gi)) {
        if (!internal(match[2])) report(`${at}: ${name} uses url(${match[2]}), which is not an id in this view`);
      }
    }
    // An omission marker in an excerpt ([data-dg-gap], drawn as a dashed rule by the batch
    // stylesheet) must also be announced: not hidden from assistive technology, and with text.
    if (element.attrs.has('data-dg-gap')) {
      if (element.attrs.get('aria-hidden') === 'true') report(`${at}: an omission marker ([data-dg-gap]) must not be aria-hidden; it announces the omission`);
      if (!doc.text(element).trim()) report(`${at}: an omission marker ([data-dg-gap]) needs text that announces the omission`);
    }
    if (element.name === 'svg' && !element.ancestors.some((a) => a.name === 'svg')) {
      const labelled = element.attrs.has('aria-label') || element.attrs.has('aria-labelledby') || element.attrs.get('aria-hidden') === 'true'
        || doc.elements.some((child) => child.parent === element && child.name === 'title');
      if (!labelled) warnings.push(`${label}: <svg> on line ${element.line} has no accessible name`);
    }
  }
  return { errors, warnings, classes, ids: new Set(ids.keys()), root };
}

// Captions and labels allow a little inline markup: code, var, em, strong, sub, sup and
// internal links. Returns a list of problems.
export function validateInlineHtml(html, label) {
  const errors = [];
  const doc = parseHtml(html);
  for (const error of doc.errors) errors.push(`${label}: ${error}`);
  for (const element of doc.elements) {
    if (!['code', 'var', 'em', 'strong', 'sub', 'sup', 'a'].includes(element.name)) errors.push(`${label}: <${element.name}> is not allowed here`);
    for (const [name, value] of element.attrs) {
      if (!(element.name === 'a' && name === 'href')) errors.push(`${label}: attribute ${name} is not allowed here`);
      else if (!/^\/[^/]/.test(value) && !value.startsWith('#') && value !== '/') errors.push(`${label}: link ${value} must be a root-relative site link`);
    }
  }
  if (/\{\{|\}\}/.test(html)) errors.push(`${label}: contains "{{" or "}}"`);
  return errors;
}

// ---------------------------------------------------------------------------------------
// The allowlist

// Reads and validates the allowlist and every file it names. Returns
// { present, batches, views: Map(id → view), errors, warnings }. Nothing is published
// from here; the build decides which views pages use.
export function loadViews(root) {
  const errors = [];
  const warnings = [];
  const views = new Map();
  const batches = [];
  const file = path.join(root, VIEWS_MANIFEST);
  if (!existsSync(file)) return { present: false, batches, views, errors, warnings };
  let manifest;
  try {
    manifest = JSON.parse(readFileSync(file, 'utf8'));
  } catch (error) {
    errors.push(`${VIEWS_MANIFEST}: ${error.message}`);
    return { present: true, batches, views, errors, warnings };
  }
  if (![1, 2].includes(manifest.version)) errors.push(`${VIEWS_MANIFEST}: unsupported version ${manifest.version}`);
  if (!Array.isArray(manifest.batches)) {
    errors.push(`${VIEWS_MANIFEST}: "batches" must be a list`);
    return { present: true, batches, views, errors, warnings };
  }
  const read = (rel, label) => {
    const target = path.join(root, rel);
    if (!existsSync(target)) {
      errors.push(`${label}: ${rel} is missing`);
      return null;
    }
    return readFileSync(target);
  };
  const pinned = (entry, expectedPath, label) => {
    if (!entry || entry.path !== expectedPath) {
      errors.push(`${label}: path must be "${expectedPath}"`);
      return null;
    }
    if (!SHA256.test(entry.sha256 ?? '')) {
      errors.push(`${label}: needs the SHA-256 of ${expectedPath}`);
      return null;
    }
    return entry;
  };

  const batchNames = new Set();
  for (const batch of manifest.batches) {
    const at = `${VIEWS_MANIFEST} batch ${JSON.stringify(batch.batch)}`;
    if (!NAME.test(batch.batch ?? '')) {
      errors.push(`${at}: batch names are lowercase letters, digits and hyphens`);
      continue;
    }
    if (batchNames.has(batch.batch)) errors.push(`${at}: listed twice`);
    batchNames.add(batch.batch);
    const date = ISO_TIME.exec(batch.createdAt ?? '')?.[1];
    if (!date) errors.push(`${at}: createdAt must be an ISO 8601 time`);
    if (!LEAN_VERSION.test(batch.lean ?? '')) errors.push(`${at}: lean must be a version such as 4.28.0`);
    if (manifest.version === 1) {
      if (!COMMIT.test(batch.product?.commit ?? '')) errors.push(`${at}: product.commit must be the full product commit`);
      if (!SHA256.test(batch.manifest?.sha256 ?? '')) errors.push(`${at}: manifest.sha256 must be the SHA-256 of the batch's manifest.json`);
      // Only a batch its pipeline declared finished is imported (import-views.mjs, readyDeclaration).
      if (!/^READY-[\w.-]+\.json$/.test(batch.ready?.file ?? '') || typeof batch.ready?.at !== 'string') errors.push(`${at}: ready (the READY declaration the import accepted the batch under) is missing; re-import the batch`);
    } else {
      // Public build manifests retain asset integrity without private capture provenance.
      const allowed = ['batch', 'createdAt', 'lean', 'stylesheet', 'keyframes', 'views'];
      for (const key of Object.keys(batch)) if (!allowed.includes(key)) errors.push(`${at}: unexpected public batch field ${key}`);
    }
    const dir = `${VIEWS_DIR}/${batch.batch}`;
    const record = { name: batch.batch, dir, date, createdAt: batch.createdAt, lean: batch.lean, commit: batch.product?.commit, product: batch.product, css: null, cssPath: `${dir}/views.css`, views: [] };
    const sheet = pinned(batch.stylesheet, 'views.css', `${at} stylesheet`);
    if (sheet) {
      const bytes = read(record.cssPath, at);
      if (bytes) {
        if (sha256(bytes) !== sheet.sha256) errors.push(`${record.cssPath} does not match its pinned SHA-256`);
        const css = decodeUtf8(bytes, record.cssPath, errors);
        const result = validateViewCss(css, record.cssPath, { allow: [batch.product?.commit, batch.product?.tree] });
        errors.push(...result.errors);
        warnings.push(...result.warnings);
        record.css = css;
        record.cssBytes = bytes;
        record.cssClasses = selectorClasses(css);
      }
    }
    for (const view of batch.views ?? []) {
      const vat = `${at} view ${JSON.stringify(view.id)}`;
      if (!NAME.test(view.id ?? '') || /^view(?:-|$)/.test(view.id)) {
        errors.push(`${vat}: view ids are lowercase letters, digits and hyphens, and do not start with "view"`);
        continue;
      }
      if (views.has(view.id)) {
        errors.push(`${vat}: the id is used by another view`);
        continue;
      }
      if (!NAME.test(view.kind ?? '')) errors.push(`${vat}: kind must be lowercase letters, digits and hyphens`);
      // A capture-only entry is a screenshot of the whole application with no recorded view.
      const captureOnly = view.fragment === undefined && view.context !== undefined;
      for (const field of captureOnly ? ['title'] : ['title', 'label']) {
        if (typeof view[field] !== 'string' || !view[field].trim() || view[field].length > 240) errors.push(`${vat}: needs a ${field} (plain text, at most 240 characters)`);
      }
      if (!captureOnly) {
        if (typeof view.caption !== 'string' || !view.caption.trim()) errors.push(`${vat}: needs a caption`);
        else errors.push(...validateInlineHtml(view.caption, `${vat} caption`));
      }
      // An excerpt is a recorded view of only part of a panel. The site says so in the
      // provenance line, with dashed frame edges and a note for assistive technology, and at
      // the start of its reviewed caption.
      if (view.excerpt !== undefined && (view.excerpt !== true || captureOnly)) errors.push(`${vat}: excerpt is either true or absent, and only a recorded view can be one`);
      if (view.excerpt === true && !view.captionDraft && typeof view.caption === 'string' && !/^(?:Excerpt\b|Part of\b)/.test(view.caption.replace(/<[^>]*>/g, '').trim())) errors.push(`${vat}: an excerpt's caption begins with "Excerpt" or "Part of", so it says that the figure shows only part of a panel`);
      // A recording drawn from a saved record (the batch's recordedState.savedRecord) says so in
      // its provenance line.
      if (view.savedRecord !== undefined && view.savedRecord !== true) errors.push(`${vat}: savedRecord is either true or absent`);
      if ((!captureOnly || view.source !== undefined) && !['term', 'file'].includes(view.source?.form)) errors.push(`${vat}: source.form must be "term" or "file"`);
      if (view.sizing !== undefined) {
        const { minWidthPx, target } = view.sizing ?? {};
        if (!Number.isInteger(minWidthPx) || minWidthPx < 1 || minWidthPx > 4000 || !['svg', 'root'].includes(target)) errors.push(`${vat}: sizing needs an integer minWidthPx (1 to 4000) and a target of "svg" or "root"`);
      }

      const entry = { ...view, captureOnly, batch: record, fragmentPath: captureOnly ? null : `${dir}/${view.id}/fragment.html`, sourcePath: `${dir}/${view.id}/source.lean` };
      const fragment = captureOnly ? null : pinned(view.fragment, `${view.id}/fragment.html`, `${vat} fragment`);
      if (fragment) {
        const bytes = read(entry.fragmentPath, vat);
        if (bytes) {
          if (sha256(bytes) !== fragment.sha256) errors.push(`${entry.fragmentPath} does not match its pinned SHA-256`);
          entry.fragmentText = decodeUtf8(bytes, entry.fragmentPath, errors);
          if (view.displayedIdentifiers !== undefined && !Array.isArray(view.displayedIdentifiers)) errors.push(`${vat}: displayedIdentifiers must be a list`);
          const result = validateFragment(entry.fragmentText, { id: view.id, kind: view.kind, label: entry.fragmentPath, displayed: view.displayedIdentifiers ?? [] });
          errors.push(...result.errors);
          warnings.push(...result.warnings);
          entry.classes = result.classes;
        }
      }
      const source = captureOnly && view.source === undefined ? null : pinned(view.source, `${view.id}/source.lean`, `${vat} source`);
      if (!source) entry.sourcePath = null;
      if (source) {
        const bytes = read(entry.sourcePath, vat);
        if (bytes) {
          if (sha256(bytes) !== source.sha256) errors.push(`${entry.sourcePath} does not match its pinned SHA-256`);
          entry.sourceText = decodeUtf8(bytes, entry.sourcePath, errors);
          if (!entry.sourceText.trim()) errors.push(`${entry.sourcePath} is empty`);
          for (const found of findPrivate(entry.sourceText, RECORDED_VIEW_PATTERNS)) errors.push(`${entry.sourcePath}: contains a ${found}`);
        }
      }
      if (view.context !== undefined) {
        const context = pinned(view.context, `${view.id}/context@2x.png`, `${vat} context`);
        if (context) {
          entry.contextPath = `${dir}/${view.id}/context@2x.png`;
          entry.contextOutput = captureOutput(batch.batch, view.id);
          const bytes = read(entry.contextPath, vat);
          if (bytes) {
            if (sha256(bytes) !== context.sha256) errors.push(`${entry.contextPath} does not match its pinned SHA-256`);
            const png = readPng(bytes);
            for (const error of png.errors) errors.push(`${entry.contextPath}: ${error}`);
            if (png.width !== context.width || png.height !== context.height) errors.push(`${entry.contextPath}: ${png.width}×${png.height} pixels, but the allowlist says ${context.width}×${context.height}`);
            if (png.width % 2 || png.height % 2) errors.push(`${entry.contextPath}: a device-scale-2 capture has even pixel dimensions`);
            if (png.animated) errors.push(`${entry.contextPath}: animated PNGs are not published`);
            const metadata = [...png.metadata.map(({ data }) => data.toString('latin1')), ...png.text.map(({ keyword, value }) => `${keyword} ${value}`)].join('\n');
            if (png.metadata.length) errors.push(`${entry.contextPath}: carries PNG metadata chunks (${[...new Set(png.metadata.map(({ type }) => type))].join(', ')}); publish pixels only`);
            for (const found of findPrivate(metadata, RECORDED_VIEW_PATTERNS)) errors.push(`${entry.contextPath}: metadata contains a ${found}`);
            // Alt text and caption are written by the site; a page may not use the capture
            // until both exist (the build refuses), but an unused capture does not block.
            entry.contextIncomplete = typeof view.context.alt !== 'string' || !view.context.alt.trim() || typeof view.context.caption !== 'string' || !view.context.caption.trim();
            if (entry.contextIncomplete) warnings.push(`${vat}: the context capture needs alt text and a caption before a page uses it`);
            else errors.push(...validateInlineHtml(view.context.caption, `${vat} context caption`));
            // Text carried over from an earlier screenshot (import-views.mjs) waits for review.
            if (view.context.textDraft !== undefined && view.context.textDraft !== true) errors.push(`${vat}: context.textDraft is either true or absent`);
            entry.contextDraft = view.context.textDraft === true;
            if (entry.contextDraft) warnings.push(`${vat}: the capture's alt text and caption were written for an earlier screenshot; review them before a page uses it`);
            entry.contextBytes = bytes;
          }
        }
      }
      if (view.captionDraft) warnings.push(`${vat}: the caption is an imported draft; review it before a page uses this view`);
      views.set(view.id, entry);
      record.views.push(entry);
    }
    // The import recorded what publishing does with the batch's @keyframes; it must still be
    // what the pinned stylesheet and fragments give.
    if (record.css !== null) {
      const plan = keyframePlan(record.css, record.name, record.views.filter((view) => view.classes).map((view) => view.classes));
      if (!batch.keyframes) errors.push(`${at}: keyframes (the import's record of renamed and dropped @keyframes) is missing; re-import the batch`);
      else if (!samePlan(batch.keyframes, plan)) errors.push(`${at}: keyframes ${JSON.stringify(batch.keyframes)} is not what the stylesheet and fragments give (${JSON.stringify(plan)}); re-import the batch`);
      record.keyframePlan = plan;
    }
    batches.push(record);
  }
  return { present: true, batches, views, errors, warnings };
}

// On wide screens recorded views are drawn a little larger, closer to the page's reading
// size. A view that reflows is zoomed from 62.5em (site.css, .dg-reflows). A view with a
// minimum width is zoomed from 80em only if its zoomed width still fits the narrowest wide
// column: a tutorial page with its sidebar at 1280 px leaves 866 px for the view.
export const VIEW_ZOOM = 1.125;
const NARROWEST_WIDE_CANVAS = 866;

// On paper nothing scrolls. A diagram whose minimum width, with the canvas padding and frame
// borders of the print styles (18 px), is wider than the text column of an A4 page with the
// browser's default 1 cm margins (718 px) is drawn smaller there, just enough to fit.
const PRINT_COLUMN = 718;
const PRINT_FRAME = 18;

// Minimum widths of recorded diagrams, generated from the allowlist: a diagram keeps its
// intrinsic width and its figure scrolls instead of shrinking the labels.
export function sizingRules(views) {
  const sized = views.filter((view) => view.sizing);
  const rules = sized.map((view) => {
    const scope = `.dg-view[data-view-id="${view.id}"]`;
    return `${view.sizing.target === 'svg' ? `${scope} svg` : scope}{min-width:${view.sizing.minWidthPx}px}`;
  });
  const zoomed = sized.filter((view) => view.sizing.target === 'root' && view.sizing.minWidthPx * VIEW_ZOOM <= NARROWEST_WIDE_CANVAS);
  if (zoomed.length) rules.push(`@media (min-width:80em){${zoomed.map((view) => `.dg-view[data-view-id="${view.id}"]{zoom:${VIEW_ZOOM}}`).join('')}}`);
  const printed = sized.filter((view) => view.sizing.target === 'root' && view.sizing.minWidthPx + PRINT_FRAME > PRINT_COLUMN);
  if (printed.length) rules.push(`@media print{${printed.map((view) => `.dg-view[data-view-id="${view.id}"]{zoom:${Math.floor(((PRINT_COLUMN - PRINT_FRAME) / view.sizing.minWidthPx) * 1000) / 1000}}`).join('')}}`);
  return rules.length ? `\n/* Minimum widths of recorded diagrams, from source-assets/views/views.json: diagrams scroll instead of shrinking. */\n${rules.join('\n')}\n` : '';
}

// ---------------------------------------------------------------------------------------
// Presentation

// The figure's label: what it is, the Lean version and the recording date. The product
// revision stays in the allowlist.
// A figure drawn from a saved record (an editor history rendered without a live editor) adds
// "from a saved history" after its kind.
export const SAVED_HISTORY = 'from a saved history';
export function provenanceLine(kind, date, lean, { savedRecord = false } = {}) {
  return `<p class="dg-provenance"><a class="dg-recorded" href="${RECORDED_HELP}">${kind}</a>${savedRecord ? ` · ${SAVED_HISTORY}` : ''} · Lean ${escapeHtml(lean)} · <time datetime="${date}">${formatDate(date)}</time></p>`;
}
const provenance = (kind, view) => provenanceLine(kind, view.batch.date, view.batch.lean, { savedRecord: view.savedRecord === true });

// The background each family of recorded views has in the app, so that a recording keeps the
// contrast its inks were designed for. The views under Explore a sample sit in a white card
// (.view-card); the editor's Source data and the Inspect panel's coverage sit in a side panel
// (.atlas-drawer, --surface); everything else sits on the page, the canvas default in site.css:
// the Visual sequence and its outline, and numerical views, whose recording includes their card.
export const APP_SURFACES = {
  card: ['quantifier-flow', 'relation-map', 'semantic-map'],
  panel: ['coverage', 'editor-source-data', 'editor-occurrence', 'editor-attempt', 'editor-supply'],
};
export function surfaceOf(kind) {
  return Object.keys(APP_SURFACES).find((surface) => APP_SURFACES[surface].includes(kind)) ?? null;
}

// What an excerpt figure says to assistive technology before the view; sighted readers see the
// frame's dashed top and bottom edges.
export const EXCERPT_NOTE = 'Only part of the panel is shown; the rest of the panel is left out.';

// The exact source beside the view. A published download with identical bytes is linked.
// The listing sits in a closed disclosure when it is long, or when the same statement already
// appears earlier in the section (sourceShown); it is never left out.
function sourceBlock(view, downloadFor, sourceShown) {
  const text = view.sourceText;
  const lines = text.replace(/\n$/, '').split('\n').length;
  const listingName = view.source.form === 'term' ? 'Lean statement, as entered in Definograph' : 'Lean source file';
  const code = `<pre class="source" tabindex="0" role="group" aria-label="${listingName}"><code class="language-lean" data-view-source="${view.id}">${renderLean(text)}</code></pre>`;
  const download = downloadFor?.(text);
  const name = download ? `<a class="filename" href="/${download.output}" download>${escapeHtml(path.posix.basename(download.output))}</a>` : null;
  const kind = view.source.form === 'term' ? 'Lean statement' : 'Lean source';
  const described = view.source.form === 'term' ? 'Lean statement, as entered in Definograph' : 'Lean source file';
  const labelText = name ? `${described}: ${name}` : described;
  if (sourceShown) {
    return `<details class="dg-source">\n<summary>Source</summary>\n<p class="dg-source-label">${labelText}</p>\n${code}\n</details>`;
  }
  if (lines > LONG_SOURCE_LINES) {
    return `<details class="dg-source">\n<summary>${kind} (${lines} lines)</summary>\n<p class="dg-source-label">${labelText}</p>\n${code}\n</details>`;
  }
  return `<div class="dg-source">\n<p class="dg-source-label">${labelText}</p>\n${code}\n</div>`;
}

// The fragment exactly as recorded, apart from trailing whitespace at its end.
export function fragmentBody(view) {
  return view.fragmentText.replace(/\s+$/, '');
}

export function renderViewFigure(view, { downloadFor, sourceShown = false } = {}) {
  return [
    `<figure class="dg-figure${view.excerpt ? ' dg-figure-excerpt' : ''}" id="view-${view.id}">`,
    provenance(view.excerpt ? 'Recorded Definograph excerpt' : 'Recorded Definograph output', view),
    sourceBlock(view, downloadFor, sourceShown),
    ...(view.excerpt ? [`<p class="visually-hidden">${EXCERPT_NOTE}</p>`] : []),
    `<div class="dg-scroll" role="region" tabindex="0" aria-label="${escapeHtml(view.label)}">`,
    `<div class="dg-canvas${view.sizing ? '' : ' dg-reflows'}" data-dg-batch="${view.batch.name}"${surfaceOf(view.kind) ? ` data-dg-surface="${surfaceOf(view.kind)}"` : ''}>`,
    fragmentBody(view),
    '</div>',
    '</div>',
    `<figcaption class="dg-caption">${view.caption}</figcaption>`,
    '</figure>',
  ].join('\n');
}

export function renderCaptureFigure(view, { downloadFor, sourceShown = false } = {}) {
  const width = view.context.width / 2;
  const height = view.context.height / 2;
  const src = `/${view.contextOutput}`;
  return [
    `<figure class="dg-figure dg-figure-capture" id="capture-${view.id}">`,
    provenance('Recorded Definograph screenshot', view),
    ...(view.sourceText !== undefined ? [sourceBlock(view, downloadFor, sourceShown)] : []),
    // Shown at its CSS size (half its pixel size): the application's text keeps its own size
    // and the frame scrolls sideways where the page is narrower.
    `<div class="dg-image dg-scroll" role="region" tabindex="0" aria-label="${escapeHtml(`Recorded screenshot: ${view.title}`)}"><img src="${src}" width="${width}" height="${height}" alt="${escapeHtml(view.context.alt)}" loading="lazy" decoding="async"></div>`,
    `<figcaption class="dg-caption">${view.context.caption} <a href="${src}">Open the screenshot on its own</a>.</figcaption>`,
    '</figure>',
  ].join('\n');
}
