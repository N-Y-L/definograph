// npm run check: rebuild dist/, then verify it. Exits non-zero if any check fails.
// Checks are static plus a request run against the local preview server; they do
// not render pages in a browser.
import { createHash } from 'node:crypto';
import http from 'node:http';
import { readFile } from 'node:fs/promises';
import path from 'node:path';
import { Lexer } from 'marked';
import { build, listFiles, publishedStylesheet, tutorialDescription } from './build.mjs';
import { excerptLines, inspectSvg } from './format.mjs';
import { conflictingHeaders, headersFor, matchesPattern, parseHeaders, parseRedirects } from './headers.mjs';
import { hasClass, parseHtml } from './html.mjs';
import { DESCRIPTION_COMMENT, DIRECTIVE, sameSource } from './markdown.mjs';
import { readPng } from './png.mjs';
import { validatePublishedMathCss } from './math-assets.mjs';
import { runMathSelfTest } from './math-selftest.mjs';
import { checkPageDirectives } from './page-directives.mjs';
import { runPageDirectiveSelfTest } from './page-directives-selftest.mjs';
import { createPreviewServer } from './preview-server.mjs';
import { PRIVATE_PATHS, findPrivate } from './privacy.mjs';
import {
  DIST, DOWNLOADS, EXTERNAL_LINKS, FAVICON, HEADERS, ILLUSTRATIONS, IMAGES, LEAN_SOURCES, NOT_FOUND, ORIGIN, PAGES, READER_IMAGE_BATCH,
  READER_VIEWS, REDIRECTS, ROOT, ROUTES, SITE_NAME, STYLESHEET, TEMPLATE, TITLE_SUFFIX, TUTORIAL, TUTORIAL_LINKS, outputAllowlist, redirectsFile, routeOutput,
} from './site.mjs';
import { runViewSelfTest } from './views-selftest.mjs';
import { runProvenanceSelfTest } from './provenance-selftest.mjs';
import { EXCERPT_NOTE, RECORDED_HELP, SAVED_HISTORY, VIEWS_MANIFEST, surfaceOf, adaptationRules, animationNamesIn, formatDate, fragmentBody, keyframePlan, samePlan, scopeViewCss, selectorClasses, sizingRules, validateViewCss } from './views.mjs';

// Reviewed statements of scope that must stay on the home page verbatim.
const HOME_SCOPE = [
  'The formal foundations already prove general results about specified encodings of Lean expressions and local source records: decoding an encoding recovers the expression’s structure, and the encoded forms can be printed as text and read back exactly.',
  'The goal is a formally proved general visualization method for any valid Lean mathematical statement. The current application provides bounded structural inspection and selected guided readings; a universal guarantee connecting valid inputs to the rendered interactive view remains unproved.',
];
// The Markdown parser is a build-time devDependency, pinned exactly.
const MARKED_VERSION = '17.0.5';
// Primary navigation labels, in route order; the site name links home.
const PRIMARY_LABELS = ['Tutorial', 'Examples', 'Reference', 'Setup'];
// What a figure's provenance link may say, by figure kind.
const PROVENANCE = { view: 'Recorded Definograph output', excerpt: 'Recorded Definograph excerpt', image: 'Recorded Definograph image', capture: 'Recorded Definograph screenshot' };
// A teaching illustration must be followed by a sentence saying it is not reader output.
const NOT_READER_OUTPUT = /not (?:a )?(?:captured|recorded) Definograph (?:view|output)|not output from the Definograph reader|not Definograph output/i;
// Site selectors that may reach inside recorded views: box sizing (the reader's own CSS
// uses border-box throughout), the focus ring, and the document-level rules.
const UNGUARDED_ALLOWED = new Set(['*', '*::before', '*::after', 'html', 'body', ':root', ':focus-visible', 'main:focus', ':target', 'details::details-content']);

const results = [];
const warnings = [];
const sha256 = (data) => createHash('sha256').update(data).digest('hex');
const normalize = (text) => text.replace(/\s+/g, ' ').trim();
const basename = (file) => path.posix.basename(file);

// URL-bearing values of an element: href, src and each srcset candidate.
function urlsOf(element) {
  const urls = [];
  for (const attr of ['href', 'src']) if (element.attrs.has(attr)) urls.push([attr, element.attrs.get(attr)]);
  if (element.attrs.has('srcset')) {
    for (const candidate of element.attrs.get('srcset').split(',')) urls.push(['srcset', candidate.trim().split(/\s+/)[0]]);
  }
  return urls;
}

async function group(name, run) {
  const failures = [];
  let summary = '';
  try {
    summary = await run((message) => failures.push(message));
  } catch (error) {
    failures.push(`check crashed: ${error.stack ?? error.message}`);
  }
  results.push({ name, failures, summary });
}

let built;
try {
  built = await build();
} catch (error) {
  console.error(`✗ build: ${error.message}`);
  process.exit(1);
}
console.log(`Built ${built.files.length} files into dist/.\n`);
warnings.push(...built.warnings);
const usedViews = new Map(built.used.views.map((view) => [view.id, view]));
const usedImages = new Map(built.used.images.map((image) => [image.name, image]));
const usedCaptures = new Map(built.used.captures.map((view) => [view.id, view]));

const files = (await listFiles(DIST)).sort();
const fileSet = new Set(files);
const pages = [
  ...PAGES.map((entry) => ({ file: routeOutput(entry), path: entry.path, entry, tutorial: TUTORIAL.includes(entry) })),
  { file: NOT_FOUND.output, path: null, entry: NOT_FOUND, tutorial: false },
];
for (const page of pages) {
  page.source = await readFile(path.join(DIST, page.file), 'utf8');
  page.doc = parseHtml(page.source);
  page.ids = new Map();
  page.duplicateIds = [];
  for (const element of page.doc.elements) {
    const id = element.attrs.get('id');
    if (id === undefined) continue;
    if (page.ids.has(id)) page.duplicateIds.push(id);
    page.ids.set(id, element);
  }
  page.all = (name) => page.doc.elements.filter((element) => element.name === name);
  page.main = page.all('main')[0];
  page.within = (ancestor) => page.doc.elements.filter((element) => element.ancestors.includes(ancestor));
  page.children = (parent) => page.doc.elements.filter((element) => element.parent === parent);
  // Accessible name from aria-label, or from the elements aria-labelledby names.
  page.nameOf = (element) => element.attrs.get('aria-label')
    ?? normalize((element.attrs.get('aria-labelledby') ?? '').split(/\s+/).filter(Boolean).map((id) => (page.ids.has(id) ? page.doc.text(page.ids.get(id)) : '')).join(' '));
  page.h1 = normalize(page.all('h1')[0] ? page.doc.text(page.all('h1')[0]) : '');
  // Recorded content: a view fragment (the reader's own markup) and every figure around one.
  page.inView = (element) => hasClass(element, 'dg-view') || element.ancestors.some((a) => hasClass(a, 'dg-view'));
  page.inFigure = (element) => hasClass(element, 'dg-figure') || element.ancestors.some((a) => hasClass(a, 'dg-figure'));
  page.figures = page.doc.elements.filter((element) => element.name === 'figure' && hasClass(element, 'dg-figure'));
}
const pageByFile = new Map(pages.map((page) => [page.file, page]));
const pageByPath = new Map(pages.filter((page) => page.path).map((page) => [page.path, page]));
const tutorialPages = TUTORIAL.map((entry) => pageByPath.get(entry.path));
const tutorialLabel = (page) => page.entry.label ?? page.h1;
for (const page of tutorialPages) page.markdown = await readFile(path.join(ROOT, page.entry.source), 'utf8');

// Paths that must not exist. They are requested from the preview server and matched
// against _headers: each must return the 404 page and must not inherit long caching.
const MISSING_PATHS = [
  '/no-such-page',
  '/examples/QuantifierForallExists.lean',
  '/learn/examples/',
  '/learn/examples/Missing.lean',
  '/learn/figures/',
  '/learn/figures/missing.svg',
  '/learn/lesson-7/',
  '/learn/follow-the-scope/missing/',
  '/learn/01-follow-the-scope.md',
  '/learn/PLAN.md',
  '/content/index.html',
  '/no-such-folder/index.html',
  '/tutorial/README.md',
  '/package.json',
  '/package-lock.json',
  '/node_modules/marked/package.json',
  '/reference/contracts/',
  '/assets/',
  '/assets/missing.js',
  '/assets/missing.css',
  '/assets/site.css',
  '/assets/site.0000000000.css',
  '/assets/views.css',
  `/assets/${built.stylesheet}.map`,
  '/app.js',
  '/api/',
  '/api/readings',
  '/_headers',
  '/_redirects',
  '/assets/reader/',
  '/assets/reader/missing.png',
  '/images/',
  '/images/missing.png',
  '/images/Quantifier-Forall-Exists.png',
  '/images/views/',
  '/images/views/missing@2x.png',
  '/source-assets/reader/public-views.json',
  `/${VIEWS_MANIFEST}`,
  '/views/',
  '/views.css',
  '/scripts/fixtures/views/fixture-1/manifest.json',
  // Wrong-case spellings of existing paths: the host matches paths case-sensitively.
  '/Learn/',
  '/Learn/Follow-The-Scope/',
  '/Favicon.svg',
  '/learn/examples/rotorlaw.lean',
  '/learn/figures/Quantifier-Scope.svg',
];
const leanText = new Map();
for (const { source } of LEAN_SOURCES) leanText.set(basename(source), await readFile(path.join(ROOT, source), 'utf8'));

await group('output allowlist', async (fail) => {
  const expected = outputAllowlist(built.stylesheet, built.used);
  // Called with the stylesheet name alone (as external tools do), the allowlist reads the
  // placed figures from the page sources; it must describe the same output.
  if (outputAllowlist(built.stylesheet).join('\n') !== expected.join('\n')) fail('outputAllowlist(stylesheet) without the build\'s figure list differs from the build');
  for (const file of files) if (!expected.includes(file)) fail(`unexpected file dist/${file}`);
  for (const file of expected) if (!fileSet.has(file)) fail(`missing dist/${file}`);
  const names = DOWNLOADS.map(({ output }) => basename(output));
  if (new Set(names).size !== names.length) fail('a download is published under more than one path');
  return `${files.length} files, exactly the allowlist; each download published once`;
});

await group('HTML syntax and structure', async (fail) => {
  const FORBIDDEN = new Set([
    'script', 'style', 'iframe', 'frame', 'object', 'embed', 'form', 'input', 'button', 'select', 'textarea',
    'base', 'noscript', 'canvas', 'video', 'audio',
  ]);
  const titles = new Set();
  const descriptions = new Set();
  const navRoutes = ROUTES.filter((route) => route.nav);
  for (const page of pages) {
    const f = (message) => fail(`${page.file}: ${message}`);
    const { doc, source } = page;
    doc.errors.forEach(f);
    if (!source.startsWith('<!doctype html>')) f('must start with <!doctype html>');
    for (const id of page.duplicateIds) f(`duplicate id "${id}"`);

    const html = page.all('html');
    if (html.length !== 1 || html[0].attrs.get('lang') !== 'en') f('needs one <html lang="en">');
    const metas = page.all('meta');
    const charset = metas.find((meta) => meta.attrs.has('charset'));
    if (!charset || charset.attrs.get('charset').toLowerCase() !== 'utf-8' || charset.start > 1024) {
      f('<meta charset="utf-8"> must appear within the first 1024 bytes');
    }
    if (!metas.some((meta) => meta.attrs.get('name') === 'viewport' && /width=device-width/.test(meta.attrs.get('content') ?? ''))) {
      f('viewport meta missing');
    }
    if (!metas.some((meta) => meta.attrs.get('name') === 'color-scheme' && meta.attrs.get('content') === 'light dark')) f('needs <meta name="color-scheme" content="light dark">');
    // Titles and descriptions: content pages use the approved metadata; a tutorial page's
    // title is its h1 plus the suffix, and its description is its first paragraph.
    const title = page.all('title').filter((element) => element.parent?.name === 'head').map((element) => normalize(doc.text(element)));
    const expectedTitle = !page.tutorial ? page.entry.title : page.h1.includes(SITE_NAME) ? page.h1 : `${page.h1}${TITLE_SUFFIX}`;
    if (title.length !== 1 || title[0] !== expectedTitle) f(`title must be "${expectedTitle}"`);
    else if (titles.has(title[0])) f(`title "${title[0]}" is used by another page`);
    else titles.add(title[0]);
    const expectedDescription = page.tutorial ? tutorialDescription(page.entry.source, page.markdown) : page.entry.description;
    const description = metas.filter((meta) => meta.attrs.get('name') === 'description').map((meta) => meta.attrs.get('content') ?? '');
    if (!expectedDescription) f('has no description (a tutorial page needs an opening paragraph)');
    else if (description.length !== 1 || description[0] !== expectedDescription) f(`meta description must be "${expectedDescription}"`);
    else if (description[0].length > 160) f(`meta description is ${description[0].length} characters (keep it to 160)`);
    else if (descriptions.has(description[0])) f('meta description is used by another page');
    else descriptions.add(description[0]);
    if (metas.some((meta) => (meta.attrs.get('http-equiv') ?? '').toLowerCase() === 'refresh')) f('meta refresh redirects are not allowed');

    const links = page.all('link');
    for (const link of links) {
      if (!['canonical', 'icon', 'stylesheet'].includes(link.attrs.get('rel'))) f(`<link rel="${link.attrs.get('rel')}"> is not used on this site`);
    }
    const canonical = links.filter((link) => link.attrs.get('rel') === 'canonical');
    const ogUrl = metas.filter((meta) => meta.attrs.get('property') === 'og:url');
    const robots = metas.filter((meta) => meta.attrs.get('name') === 'robots');
    if (page.path) {
      const expected = `${ORIGIN}${page.path}`;
      if (canonical.length !== 1 || canonical[0].attrs.get('href') !== expected) f(`canonical link must be ${expected}`);
      if (ogUrl.length !== 1 || ogUrl[0].attrs.get('content') !== expected) f(`og:url must be ${expected}`);
      if (robots.length) f('route pages must not carry a robots meta');
    } else {
      if (canonical.length || ogUrl.length) f('the 404 page must not declare a canonical URL');
      if (robots.length !== 1 || robots[0].attrs.get('content') !== 'noindex') f('the 404 page needs <meta name="robots" content="noindex">');
    }
    const stylesheets = links.filter((link) => link.attrs.get('rel') === 'stylesheet');
    if (stylesheets.length !== 1 || stylesheets[0].attrs.get('href') !== `/assets/${built.stylesheet}`) {
      f('needs exactly one stylesheet link, to the hashed stylesheet');
    }
    const icons = links.filter((link) => link.attrs.get('rel') === 'icon');
    if (icons.length !== 1 || icons[0].attrs.get('href') !== '/favicon.svg') f('needs the /favicon.svg icon link');

    const mains = page.all('main');
    if (mains.length !== 1 || mains[0].attrs.get('id') !== 'main') f('needs one <main id="main">');
    const siteHeaders = page.all('header').filter((header) => hasClass(header, 'site-header'));
    if (siteHeaders.length !== 1 || siteHeaders[0].ancestors.some((a) => a.name === 'main')) f('needs one site header outside <main>');
    const footers = page.all('footer').filter((footer) => !footer.ancestors.some((a) => a.name === 'main'));
    if (footers.length !== 1) f('needs one site footer outside <main>');
    // The site's own navigation landmarks have distinct names. A recorded view keeps the
    // reader's markup (for example its "Reading steps" navigation, which repeats when a page
    // shows several reading steps); its navigation must still be named.
    const siteNavs = page.all('nav').filter((nav) => !page.inView(nav));
    const navNames = siteNavs.map((nav) => page.nameOf(nav));
    if (navNames.some((name) => !name) || new Set(navNames).size !== navNames.length) f('every site <nav> needs a distinct accessible name');
    for (const nav of page.all('nav').filter((element) => page.inView(element))) if (!page.nameOf(nav)) f(`<nav> on line ${nav.line} inside a recorded view has no accessible name`);
    const firstLink = page.all('a')[0];
    if (!firstLink || firstLink.attrs.get('href') !== '#main' || !hasClass(firstLink, 'skip-link')) f('the first link must be the skip link to #main');
    const brand = page.all('a').find((a) => hasClass(a, 'brand'));
    if (!brand || brand.attrs.get('href') !== '/' || !brand.ancestors.includes(siteHeaders[0]) || normalize(doc.text(brand)) !== SITE_NAME) f('the header needs the site name linking home');

    // Primary navigation: Tutorial, Examples, Reference and Setup in order. The current
    // page is marked "page"; on tutorial pages below /learn/, the Tutorial entry is marked as
    // the current section. The site name is marked on the home page.
    const inPrimaryNav = (element) => element.ancestors.some((a) => a.name === 'nav' && a.attrs.get('aria-label') === 'Primary');
    const primaryLinks = page.all('a').filter(inPrimaryNav);
    if (primaryLinks.map((a) => a.attrs.get('href')).join(' ') !== navRoutes.map((route) => route.path).join(' ')) f('the primary navigation must list Tutorial, Examples, Reference and Setup in order');
    if (primaryLinks.map((a) => normalize(doc.text(a))).join('|') !== PRIMARY_LABELS.join('|')) f(`the primary navigation labels must be ${PRIMARY_LABELS.join(', ')}`);
    // Current-page marking concerns the site's navigation; a recorded view keeps the reader's
    // own marking of its selected step or tab.
    const currentPage = doc.elements.filter((element) => element.attrs.get('aria-current') === 'page' && !page.inView(element));
    const currentOther = doc.elements.filter((element) => element.attrs.has('aria-current') && element.attrs.get('aria-current') !== 'page' && !page.inView(element));
    if (currentPage.some((element) => element.name !== 'a' || element.attrs.get('href') !== page.path)) f('aria-current="page" may only mark links to this page');
    const primaryCurrent = primaryLinks.filter((a) => a.attrs.has('aria-current'));
    if (!page.path) {
      if (currentPage.length || currentOther.length) f('the 404 page must not mark a navigation entry as current');
    } else if (page.path === '/') {
      if (primaryCurrent.length || brand?.attrs.get('aria-current') !== 'page') f('on the home page only the site name is marked as the current page');
    } else if (page.entry?.section) {
      if (primaryCurrent.length !== 1 || primaryCurrent[0].attrs.get('href') !== page.entry.section || primaryCurrent[0].attrs.get('aria-current') !== 'true') f(`the ${page.entry.section} entry must be marked as the current section (aria-current="true")`);
      if (currentPage.length) f('a page outside the primary navigation marks no link as the current page');
    } else if (page.tutorial && page.path !== '/learn/') {
      if (primaryCurrent.length !== 1 || primaryCurrent[0].attrs.get('href') !== '/learn/' || primaryCurrent[0].attrs.get('aria-current') !== 'true') f('the Tutorial entry must be marked as the current section (aria-current="true")');
      if (currentPage.length !== 1) f(`the tutorial navigation must mark ${page.path} with aria-current="page"`);
    } else if (primaryCurrent.length !== 1 || primaryCurrent[0].attrs.get('href') !== page.path || primaryCurrent[0].attrs.get('aria-current') !== 'page') {
      f(`the primary navigation must mark ${page.path}, and only it, with aria-current="page"`);
    }
    if (page.path !== '/' && brand?.attrs.has('aria-current')) f('the site name is marked current only on the home page');
    if (currentOther.some((element) => !primaryCurrent.includes(element))) f('only the primary navigation may mark a current section');

    // The page outline. Headings inside a recorded view belong to the reader's own markup.
    const headings = doc.elements.filter((element) => /^h[1-6]$/.test(element.name) && !page.inView(element));
    if (headings.filter((heading) => heading.name === 'h1').length !== 1 || headings[0]?.name !== 'h1') f('needs exactly one <h1>, as the first heading');
    let previous = 0;
    for (const heading of headings) {
      const level = Number(heading.name[1]);
      const text = normalize(doc.text(heading));
      if (!text) f(`empty <${heading.name}> on line ${heading.line}`);
      if (level > previous + 1) f(`<${heading.name}> "${text}" skips a heading level`);
      previous = level;
    }

    for (const element of doc.elements) {
      const at = `<${element.name}> on line ${element.line}`;
      if (FORBIDDEN.has(element.name)) f(`${at} is not allowed on this static site`);
      for (const [name] of element.attrs) {
        if (name === 'style') f(`${at}: style attribute (the CSP blocks inline styles)`);
        if (name.startsWith('on')) f(`${at}: event handler attribute ${name}`);
      }
      if (element.name === 'img' && !element.attrs.has('alt')) f(`${at}: missing alt`);
      if (element.name === 'img' && !['width', 'height'].every((attr) => /^[1-9][0-9]*$/.test(element.attrs.get(attr) ?? ''))) f(`${at}: needs integer width and height attributes`);
      if (element.name === 'a') {
        const images = doc.elements.filter((x) => x.name === 'img' && x.ancestors.includes(element));
        const accessibleName = normalize(doc.text(element)) || element.attrs.get('aria-label') || images.map((img) => img.attrs.get('alt')).join('');
        if (!element.attrs.get('href')) f(`${at}: link without href`);
        if (!accessibleName) f(`${at}: link without text`);
        if (element.attrs.has('target')) f(`${at}: links open in the same tab`);
      }
      // The rules below govern the site's own markup; a recorded view keeps the reader's.
      if (page.inView(element)) continue;
      if (element.name === 'pre' && element.attrs.get('tabindex') !== '0') f(`${at}: needs tabindex="0" so keyboard users can scroll it`);
      if (element.name === 'pre' && (!['group', 'region'].includes(element.attrs.get('role')) || !normalize(element.attrs.get('aria-label') ?? ''))) f(`${at}: a focusable listing needs role="group" and an aria-label naming its source`);
      if (element.name === 'details') {
        const first = page.children(element)[0];
        if (first?.name !== 'summary' || !normalize(doc.text(first))) f(`${at}: must start with a labelled <summary>`);
        if (page.children(element).length < 2) f(`${at}: has no content besides its summary`);
      }
      if (element.name === 'table') {
        const captioned = doc.elements.some((x) => x.name === 'caption' && x.parent === element && normalize(doc.text(x)));
        if (!captioned && !page.nameOf(element)) f(`${at}: needs a <caption> or an aria-labelledby heading`);
        if (!hasClass(element, 'stack-table')) f(`${at}: tables use class="stack-table" so they stack on narrow screens`);
      }
      if (element.name === 'th') {
        const scope = element.ancestors.some((a) => a.name === 'thead') ? 'col' : 'row';
        if (element.attrs.get('scope') !== scope) f(`${at}: needs scope="${scope}"`);
      }
      if (element.name === 'td' && element.ancestors.some((a) => a.name === 'table' && hasClass(a, 'stack-table')) && !element.attrs.get('data-label')) {
        f(`${at}: stacked-table cells need data-label`);
      }
    }
    checkPageDirectives(source, usedViews).forEach(f);
  }
  return `${pages.length} pages: balanced tags, valid nesting, unique ids, approved titles and descriptions, landmarks, headings, current-page marking`;
});

await group('links, anchors and downloads', async (fail) => {
  let internal = 0;
  let fragments = 0;
  let downloads = 0;
  const external = new Set();
  const linked = new Set();
  const linkedPages = new Set();
  const downloadOutputs = new Set(DOWNLOADS.map(({ output }) => output));
  const resolveInternal = (pathname) => {
    if (pathname.endsWith('/')) {
      const file = `${pathname.slice(1)}index.html`;
      return fileSet.has(file) ? { file } : { error: 'no such page' };
    }
    const file = pathname.slice(1);
    if (fileSet.has(`${file}/index.html`)) return { error: `add the trailing slash (${pathname}/) to avoid a redirect` };
    if (file.endsWith('.html')) return { error: 'link to the route, not to its .html file' };
    if (file === '_headers') return { error: '_headers is hosting configuration and is not served' };
    return fileSet.has(file) ? { file } : { error: 'no such file in dist/' };
  };
  for (const page of pages) {
    for (const element of page.doc.elements) {
      for (const [attr, value] of urlsOf(element)) {
        const at = `${page.file} line ${element.line}: ${attr}="${value}"`;
        if (element.name === 'link' && element.attrs.get('rel') === 'canonical') continue; // checked with the page head
        if (value.startsWith('#')) {
          fragments += 1;
          if (!page.ids.has(value.slice(1))) fail(`${at}: no element with that id`);
          continue;
        }
        if (value.startsWith('https://')) {
          if (!EXTERNAL_LINKS.has(value)) fail(`${at}: external URL is not in the allowlist`);
          else if (element.name !== 'a') fail(`${at}: external resources may be linked but never loaded`);
          external.add(value);
          continue;
        }
        if (!value.startsWith('/') || value.startsWith('//')) {
          fail(`${at}: use a root-relative internal URL or an allowlisted https link`);
          continue;
        }
        internal += 1;
        const [target, fragment] = value.split('#');
        if (target.includes('?')) fail(`${at}: query strings are not used`);
        const resolved = resolveInternal(target);
        if (resolved.error) {
          fail(`${at}: ${resolved.error}`);
          continue;
        }
        linked.add(resolved.file);
        if (pageByFile.has(resolved.file) && resolved.file !== page.file) linkedPages.add(resolved.file);
        if (downloadOutputs.has(resolved.file)) downloads += 1;
        if (element.attrs.has('download') && !downloadOutputs.has(resolved.file)) fail(`${at}: download links are only for the published sources and guides`);
        if (fragment !== undefined) {
          fragments += 1;
          const targetPage = pageByFile.get(resolved.file);
          if (!targetPage) fail(`${at}: fragment on a file that is not a page`);
          else if (!targetPage.ids.has(fragment)) fail(`${at}: ${resolved.file} has no id "${fragment}"`);
        }
      }
    }
  }
  // Every published download and page must be reachable from another page.
  for (const output of downloadOutputs) if (!linked.has(output)) fail(`no page links to /${output}`);
  for (const page of pages) if (page.path && !linkedPages.has(page.file)) fail(`no other page links to ${page.path}`);
  // Links inside the published guides point back into the site; they must resolve too.
  for (const { output } of DOWNLOADS.filter((d) => d.output.endsWith('.md'))) {
    const text = await readFile(path.join(DIST, output), 'utf8');
    for (const [, href] of text.matchAll(/\]\((\/[^)\s]*)\)/g)) {
      const [target, fragment] = href.split('#');
      const resolved = resolveInternal(target);
      if (resolved.error) fail(`${output}: link ${href}: ${resolved.error}`);
      else if (fragment !== undefined && !pageByFile.get(resolved.file)?.ids.has(fragment)) fail(`${output}: link ${href}: no such anchor`);
    }
  }
  return `${internal} internal links (${downloads} to downloads), ${fragments} fragment links, ${external.size} allowlisted external destinations; every page and download is linked; guide links resolve`;
});

await group('source bytes and listings', async (fail) => {
  for (const { source, output, sha256: pinned } of DOWNLOADS) {
    const original = await readFile(path.join(ROOT, source));
    const published = await readFile(path.join(DIST, output));
    if (sha256(original) !== pinned) fail(`${source} no longer matches its pinned SHA-256 (now ${sha256(original)}); update the pin deliberately in scripts/site.mjs`);
    if (!published.equals(original)) fail(`dist/${output} differs from ${source}`);
  }
  let listings = 0;
  let excerpts = 0;
  let viewSources = 0;
  for (const page of pages) {
    for (const code of page.all('code').filter((element) => element.attrs.has('data-source'))) {
      listings += 1;
      const name = code.attrs.get('data-source');
      const at = `${page.file} line ${code.line}`;
      if (code.parent?.name !== 'pre') fail(`${at}: a source listing must be <pre><code>`);
      if (!leanText.has(name)) {
        fail(`${at}: unknown data-source "${name}"`);
        continue;
      }
      let expected = leanText.get(name);
      const lines = code.attrs.get('data-lines');
      if (lines) {
        excerpts += 1;
        const [from, to] = lines.split('-').map(Number);
        expected = excerptLines(expected, from, to);
      }
      if (page.doc.text(code) !== expected) fail(`${at}: displayed ${name}${lines ? ` lines ${lines}` : ''} differs from the file`);
    }
    // The source beside a recorded view is exactly what the reader analysed. A lesson may
    // also show the statement above the figure; that block must repeat it exactly (apart from
    // a final newline) and the view must appear on the same page.
    for (const code of page.all('code').filter((element) => element.attrs.has('data-view-source'))) {
      viewSources += 1;
      const id = code.attrs.get('data-view-source');
      const view = usedViews.get(id) ?? usedCaptures.get(id);
      const at = `${page.file} line ${code.line}`;
      if (code.parent?.name !== 'pre') fail(`${at}: a source listing must be <pre><code>`);
      if (!view) {
        fail(`${at}: data-view-source "${id}" names no view used by the build`);
        continue;
      }
      const inFigure = code.ancestors.some((a) => a.attrs.get('id') === `view-${id}` || a.attrs.get('id') === `capture-${id}`);
      if (inFigure && page.doc.text(code) !== view.sourceText) fail(`${at}: the source shown in the figure of ${id} differs from ${view.sourcePath}`);
      if (!inFigure && !sameSource(page.doc.text(code), view.sourceText)) fail(`${at}: the statement shown for ${id} differs from ${view.sourcePath}`);
      if (!inFigure && !page.ids.has(`view-${id}`) && !page.ids.has(`capture-${id}`)) fail(`${at}: the statement is marked as the source of ${id}, which this page does not show`);
    }
    for (const figure of page.figures.filter((element) => (element.attrs.get('id') ?? '').startsWith('view-'))) {
      const id = figure.attrs.get('id').slice(5);
      if (!page.within(figure).some((element) => element.attrs.get('data-view-source') === id)) fail(`${page.file} line ${figure.line}: the figure of ${id} must hold its own source listing`);
    }
    // Lean code that is not taken from a published file is reported for review.
    for (const code of page.all('code').filter((element) => hasClass(element, 'language-lean') && !element.attrs.has('data-source') && !element.attrs.has('data-view-source') && !element.attrs.has('data-expressions-of'))) {
      warnings.push(`${page.file} line ${code.line}: Lean code is not a whole published file or an exact excerpt of one`);
    }
    // Term snippets: line i of the code must appear verbatim in the i-th named file.
    for (const code of page.all('code').filter((element) => element.attrs.has('data-expressions-of'))) {
      const names = code.attrs.get('data-expressions-of').split(/\s+/).filter(Boolean);
      const lines = page.doc.text(code).replace(/\n$/, '').split('\n');
      if (lines.length !== names.length) fail(`${page.file} line ${code.line}: ${lines.length} lines for ${names.length} named files`);
      lines.forEach((line, i) => {
        if (!line.trim() || !leanText.get(names[i])?.includes(line)) fail(`${page.file} line ${code.line}: "${line}" is not taken verbatim from ${names[i] ?? 'a named file'}`);
      });
    }
  }
  return `${DOWNLOADS.length} downloads match their pinned SHA-256 byte for byte; ${listings} listings (${excerpts} line excerpts) and ${viewSources} recorded-view sources match their files`;
});

// A figure's provenance line: the kind of recording, "from a saved history" exactly when the
// batch says the recording was drawn from a saved record, the date and the Lean version.
function checkProvenance(page, figure, kind, date, lean, fail, { savedRecord = false, renderedFromSavedData = false, nativeCapture, recordedTheme, adaptiveTheme = false } = {}) {
  const at = `${page.file} line ${figure.line}`;
  const first = page.children(figure)[0];
  if (!first || first.name !== 'p' || !hasClass(first, 'dg-provenance')) {
    fail(`${at}: a recorded figure opens with its provenance line`);
    return;
  }
  const link = page.within(first).find((element) => element.name === 'a');
  if (!link || link.attrs.get('href') !== RECORDED_HELP || normalize(page.doc.text(link)) !== PROVENANCE[kind]) fail(`${at}: the provenance must link "${PROVENANCE[kind]}" to ${RECORDED_HELP}`);
  const times = page.within(first).filter((element) => element.name === 'time');
  const time = times[0];
  if (!time || time.attrs.get('datetime') !== date || normalize(page.doc.text(time)) !== formatDate(date)) fail(`${at}: the provenance must give the recording date ${date}`);
  if (!normalize(page.doc.text(first)).includes(`Lean ${lean}`)) fail(`${at}: the provenance must give the Lean version ${lean}`);
  const saved = normalize(page.doc.text(first)).includes(`· ${SAVED_HISTORY} ·`);
  if (saved !== savedRecord) fail(`${at}: the provenance ${savedRecord ? 'must say' : 'may say only for a saved record'} "${SAVED_HISTORY}"`);
  const text = normalize(page.doc.text(first));
  if (renderedFromSavedData) {
    if (!text.includes(`· Rendered ${formatDate(date)} ·`) || !text.includes(`Saved input: Lean ${lean}`) || !text.endsWith('Lean was not rerun.')) fail(`${at}: a saved-data rendering must label its rendering date, saved input's Lean version and absence of a new Lean run`);
    if (text.includes('· from saved results ·') !== !savedRecord) fail(`${at}: ordinary saved results and saved editor histories need distinct labels`);
    const theme = adaptiveTheme ? 'Adapts to page theme' : recordedTheme ? `${recordedTheme === 'light' ? 'Light' : 'Dark'} theme` : null;
    for (const label of ['Adapts to page theme', 'Light theme', 'Dark theme']) if (text.includes(`· ${label} ·`) !== (label === theme)) fail(`${at}: the provenance must describe the figure's actual theme behavior`);
    const day = (stamp) => new Date(stamp).toISOString().slice(0, 10);
    const expectedNativeTimes = nativeCapture === null ? [] : [nativeCapture.startedAt, ...(day(nativeCapture.startedAt) === day(nativeCapture.completedAt) ? [] : [nativeCapture.completedAt])];
    if (times.length !== expectedNativeTimes.length + 1 || expectedNativeTimes.some((stamp, index) => times[index + 1]?.attrs.get('datetime') !== stamp || normalize(page.doc.text(times[index + 1])) !== formatDate(day(stamp)))) fail(`${at}: the native capture dates must match the recorded range`);
    if (!text.includes('· Dates in UTC ·')) fail(`${at}: saved-data dates must identify their time zone`);
    if (text.includes('Native capture date unavailable') !== (nativeCapture === null)) fail(`${at}: an unavailable native capture date must be stated, never inferred`);
    if (nativeCapture !== null && !text.includes('· Native capture ')) fail(`${at}: native capture dates need an explicit label`);
  } else if (times.length !== 1 || /\bRendered\b|from saved results|Native capture|Saved input:|Lean was not rerun/.test(text)) fail(`${at}: a legacy recording must retain its original provenance wording`);
}

// A figure's own copy of its source (a recorded view's, or a screenshot's that has one) follows
// the provenance line and equals the source file. It sits in a closed disclosure labelled
// "Source" exactly when the same statement appears earlier in this section (after the nearest
// preceding h2 or h3, in a listing outside hints, answers and figures); otherwise a short source
// is shown open. It is never left out.
function checkFigureSource(page, figure, children, view, at, fail) {
  const source = children[1];
  const short = view.sourceText.replace(/\n$/, '').split('\n').length <= 12;
  const outside = (element) => !page.inFigure(element) && !page.inView(element) && !element.ancestors.some((a) => a.name === 'details');
  const heading = page.doc.elements.filter((element) => /^h[23]$/.test(element.name) && outside(element) && element.start < figure.start).at(-1);
  const earlier = page.doc.elements.some((element) => element.name === 'code' && element.parent?.name === 'pre' && outside(element)
    && element.start > (heading?.start ?? 0) && element.start < figure.start && sameSource(page.doc.text(element), view.sourceText));
  const listing = source ? page.within(source).find((element) => element.attrs.get('data-view-source') === view.id) : null;
  if (!source || !hasClass(source, 'dg-source') || !listing) fail(`${at}: the exact source follows the provenance line`);
  else if (earlier) {
    const summary = page.children(source).find((element) => element.name === 'summary');
    if (source.name !== 'details' || source.attrs.has('open') || normalize(summary ? page.doc.text(summary) : '') !== 'Source') fail(`${at}: the statement appears earlier in this section, so the figure keeps its source in a closed disclosure labelled "Source"`);
  } else if (source.name === 'details' && short) fail(`${at}: the source of ${view.id} is collapsed, but the same statement does not appear earlier in this section`);
  if (listing && page.doc.text(listing) !== view.sourceText) fail(`${at}: the figure's copy of the source differs from ${view.sourcePath}`);
}

await group('recorded views', async (fail) => {
  let viewCount = 0;
  let imageCount = 0;
  let captureCount = 0;
  const shown = { views: new Set(), images: new Set(), captures: new Set() };
  for (const page of pages) {
    for (const figure of page.figures) {
      const at = `${page.file} line ${figure.line}`;
      const id = figure.attrs.get('id') ?? '';
      const children = page.children(figure);
      const caption = children.at(-1);
      if (caption?.name !== 'figcaption' || !normalize(page.doc.text(caption))) fail(`${at}: a recorded figure ends with a visible caption`);
      if (id.startsWith('view-')) {
        viewCount += 1;
        const view = usedViews.get(id.slice(5));
        if (!view) {
          fail(`${at}: ${id} is not a view the build placed`);
          continue;
        }
        shown.views.add(view.id);
        checkProvenance(page, figure, view.excerpt ? 'excerpt' : 'view', view.batch.date, view.batch.lean, fail, { savedRecord: view.savedRecord === true, renderedFromSavedData: view.batch.renderedFromSavedData === true, nativeCapture: view.nativeCapture, recordedTheme: view.batch.recordedTheme, adaptiveTheme: view.batch.adaptiveTheme === true });
        checkFigureSource(page, figure, children, view, at, fail);
        const scroll = children.find((element) => hasClass(element, 'dg-scroll'));
        // An excerpt's frame has dashed top and bottom edges (dg-figure-excerpt), and a visually
        // hidden note before the view says that the rest of the panel is left out.
        const excerptNote = children.find((element) => element.name === 'p' && hasClass(element, 'visually-hidden'));
        if (view.excerpt) {
          if (!hasClass(figure, 'dg-figure-excerpt') || !excerptNote || normalize(page.doc.text(excerptNote)) !== EXCERPT_NOTE || !scroll || excerptNote.start > scroll.start) fail(`${at}: an excerpt figure is marked dg-figure-excerpt and says "${EXCERPT_NOTE}" before the view`);
        } else if (hasClass(figure, 'dg-figure-excerpt') || excerptNote) fail(`${at}: only an excerpt is marked as one`);
        if (!scroll || scroll.attrs.get('role') !== 'region' || scroll.attrs.get('tabindex') !== '0' || !normalize(scroll.attrs.get('aria-label') ?? '')) {
          fail(`${at}: the view sits in a keyboard-focusable scroll region with an accessible name`);
          continue;
        }
        const canvas = page.children(scroll);
        const root = canvas.length === 1 && hasClass(canvas[0], 'dg-canvas') ? page.children(canvas[0]) : [];
        if (root.length !== 1 || !hasClass(root[0], 'dg-view') || root[0].attrs.get('data-view-id') !== view.id) fail(`${at}: the scroll region holds one .dg-canvas holding exactly the view`);
        if (!page.source.includes(fragmentBody(view))) fail(`${at}: the published page does not contain ${view.fragmentPath} unchanged`);
      } else if (id.startsWith('image-')) {
        imageCount += 1;
        const image = usedImages.get(id.slice(6));
        if (!image) {
          fail(`${at}: ${id} is not a reader image the build placed`);
          continue;
        }
        shown.images.add(image.name);
        checkProvenance(page, figure, 'image', READER_IMAGE_BATCH.recorded, READER_IMAGE_BATCH.lean, fail);
        const img = page.within(figure).filter((element) => element.name === 'img');
        const src = `/${image.output}`;
        if (img.length !== 1 || img[0].attrs.get('src') !== src) fail(`${at}: shows exactly ${src}`);
        else {
          if (img[0].attrs.get('width') !== String(image.width) || img[0].attrs.get('height') !== String(image.height)) fail(`${at}: declares ${image.width}×${image.height}`);
          if (normalize(img[0].attrs.get('alt') ?? '') !== normalize(image.alt)) fail(`${at}: needs its approved alt text`);
        }
        const codes = page.within(figure).filter((element) => element.attrs.has('data-source'));
        if (codes.length !== 1 || codes[0].attrs.get('data-source') !== image.lean || codes[0].attrs.has('data-lines')) fail(`${at}: shows ${image.lean} in full`);
        if (!page.within(figure).some((a) => a.name === 'a' && a.attrs.get('href') === image.sourceHref && a.attrs.has('download'))) fail(`${at}: offers ${image.lean} for download`);
        if (!page.within(caption ?? figure).some((a) => a.name === 'a' && a.attrs.get('href') === src && normalize(page.doc.text(a)))) fail(`${at}: the caption links to the full-size image`);
        const captionText = normalize(caption ? page.doc.text(caption) : '');
        if (!captionText.includes(normalize(image.caption))) fail(`${at}: the caption must keep the approved caption`);
      } else if (id.startsWith('capture-')) {
        captureCount += 1;
        const view = usedCaptures.get(id.slice(8));
        if (!view) {
          fail(`${at}: ${id} is not a capture the build placed`);
          continue;
        }
        shown.captures.add(view.id);
        checkProvenance(page, figure, 'capture', view.batch.date, view.batch.lean, fail, { savedRecord: view.savedRecord === true, renderedFromSavedData: view.batch.renderedFromSavedData === true, nativeCapture: view.nativeCapture, recordedTheme: view.batch.recordedTheme });
        if (view.sourceText !== undefined) checkFigureSource(page, figure, children, view, at, fail);
        const img = page.within(figure).filter((element) => element.name === 'img');
        if (img.length !== 1 || img[0].attrs.get('src') !== `/${view.contextOutput}` || img[0].attrs.get('width') !== String(view.context.width / 2) || img[0].attrs.get('height') !== String(view.context.height / 2)) {
          fail(`${at}: shows /${view.contextOutput} at half its pixel size (a device-scale-2 capture)`);
        }
        const frame = img[0]?.parent;
        if (!frame || !hasClass(frame, 'dg-scroll') || frame.attrs.get('role') !== 'region' || frame.attrs.get('tabindex') !== '0' || !normalize(frame.attrs.get('aria-label') ?? '')) {
          fail(`${at}: the screenshot sits at its own size in a keyboard-focusable scroll region with an accessible name`);
        }
        if (!page.within(caption ?? figure).some((a) => a.name === 'a' && a.attrs.get('href') === `/${view.contextOutput}`)) fail(`${at}: the caption links to the screenshot on its own`);
      } else fail(`${at}: a recorded figure needs a view-, image- or capture- id`);
    }
    // Recorded markup appears only inside its figure.
    for (const root of page.doc.elements.filter((element) => hasClass(element, 'dg-view') && !element.ancestors.some((a) => hasClass(a, 'dg-view')))) {
      if (!root.ancestors.some((a) => hasClass(a, 'dg-canvas')) || !root.ancestors.some((a) => hasClass(a, 'dg-figure'))) fail(`${page.file} line ${root.line}: recorded view markup outside a recorded figure`);
    }
    // Every page says that its figures are recorded and that the site runs no Lean.
    const footer = page.all('footer').find((element) => !element.ancestors.includes(page.main));
    if (!/This site does not run Lean/.test(normalize(footer ? page.doc.text(footer) : ''))) fail(`${page.file}: the footer must say that the site does not run Lean`);
  }
  for (const id of usedViews.keys()) if (!shown.views.has(id)) fail(`view ${id} was placed by the build but no figure shows it`);
  for (const name of usedImages.keys()) if (!shown.images.has(name)) fail(`image ${name} was placed by the build but no figure shows it`);
  for (const id of usedCaptures.keys()) if (!shown.captures.has(id)) fail(`capture ${id} was placed by the build but no figure shows it`);

  // The published stylesheet is site.css, then each used batch's own styles (comments removed,
  // every selector confined to that batch's figures), then the generated widths.
  const css = await readFile(path.join(DIST, 'assets', built.stylesheet), 'utf8');
  const sizing = sizingRules(built.used.views);
  if (css !== publishedStylesheet(await readFile(path.join(ROOT, STYLESHEET), 'utf8'), built.batches, built.used.views)) fail('the published stylesheet must be site.css, the used batches\' scoped styles, then the generated diagram widths');
  if (sizing) for (const error of validateViewCss(sizing, 'generated diagram widths').errors) fail(error);
  // No animation name in the published stylesheet can collide with another batch or the site.
  for (const match of css.matchAll(/@(?:-webkit-)?keyframes\s+([\w-]+)/g)) if (!match[1].startsWith('dg-')) fail(`published @keyframes ${match[1]} does not start with dg-`);
  const importRecord = JSON.parse(await readFile(path.join(ROOT, VIEWS_MANIFEST), 'utf8'));
  for (const batch of built.batches) {
    const prefix = `:where([data-dg-batch="${batch.name}"]) > `;
    // The import recorded what publishing does with the batch's @keyframes; recompute it from
    // the pinned stylesheet and every fragment of the batch.
    const recorded = importRecord.batches.find((b) => b.batch === batch.name)?.keyframes;
    const plan = keyframePlan(batch.css, batch.name, batch.views.filter((view) => view.classes).map((view) => view.classes));
    if (!samePlan(recorded, plan)) fail(`${batch.name}: the recorded keyframes plan ${JSON.stringify(recorded)} is not what its stylesheet and fragments give (${JSON.stringify(plan)})`);
    const scoped = scopeViewCss(batch.css, batch.name, plan);
    for (const match of scoped.matchAll(/(?:^|[{}])\s*([^{}@]+)\{/g)) {
      for (const selector of match[1].split(/,(?![^(]*\))/)) {
        const rest = selector.trim();
        if (/^(?:from|to|\d+%)$/.test(rest)) continue;
        if (!rest.startsWith(prefix) || !/^(?:\.dg-view(?![\w-])|:(?:where|is)\(\s*\.dg-view\s*\))/.test(rest.slice(prefix.length))) fail(`published ${batch.name} selector "${rest.slice(0, 80)}" is not confined to its batch's figures`);
      }
    }
    if (/\/\*/.test(scoped)) fail(`published ${batch.name} styles keep a comment`);
    // Animation names are the batch's own: the published @keyframes are exactly the plan's
    // renamed ones, each prefixed dg-<batch>-, dropped ones are gone, and every name an
    // animation or animation-name declaration uses is one of them.
    const published = [...scoped.matchAll(/@(?:-webkit-)?keyframes\s+([\w-]+)/g)].map((match) => match[1]);
    const kept = new Set(Object.values(plan.renamed));
    for (const name of published) {
      if (!name.startsWith(`dg-${batch.name}-`)) fail(`published ${batch.name} @keyframes ${name} is not prefixed dg-${batch.name}-`);
      else if (!kept.has(name)) fail(`published ${batch.name} @keyframes ${name} is not in the recorded plan`);
    }
    for (const name of kept) if (!published.includes(name)) fail(`published ${batch.name} styles lack @keyframes ${name}`);
    for (const name of plan.dropped) if (published.includes(name) || published.includes(`dg-${batch.name}-${name}`)) fail(`published ${batch.name} styles keep the dropped @keyframes ${name}`);
    for (const match of scoped.matchAll(/(?:^|[{;])\s*((?:-webkit-|-moz-|-o-)?animation(?:-name)?)\s*:\s*([^;}]*)/gim)) {
      for (const name of animationNamesIn(match[2])) if (!kept.has(name)) fail(`published ${batch.name} ${match[1]} uses "${name}", which is not one of the batch's published @keyframes`);
    }
    for (const error of validateViewCss(adaptationRules(batch.name).replace(/:where\(\[data-dg-batch="[^"]+"\]\) > /g, ''), 'recording adaptations').errors) fail(error);
  }
  // Each figure's canvas names the set its view came from.
  for (const page of pages) {
    for (const canvas of page.doc.elements.filter((element) => hasClass(element, 'dg-canvas'))) {
      const root = page.children(canvas)[0];
      const view = usedViews.get(root?.attrs.get('data-view-id'));
      if (view && canvas.attrs.get('data-dg-batch') !== view.batch.name) fail(`${page.file} line ${canvas.line}: the canvas of ${view.id} must carry data-dg-batch="${view.batch.name}"`);
      if (view && canvas.attrs.get('data-dg-theme') !== (view.batch.adaptiveTheme === true ? 'adaptive' : view.batch.recordedTheme)) fail(`${page.file} line ${canvas.line}: the canvas of ${view.id} must carry its explicitly recorded or adaptive theme`);
      // The canvas has the background the view's family has in the app.
      if (view && (canvas.attrs.get('data-dg-surface') ?? null) !== surfaceOf(view.kind)) fail(`${page.file} line ${canvas.line}: the canvas of ${view.id} (${view.kind}) must ${surfaceOf(view.kind) ? `carry data-dg-surface="${surfaceOf(view.kind)}"` : 'keep the page background'}`);
    }
  }
  for (const batch of built.batches) if (sha256(batch.cssBytes) !== JSON.parse(await readFile(path.join(ROOT, VIEWS_MANIFEST), 'utf8')).batches.find((b) => b.batch === batch.name)?.stylesheet?.sha256) fail(`${batch.cssPath} no longer matches its pin`);
  // Views in the allowlist that no page uses are reported, not failed.
  for (const view of built.views.views.values()) {
    if (!usedViews.has(view.id) && !usedCaptures.has(view.id)) warnings.push(`recorded ${view.captureOnly ? 'screenshot' : 'view'} ${view.id} (${view.batch.name}) is allowlisted but no page uses it`);
  }
  // Reader images that no page places are not published.
  for (const image of IMAGES) if (!usedImages.has(image.name)) warnings.push(`reader image ${image.name} is not placed on any page and is not published`);
  return `${viewCount} recorded views, ${imageCount} reader images and ${captureCount} captures, each with provenance, date, Lean version, exact source and caption; fragments published unchanged in named scroll regions; stylesheet = site.css + ${built.batches.length} batch stylesheet(s)`;
});

await group('recorded-view validator self-test', async (fail) => {
  const { failures, cases } = runViewSelfTest(ROOT);
  failures.forEach(fail);
  return `the fixture batch imports, loads and renders; ${cases} broken fragments and stylesheets are each rejected for the expected reason; changed files fail their pins`;
});

await group('static math asset and fragment self-test', async (fail) => {
  const { failures, cases } = runMathSelfTest(ROOT);
  failures.forEach(fail);
  for (const asset of built.used.mathAssets) if (sha256(await readFile(path.join(DIST, asset.output))) !== asset.sha256) fail(`${asset.output}: published math asset differs from its pin`);
  return `${cases} math profile, resource and import checks; published font/license bytes pinned`;
});

await group('final-page directive self-test', async (fail) => {
  const { failures, cases } = runPageDirectiveSelfTest(ROOT);
  failures.forEach(fail);
  return `${cases} exact-recording TeX exemptions and unreplaced-directive checks`;
});

await group('saved-data provenance self-test', async (fail) => {
  const { failures, cases } = runProvenanceSelfTest(ROOT);
  failures.forEach(fail);
  return `${cases} metadata, date, import-field, legacy and rendering checks; no native captures created`;
});

// What a Markdown file should show once rendered, from marked's own lexer: heading and
// text blocks in order, code blocks, <details> answers with the text inside each, images,
// and the figures its directives place.
function markdownExpectations(markdown) {
  const out = { headings: [], texts: [], codes: [], details: [], images: [], figures: [] };
  let open = null;
  const inline = (tokens = []) => tokens.map((token) => {
    if (token.type === 'image') {
      out.images.push({ alt: token.text, href: token.href });
      return '';
    }
    if (token.type === 'br') return ' ';
    if (token.tokens) return inline(token.tokens);
    return token.text ?? '';
  }).join('');
  const text = (value) => {
    const normalized = normalize(value);
    if (!normalized) return;
    out.texts.push(normalized);
    open?.texts.push(normalized);
  };
  const blocks = (tokens) => {
    for (const token of tokens) {
      if (token.type === 'heading') {
        const value = normalize(inline(token.tokens));
        out.headings.push({ depth: token.depth, text: value });
        text(value);
      } else if (token.type === 'paragraph') {
        const directive = DIRECTIVE.exec(token.text.trim());
        if (directive) out.figures.push(`${directive[1]}-${directive[2]}`);
        else text(inline(token.tokens));
      } else if (token.type === 'text') text(token.tokens ? inline(token.tokens) : token.text);
      else if (token.type === 'list') for (const item of token.items) blocks(item.tokens);
      else if (token.type === 'blockquote') blocks(token.tokens);
      else if (token.type === 'table') for (const cell of [...token.header, ...token.rows.flat()]) text(inline(cell.tokens));
      else if (token.type === 'code') {
        out.codes.push(`${token.text}\n`);
        if (open) open.codes += 1;
      } else if (token.type === 'html') {
        const raw = token.text.trim();
        if (/^<!--\s*description:/.test(raw)) continue;
        if (raw.startsWith('<details>')) {
          open = { summary: normalize(/<summary>([^<>]+)<\/summary>/.exec(raw)?.[1] ?? ''), texts: [], codes: 0 };
          out.details.push(open);
        } else if (raw === '</details>') open = null;
        else out.texts.push(`[raw HTML ${raw.slice(0, 30)}]`);
      } else if (!['space', 'hr', 'def'].includes(token.type)) out.texts.push(`[unhandled ${token.type} block]`);
    }
  };
  blocks(new Lexer({ gfm: true }).lex(markdown.replace(DESCRIPTION_COMMENT, '')));
  return out;
}

// The published route of a tutorial link, resolved independently of the build.
function expectedHref(href, source) {
  if (/^[a-z][a-z0-9+.-]*:/i.test(href) || href.startsWith('#')) return href;
  const [target, fragment] = href.split('#');
  const route = TUTORIAL_LINKS.get(path.posix.normalize(path.posix.join(path.posix.dirname(source), target)));
  return route && (fragment === undefined ? route : `${route}#${fragment}`);
}

await group('tutorial rendering and navigation', async (fail) => {
  const counts = { headings: 0, texts: 0, codes: 0, details: 0, images: 0, figures: 0 };
  for (const page of tutorialPages) {
    const at = page.file;
    const expected = markdownExpectations(page.markdown);
    const article = page.all('article').find((element) => hasClass(element, 'doc'));
    if (!article) {
      fail(`${at}: the rendered lesson must sit in <article class="doc">`);
      continue;
    }
    // Figures placed by directives are checked with the recorded views.
    const inArticle = page.within(article).filter((element) => !page.inFigure(element));
    const figures = page.within(article).filter((element) => element.name === 'figure' && hasClass(element, 'dg-figure')).map((figure) => figure.attrs.get('id'));
    if (JSON.stringify(figures) !== JSON.stringify(expected.figures)) fail(`${at}: recorded figures ${figures.join(', ') || 'none'} do not match the directives ${expected.figures.join(', ') || 'none'}`);
    // Headings, in order, with the same levels and text.
    const headings = inArticle.filter((element) => /^h[1-6]$/.test(element.name)).map((element) => ({ depth: Number(element.name[1]), text: normalize(page.doc.text(element)) }));
    if (JSON.stringify(headings) !== JSON.stringify(expected.headings)) fail(`${at}: headings differ from ${page.entry.source}`);
    // Every text block, in order (the section list for narrow screens is navigation, not lesson text).
    const lessonText = normalize(page.children(article).filter((element) => !hasClass(element, 'page-toc') && !page.inFigure(element)).map((element) => page.doc.text(element)).join(' '));
    let cursor = 0;
    for (const fragment of expected.texts) {
      const found = lessonText.indexOf(fragment, cursor);
      if (found === -1) fail(`${at}: missing or out of order: "${fragment.slice(0, 90)}"`);
      else cursor = found + fragment.length;
    }
    // Code blocks, exactly and in order.
    const codes = inArticle.filter((element) => element.name === 'code' && element.parent?.name === 'pre').map((code) => page.doc.text(code));
    if (JSON.stringify(codes) !== JSON.stringify(expected.codes)) fail(`${at}: code blocks differ from ${page.entry.source}`);
    // Hints and worked answers: the same disclosures, each still holding its own text.
    const details = inArticle.filter((element) => element.name === 'details');
    if (details.length !== expected.details.length) fail(`${at}: ${details.length} disclosures rendered for ${expected.details.length} in the Markdown`);
    details.forEach((element, i) => {
      const want = expected.details[i];
      if (!want) return;
      const summary = page.children(element).find((child) => child.name === 'summary');
      if (normalize(summary ? page.doc.text(summary) : '') !== want.summary) fail(`${at}: disclosure ${i + 1} should be labelled "${want.summary}"`);
      const inside = normalize(page.doc.text(element));
      let position = 0;
      for (const fragment of want.texts) {
        const found = inside.indexOf(fragment, position);
        if (found === -1) fail(`${at}: disclosure ${i + 1} ("${want.summary}") lost "${fragment.slice(0, 70)}"`);
        else position = found + fragment.length;
      }
      if (page.within(element).filter((child) => child.name === 'pre').length !== want.codes) fail(`${at}: disclosure ${i + 1} should hold ${want.codes} code blocks`);
    });
    // Images: the same alt text, pointing at the published illustration.
    const images = inArticle.filter((element) => element.name === 'img');
    if (images.length !== expected.images.length) fail(`${at}: ${images.length} images rendered for ${expected.images.length} in the Markdown`);
    images.forEach((img, i) => {
      const want = expected.images[i];
      if (!want) return;
      if (normalize(img.attrs.get('alt') ?? '') !== normalize(want.alt)) fail(`${at}: image ${i + 1} alt text differs from the Markdown`);
      if (img.attrs.get('src') !== expectedHref(want.href, page.entry.source)) fail(`${at}: image ${i + 1} should load ${expectedHref(want.href, page.entry.source)}`);
    });
    // Links keep their text and lead to the mapped routes.
    const markdownLinks = [];
    const collect = (tokens = []) => tokens.forEach((token) => {
      if (token.type === 'link') markdownLinks.push(expectedHref(token.href, page.entry.source));
      collect(token.tokens);
      collect(token.items);
      if (token.type === 'table') [...token.header, ...token.rows.flat()].forEach((cell) => collect(cell.tokens));
    });
    collect(new Lexer({ gfm: true }).lex(page.markdown));
    const renderedLinks = inArticle.filter((element) => element.name === 'a' && !element.ancestors.some((a) => hasClass(a, 'page-toc'))).map((a) => a.attrs.get('href'));
    if (JSON.stringify(renderedLinks) !== JSON.stringify(markdownLinks)) fail(`${at}: links differ from the mapped Markdown links`);
    counts.headings += headings.length;
    counts.texts += expected.texts.length;
    counts.codes += codes.length;
    counts.details += details.length;
    counts.images += images.length;
    counts.figures += figures.length;

    // Meaning boundaries that apply to any lesson. A teaching illustration is followed by a
    // sentence saying it is not reader output; a listing that uses sorry, outside an answer,
    // is followed by an explanation of the sorryAx dependency.
    for (const img of images) {
      const paragraph = img.parent?.name === 'p' ? img.parent : null;
      const next = paragraph ? page.children(paragraph.parent)[page.children(paragraph.parent).indexOf(paragraph) + 1] : undefined;
      if (!next || !NOT_READER_OUTPUT.test(normalize(page.doc.text(next)))) fail(`${at}: the teaching illustration on line ${img.line} must be followed by a sentence saying it is not Definograph output`);
    }
    for (const pre of inArticle.filter((element) => element.name === 'pre' && !element.ancestors.some((a) => a.name === 'details'))) {
      if (!/(?<![\p{L}\p{N}_.'])sorry(?![\p{L}\p{N}_.'])/u.test(page.doc.text(pre))) continue;
      const next = page.children(pre.parent)[page.children(pre.parent).indexOf(pre) + 1];
      if (!next || next.name !== 'p' || !normalize(page.doc.text(next)).includes('sorryAx')) fail(`${at}: the listing on line ${pre.line} uses sorry; the paragraph directly after it must explain the sorryAx dependency`);
    }

    // Navigation: the tutorial sidebar lists every page in order and marks this one; its
    // section links, and the narrow-screen section list, follow this page's h2 headings.
    const sections = page.within(article).filter((element) => element.name === 'h2' && !page.inView(element)).map((element) => `#${element.attrs.get('id')}`);
    const sidebar = page.all('nav').find((nav) => page.nameOf(nav) === 'Tutorial contents');
    if (!sidebar) {
      fail(`${at}: needs the "Tutorial contents" navigation`);
    } else {
      const entries = page.within(sidebar).filter((a) => a.name === 'a' && hasClass(a.parent?.parent ?? a, 'sidebar-pages'));
      if (entries.map((a) => a.attrs.get('href')).join(' ') !== TUTORIAL.map((entry) => entry.path).join(' ')) fail(`${at}: the tutorial navigation must list every tutorial page in order`);
      if (entries.map((a) => normalize(page.doc.text(a))).join('|') !== tutorialPages.map(tutorialLabel).join('|')) fail(`${at}: tutorial navigation labels must be the page titles`);
      const marked = entries.filter((a) => a.attrs.get('aria-current') === 'page');
      if (marked.length !== 1 || marked[0].attrs.get('href') !== page.path) fail(`${at}: the tutorial navigation must mark this page as current`);
      const nested = page.within(sidebar).filter((a) => a.name === 'a' && a.ancestors.some((u) => hasClass(u, 'sidebar-sections'))).map((a) => a.attrs.get('href'));
      if (nested.join(' ') !== sections.join(' ')) fail(`${at}: the tutorial navigation must list this page's sections`);
    }
    const toc = page.all('nav').find((nav) => page.nameOf(nav) === 'On this page');
    const tocLinks = toc ? page.within(toc).filter((a) => a.name === 'a').map((a) => a.attrs.get('href')) : [];
    if (tocLinks.join(' ') !== sections.join(' ')) fail(`${at}: "On this page" must list the page's sections`);
    const index = tutorialPages.indexOf(page);
    const pager = page.all('nav').find((nav) => hasClass(nav, 'pager'));
    const pagerLinks = pager ? page.within(pager).filter((a) => a.name === 'a') : [];
    const wanted = [
      tutorialPages[index - 1] && { href: tutorialPages[index - 1].path, text: `Previous ${tutorialLabel(tutorialPages[index - 1])}` },
      tutorialPages[index + 1] && { href: tutorialPages[index + 1].path, text: `Next ${tutorialLabel(tutorialPages[index + 1])}` },
    ].filter(Boolean);
    const found = pagerLinks.map((a) => ({ href: a.attrs.get('href'), text: normalize(page.doc.text(a)) }));
    if (JSON.stringify(found) !== JSON.stringify(wanted)) fail(`${at}: previous and next links must lead to the neighbouring tutorial pages`);
  }

  // Teaching graphics: exact bytes, inert SVG, shown in the tutorial, never as a reader view.
  // A graphic no lesson shows is not published.
  for (const figure of ILLUSTRATIONS.filter((candidate) => !built.used.illustrations.some((used) => used.output === candidate.output))) {
    if (fileSet.has(figure.output)) fail(`/${figure.output} is published although no lesson shows it`);
    warnings.push(`${figure.source} is not shown by any lesson and is not published`);
  }
  for (const figure of built.used.illustrations) {
    const at = figure.source;
    if (!/^tutorial\/figures\/[a-z0-9-]+\.svg$/.test(figure.source) || figure.output !== `learn/figures/${basename(figure.source)}`) fail(`${at}: teaching graphics publish from tutorial/figures/ to learn/figures/`);
    const original = await readFile(path.join(ROOT, figure.source));
    if (sha256(original) !== figure.sha256) fail(`${at} no longer matches its pinned SHA-256 (now ${sha256(original)})`);
    if (!(await readFile(path.join(DIST, figure.output))).equals(original)) fail(`dist/${figure.output} differs from ${at}`);
    const svg = inspectSvg(original.toString('utf8'));
    for (const problem of svg.problems) fail(`${at}: contains ${problem}`);
    if (svg.width !== figure.width || svg.height !== figure.height) fail(`${at}: is ${svg.width}×${svg.height}, but the manifest says ${figure.width}×${figure.height}`);
    const uses = pages.flatMap((page) => page.all('img').filter((img) => img.attrs.get('src') === `/${figure.output}`).map((img) => ({ page, img })));
    if (!uses.length) fail(`/${figure.output} is published but no page shows it`);
    for (const { page, img } of uses) {
      if (!page.tutorial) fail(`${page.file}: teaching graphics belong to the tutorial`);
      if (img.attrs.get('width') !== String(figure.width) || img.attrs.get('height') !== String(figure.height)) fail(`${page.file}: /${figure.output} must declare ${figure.width}×${figure.height}`);
      if (page.inFigure(img)) fail(`${page.file}: a teaching graphic must not be presented as recorded output`);
    }
  }
  // The example notes link every tutorial Lean file.
  const notes = pageByPath.get('/learn/example-notes/');
  if (notes) {
    for (const { source, output } of DOWNLOADS.filter((download) => download.source.startsWith('tutorial/'))) {
      if (!notes.all('a').some((a) => a.attrs.get('href') === `/${output}`)) fail(`/learn/example-notes/ must link ${basename(source)}`);
    }
  }
  return `${tutorialPages.length} pages match their Markdown: ${counts.headings} headings, ${counts.texts} text blocks in order, ${counts.codes} code blocks, ${counts.details} hint and answer disclosures, ${counts.images} teaching graphics, ${counts.figures} recorded figures; sidebar, section lists and previous/next verified`;
});

await group('request boundary and privacy', async (fail) => {
  // Executable or fetching contexts: URL-bearing attributes and the stylesheet. Prose and
  // the downloadable guides may mention local addresses as instructions; they are not requests.
  const URL_ATTRIBUTES = new Set(['href', 'src', 'srcset', 'action', 'formaction', 'poster', 'data', 'background', 'cite', 'manifest', 'ping', 'longdesc', 'xlink:href']);
  const LOOPBACK = /localhost|127\.0\.0\.1|0\.0\.0\.0|\[::1\]/i;
  let requests = 0;
  for (const page of pages) {
    for (const element of page.doc.elements) {
      const values = [...element.attrs].filter(([name]) => URL_ATTRIBUTES.has(name) && name !== 'srcset').concat(urlsOf(element).filter(([name]) => name === 'srcset'));
      for (const [name, value] of values) {
        requests += 1;
        const at = `${page.file} line ${element.line}: ${name}="${value}"`;
        // In-document SVG references inside a recorded view (checked by the view rules).
        if (value.startsWith('#') && page.inView(element)) continue;
        const scheme = /^\s*([a-z][a-z0-9+.-]*):/i.exec(value)?.[1].toLowerCase();
        if (scheme && scheme !== 'https') fail(`${at}: ${scheme}: URLs are not used (no local, editor-host, script or data requests)`);
        if (LOOPBACK.test(value)) fail(`${at}: points at a local service`);
        if (/^\/api(\/|$)/i.test(value)) fail(`${at}: points at an API path; the site has none`);
      }
    }
  }
  const css = await readFile(path.join(DIST, 'assets', built.stylesheet), 'utf8');
  validatePublishedMathCss(css, built.batches).forEach(fail);
  for (const file of ['_headers', 'robots.txt', 'sitemap.xml']) {
    if (LOOPBACK.test(await readFile(path.join(DIST, file), 'utf8'))) fail(`dist/${file}: refers to a local service`);
  }
  // Private paths are checked everywhere, downloads, graphics and recorded views included.
  const textFiles = files.filter((file) => /\.(html|css|txt|xml|svg|md|lean)$/.test(file) || file === '_headers' || file === '_redirects');
  for (const file of textFiles) {
    const text = await readFile(path.join(DIST, file), 'utf8');
    for (const found of findPrivate(text, PRIVATE_PATHS)) fail(`dist/${file}: ${found}`);
    if (text.includes(ROOT)) fail(`dist/${file}: contains the local project path`);
  }
  // PNG metadata travels with the bytes, so a local path in it would be published.
  for (const file of files.filter((name) => name.endsWith('.png'))) {
    const png = readPng(await readFile(path.join(DIST, file)));
    const metadata = [...png.metadata.map(({ data }) => data.toString('latin1')), ...png.text.map(({ keyword, value }) => `${keyword} ${value}`)].join('\n');
    for (const found of findPrivate(metadata, PRIVATE_PATHS)) fail(`dist/${file}: PNG metadata contains a ${found}`);
    if (png.metadata.length) warnings.push(`dist/${file} carries PNG metadata (${[...new Set(png.metadata.map(({ type }) => type))].join(', ')}), published unchanged`);
  }
  if (files.some((file) => /\.(m?js|cjs|map|json|ts)$/i.test(file))) fail('dist/ must not contain scripts, source maps or data files');
  // Product revisions are local development builds that readers cannot fetch; no published
  // file may cite one. Tutorial pages (the tutorial author's text) are reported instead.
  const productIds = new Set([...built.views.batches.flatMap((batch) => [batch.commit, batch.product?.tree])].filter(Boolean));
  for (const file of textFiles) {
    const text = await readFile(path.join(DIST, file), 'utf8');
    for (const id of productIds) {
      if (!text.includes(id) && !text.includes(id.slice(0, 7))) continue;
      const tutorialPage = pages.some((page) => page.tutorial && page.file === file);
      const message = `dist/${file}: cites product revision ${id.slice(0, 12)}, which readers cannot fetch; describe it as a development build that has not been published`;
      if (tutorialPage) warnings.push(message);
      else fail(message);
    }
  }
  for (const page of pages) {
    for (const a of page.all('a')) {
      if (/\.(vsix|dmg|pkg|exe|msi|zip|tar|gz|tgz|deb|rpm|appimage)(?:$|[?#])/i.test(a.attrs.get('href') ?? '')) {
        fail(`${page.file} line ${a.line}: links to a downloadable package`);
      }
    }
  }
  // The only package is the build-time Markdown parser, pinned exactly in the lockfile.
  const pkg = JSON.parse(await readFile(path.join(ROOT, 'package.json'), 'utf8'));
  for (const key of ['dependencies', 'optionalDependencies', 'peerDependencies', 'bundleDependencies', 'bundledDependencies']) {
    if (pkg[key] && Object.keys(pkg[key]).length) fail(`package.json declares ${key}; the site has no runtime dependencies`);
  }
  if (JSON.stringify(pkg.devDependencies ?? {}) !== JSON.stringify({ marked: MARKED_VERSION })) fail(`package.json devDependencies must be exactly { "marked": "${MARKED_VERSION}" }`);
  const lock = await readFile(path.join(ROOT, 'package-lock.json'), 'utf8').then(JSON.parse).catch(() => null);
  if (!lock) {
    fail('package-lock.json is missing; npm ci needs it');
  } else {
    const entries = Object.keys(lock.packages ?? {}).filter((key) => key !== '');
    const locked = lock.packages?.['node_modules/marked'];
    if (lock.lockfileVersion !== 3) fail('package-lock.json must use lockfileVersion 3');
    if (entries.join(' ') !== 'node_modules/marked') fail(`the lockfile must hold only marked (found: ${entries.join(', ') || 'none'})`);
    if (lock.packages?.['']?.devDependencies?.marked !== MARKED_VERSION) fail(`the lockfile root must require marked ${MARKED_VERSION}`);
    if (locked?.version !== MARKED_VERSION || locked?.dev !== true || !/^sha512-/.test(locked?.integrity ?? '')) fail(`the lockfile must pin marked ${MARKED_VERSION} as a development dependency with an integrity hash`);
  }
  const installed = await readFile(path.join(ROOT, 'node_modules/marked/package.json'), 'utf8').then(JSON.parse).catch(() => null);
  if (installed?.version !== MARKED_VERSION) fail(`node_modules has marked ${installed?.version ?? 'missing'}; run npm ci`);
  return `${requests} URL attributes are same-origin, in-view references or allowlisted https; ${textFiles.length} text outputs and every PNG free of private paths; no scripts published; only marked ${MARKED_VERSION}, build-time and locked`;
});

await group('_headers', async (fail) => {
  const rules = parseHeaders(await readFile(path.join(DIST, '_headers'), 'utf8'));
  const missingPath = '/no-such-page';
  const served = [
    ...PAGES.map((page) => page.path),
    missingPath,
    ...files.filter((file) => !file.endsWith('.html') && file !== '_headers' && file !== '_redirects').map((file) => `/${file}`),
  ];
  for (const rule of rules) {
    if (!served.some((p) => matchesPattern(rule.pattern, p))) fail(`line ${rule.line}: ${rule.pattern} matches nothing that is served`);
  }
  for (const p of served) {
    const conflicts = conflictingHeaders(rules, p);
    if (conflicts.length) fail(`${p}: ${conflicts.join(', ')} set more than once (the host would join the values)`);
    const headers = headersFor(rules, p);
    if (!headers.get('content-security-policy') || headers.get('x-content-type-options')?.value !== 'nosniff') fail(`${p}: CSP and nosniff must apply`);
  }
  for (const p of [...PAGES.map((page) => page.path), missingPath]) {
    const headers = headersFor(rules, p);
    const get = (name) => headers.get(name)?.value;
    if (get('x-frame-options') !== 'DENY') fail(`${p}: X-Frame-Options: DENY missing`);
    if (!['no-referrer', 'same-origin', 'strict-origin', 'strict-origin-when-cross-origin'].includes(get('referrer-policy'))) fail(`${p}: restrictive Referrer-Policy missing`);
    if ((get('cache-control') ?? '').includes('immutable')) fail(`${p}: pages must not be cached as immutable`);
    if (get('content-type')) fail(`${p}: pages keep the host's HTML content type`);
  }
  const csp = headersFor(rules, '/').get('content-security-policy')?.value ?? '';
  const directives = new Map(
    csp.split(';').map((part) => part.trim()).filter(Boolean).map((part) => {
      const [name, ...values] = part.split(/\s+/);
      return [name.toLowerCase(), values];
    }),
  );
  const expected = {
    'default-src': "'none'", 'img-src': "'self'", 'style-src': "'self'", 'font-src': "'self'",
    'base-uri': "'none'", 'form-action': "'none'", 'frame-ancestors': "'none'",
  };
  for (const [name, value] of Object.entries(expected)) {
    if ((directives.get(name) ?? []).join(' ') !== value) fail(`CSP ${name} should be ${value}`);
  }
  for (const [name, values] of directives) {
    if (name === 'script-src' && values.join(' ') !== "'none'") fail("CSP script-src, if present, must be 'none'");
    for (const value of values) if (/unsafe-|^\*$|^(https?|data|blob):$/i.test(value)) fail(`CSP ${name} allows ${value}`);
  }
  // Caching: one rule, for the exact hashed stylesheet. A splat rule would also match
  // missing paths, and 404 responses inherit the headers of the rules their path matches.
  const stylesheetPath = `/assets/${built.stylesheet}`;
  const cacheRules = rules.filter((rule) => rule.set.some(([name]) => name.toLowerCase() === 'cache-control'));
  if (cacheRules.length !== 1 || cacheRules[0].pattern !== stylesheetPath) {
    fail(`only the exact path ${stylesheetPath} may set Cache-Control (found: ${cacheRules.map((rule) => rule.pattern).join(', ') || 'none'})`);
  }
  if (!/\bimmutable\b/.test(headersFor(rules, stylesheetPath).get('cache-control')?.value ?? '')) fail('the hashed stylesheet should be cached as immutable');
  for (const p of MISSING_PATHS) {
    const cache = headersFor(rules, p).get('cache-control')?.value;
    if (cache) fail(`missing ${p} would receive Cache-Control: ${cache}; misses keep the host's revalidating default`);
  }
  for (const output of [...built.used.illustrations.map((figure) => figure.output), ...built.used.images.map((image) => image.output), ...built.used.captures.map((view) => view.contextOutput)]) {
    const headers = headersFor(rules, `/${output}`);
    if (headers.get('cache-control') || headers.get('content-type')) fail(`/${output}: images keep the host's type and revalidating cache`);
  }
  if ((await readFile(path.join(DIST, '_headers'), 'utf8')).includes('{{')) fail('dist/_headers contains an unfilled placeholder');
  for (const { output, type } of DOWNLOADS) {
    const assigned = headersFor(rules, `/${output}`).get('content-type')?.value;
    if (assigned !== type) fail(`/${output} should be served as ${type}, not ${assigned ?? 'the host default'}`);
  }
  return `${rules.length} rules, no header set twice; CSP and nosniff on every path; immutable caching only for ${stylesheetPath}, none for ${MISSING_PATHS.length} missing paths; downloads served as plain text`;
});

await group('_redirects', async (fail) => {
  const text = await readFile(path.join(DIST, '_redirects'), 'utf8');
  if (text !== redirectsFile()) fail('dist/_redirects must be generated from REDIRECTS in scripts/site.mjs');
  let rules = [];
  try {
    rules = parseRedirects(text);
  } catch (error) {
    fail(error.message);
  }
  const sources = new Set();
  for (const rule of rules) {
    const at = `_redirects line ${rule.line}`;
    if (rule.status !== 301) fail(`${at}: retired routes redirect permanently (301)`);
    if (sources.has(rule.from)) fail(`${at}: ${rule.from} is redirected twice`);
    sources.add(rule.from);
    const target = pageByPath.get(rule.to);
    if (!target) fail(`${at}: ${rule.to} is not a published page`);
    const shadowed = rule.from.endsWith('/') ? fileSet.has(`${rule.from.slice(1)}index.html`) : fileSet.has(rule.from.slice(1)) || fileSet.has(`${rule.from.slice(1)}/index.html`);
    if (shadowed) fail(`${at}: ${rule.from} is a published path; a redirect would hide it`);
    if (rules.some((other) => other.from === rule.to)) fail(`${at}: ${rule.to} is itself redirected`);
  }
  for (const { from, to } of REDIRECTS) {
    for (const source of [from, from.replace(/\/$/, '')]) {
      if (!rules.some((rule) => rule.from === source && rule.to === to)) fail(`_redirects must send ${source} to ${to}`);
    }
  }
  return `${rules.length} permanent redirects from ${REDIRECTS.length} retired routes to published pages; none hides a published path or chains`;
});

await group('wrangler.jsonc', async (fail) => {
  const config = JSON.parse(stripJsonComments(await readFile(path.join(ROOT, 'wrangler.jsonc'), 'utf8')));
  const expect = (label, actual, wanted) => {
    if (actual !== wanted) fail(`${label} is ${JSON.stringify(actual)}, expected ${JSON.stringify(wanted)}`);
  };
  expect('name', config.name, 'definograph-web');
  expect('compatibility_date', config.compatibility_date, '2026-09-27');
  expect('assets.directory', config.assets?.directory, './dist');
  expect('assets.html_handling', config.assets?.html_handling, 'auto-trailing-slash');
  expect('assets.not_found_handling', config.assets?.not_found_handling, '404-page');
  // Deployment keys such as routes may be added; keys that would put code in front of the assets may not.
  for (const key of ['main', 'site']) if (key in config) fail(`"${key}" would add a Worker script or legacy site; this is an assets-only Worker`);
  if (config.assets && 'run_worker_first' in config.assets) fail('assets.run_worker_first has no place in an assets-only Worker');
  if (!fileSet.has('404.html')) fail('dist/404.html is required for 404-page handling');
  return 'assets-only Worker serving ./dist with auto-trailing-slash and 404-page handling';
});

await group('sitemap.xml and robots.txt', async (fail) => {
  const sitemap = await readFile(path.join(DIST, 'sitemap.xml'), 'utf8');
  const locations = [...sitemap.matchAll(/<loc>([^<]*)<\/loc>/g)].map((match) => match[1]);
  if (!sitemap.startsWith('<?xml version="1.0" encoding="UTF-8"?>')) fail('sitemap.xml needs an XML declaration');
  if (locations.join(' ') !== PAGES.map((page) => `${ORIGIN}${page.path}`).join(' ')) fail('sitemap.xml must list exactly the canonical page URLs');
  const robots = await readFile(path.join(DIST, 'robots.txt'), 'utf8');
  if (!robots.includes(`Sitemap: ${ORIGIN}/sitemap.xml`)) fail('robots.txt must point to the sitemap');
  if (/^Disallow:\s*\/\s*$/m.test(robots)) fail('robots.txt must not disallow the whole site');
  return `${locations.length} canonical URLs`;
});

// Complex selectors of a stylesheet's style rules, with @media and @supports flattened.
function styleSelectors(css) {
  const text = css.replace(/\/\*[\s\S]*?\*\//g, '');
  const selectors = [];
  for (const match of text.matchAll(/([^{}]+)\{/g)) {
    const prelude = match[1].trim();
    if (!prelude || prelude.startsWith('@') || /^(?:from|to|\d+%)$/.test(prelude)) continue;
    let depth = 0;
    let start = 0;
    for (let i = 0; i <= prelude.length; i += 1) {
      const ch = prelude[i];
      if (ch === '(') depth += 1;
      else if (ch === ')') depth -= 1;
      else if ((ch === ',' && depth === 0) || i === prelude.length) {
        selectors.push(prelude.slice(start, i).trim().replace(/\s+/g, ' '));
        start = i + 1;
      }
    }
  }
  return selectors;
}

// The compounds of a complex selector, split at combinators outside brackets, each with the
// combinator that joins it to the previous compound (' ', '>', '+' or '~').
function compounds(selector) {
  const parts = [];
  let depth = 0;
  let current = '';
  let combinator = null;
  let pending = ' ';
  for (const ch of selector) {
    if (ch === '(' || ch === '[') depth += 1;
    if (ch === ')' || ch === ']') depth -= 1;
    if (depth === 0 && /[\s>+~]/.test(ch)) {
      if (current) {
        parts.push({ text: current, combinator });
        current = '';
        pending = ' ';
      }
      if (ch !== ' ') pending = ch;
      combinator = pending;
    } else current += ch;
  }
  if (current) parts.push({ text: current, combinator });
  return parts;
}
// A compound restricts matching elements when it names a class, id or attribute outside
// :where(), :is() and :not() arguments.
const restricts = (compound) => /[.#[]/.test(compound.replace(/:(?:where|is|not)\([^)]*\)/g, ''));

await group('stylesheet', async (fail) => {
  const raw = await readFile(path.join(ROOT, STYLESHEET), 'utf8');
  const css = raw.replace(/\/\*[\s\S]*?\*\//g, '');
  let depth = 0;
  for (const ch of css) {
    if (ch === '{') depth += 1;
    if (ch === '}') depth -= 1;
    if (depth < 0) break;
  }
  if (depth !== 0) fail('unbalanced braces');
  if (/@import|url\(|@font-face/i.test(css)) fail('the stylesheet must not load fonts or other resources');
  for (const match of css.matchAll(/font-size\s*:\s*([^;}]+)/g)) {
    const value = match[1].trim();
    const minimum = /^clamp\(\s*([^,]+),/.exec(value)?.[1].trim() ?? value;
    if (minimum === 'inherit') continue;
    const size = /^(\d*\.?\d+)(rem|em|px)$/.exec(minimum);
    if (!size) {
      fail(`font-size: ${value} is not a form this check understands`);
      continue;
    }
    const px = size[2] === 'px' ? Number(size[1]) : Number(size[1]) * 16;
    if (px < 14) fail(`font-size: ${value} is below 14px`);
  }
  const body = /(?:^|\})\s*body\s*\{([^}]*)\}/.exec(css)?.[1] ?? '';
  const bodySize = /font-size\s*:\s*(\d*\.?\d+)rem/.exec(body)?.[1];
  if (!bodySize || Number(bodySize) < 1) fail('body text must be at least 1rem (16px)');
  const declarations = css.replace(/@media[^{]*\{/g, '{');
  for (const match of declarations.matchAll(/(?<![-\w])(width|min-width)\s*:\s*(\d*\.?\d+)(px|rem|em)\b/g)) {
    const px = match[3] === 'px' ? Number(match[2]) : Number(match[2]) * 16;
    if (px > 320) fail(`${match[1]}: ${match[2]}${match[3]} can overflow a 320px viewport`);
  }
  if (/\d(vw|vh)\b/.test(declarations.replace(/clamp\([^;]*\)/g, ''))) fail('viewport units outside clamp() do not follow text zoom');
  if (/box-shadow|linear-gradient|radial-gradient/i.test(css)) fail('the documentation style uses no shadows or gradients');
  if (!/@media\s*\(prefers-color-scheme:\s*dark\)/.test(css)) fail('the stylesheet needs a dark colour scheme');
  if (!/@media\s+print/.test(css)) fail('the stylesheet needs print rules');

  // Isolation of recorded views. A site rule whose last compound is a bare element (or a
  // pseudo-class) can style the reader's markup unless it carries :not(.dg-view *), or an
  // earlier compound requires a class that no recorded figure sits inside.
  const figureAncestors = new Set(['dg-figure', 'dg-scroll', 'dg-canvas']);
  for (const page of pages) {
    for (const figure of page.figures) for (const ancestor of figure.ancestors) for (const name of (ancestor.attrs.get('class') ?? '').split(/\s+/).filter(Boolean)) figureAncestors.add(name);
  }
  let guarded = 0;
  for (const selector of styleSelectors(raw)) {
    if (selector.includes(':not(.dg-view *)')) {
      guarded += 1;
      continue;
    }
    const parts = compounds(selector);
    const last = parts.at(-1);
    if (restricts(last?.text ?? '')) continue;
    const classesOf = (part) => [...part.text.matchAll(/\.(-?[_a-zA-Z][\w-]*)/g)].map((m) => m[1]);
    // A direct child of a site container is never inside a view (the view root is the only
    // child of .dg-canvas, and view elements are children of view elements).
    const parent = parts.at(-2);
    if (last?.combinator === '>' && parent && classesOf(parent).some((name) => !['dg-view', 'dg-canvas'].includes(name))) continue;
    const earlierClasses = parts.slice(0, -1).flatMap(classesOf);
    if (earlierClasses.some((name) => !figureAncestors.has(name))) continue;
    if (UNGUARDED_ALLOWED.has(selector) || selector === '.dg-canvas *') continue;
    fail(`selector "${selector}" can style elements inside recorded views; wrap it in :where(:not(.dg-view *))`);
  }
  // No class may be both styled by the site and used inside a recorded view.
  const siteClasses = selectorClasses(raw);
  siteClasses.delete('dg-view');
  const collisions = new Map();
  for (const page of pages) {
    for (const element of page.doc.elements.filter((candidate) => page.inView(candidate))) {
      for (const name of (element.attrs.get('class') ?? '').split(/\s+/).filter(Boolean)) {
        if (siteClasses.has(name)) collisions.set(name, `${page.file} line ${element.line}`);
      }
    }
  }
  for (const [name, where] of collisions) fail(`class "${name}" is styled by site.css and also used inside a recorded view (${where}); rename the site class`);

  // Every class used in the pages should be styled or deliberately structural. The reader's
  // own classes inside recorded views are styled by its stylesheet.
  const STRUCTURAL = new Set(['route-list', 'source', 'language-lean', 'language-sh', 'dg-view', 'dg-figure-image', 'dg-figure-capture']);
  const used = new Set(pages.flatMap((page) => page.doc.elements.filter((element) => !page.inView(element)).flatMap((element) => (element.attrs.get('class') ?? '').split(/\s+/).filter(Boolean))));
  for (const name of used) if (!STRUCTURAL.has(name) && !new RegExp(`\\.${name}(?![\\w-])`).test(css)) fail(`class "${name}" is used but not styled`);
  return `self-contained; text ≥ 14px, body ≥ 16px; no fixed widths above 320px; no shadows or gradients; light, dark and print; ${guarded} guarded rules keep site styles out of recorded views; no class shared with the reader's markup`;
});

await group('content invariants', async (fail) => {
  // Home: what Definograph is, a recorded figure straight after the introduction, the
  // reviewed statements of scope, and the plain statement that the site runs no Lean.
  const home = pageByFile.get('index.html');
  const homeText = normalize(home.doc.text(home.main));
  if (home.h1 !== SITE_NAME) fail(`home <h1> must read "${SITE_NAME}"`);
  for (const sentence of HOME_SCOPE) if (!homeText.includes(sentence)) fail(`the home page must keep the reviewed statement: "${sentence.slice(0, 70)}…"`);
  if (!/research prototype/.test(homeText) || !/runs no Lean/.test(homeText)) fail('the home introduction must say Definograph is a research prototype and that the site runs no Lean');
  // Straight after the introduction: recorded views of at least two different kinds, so the
  // first screen shows more than one way of reading a statement.
  const mainChildren = home.children(home.main);
  const intro = mainChildren.find((element) => hasClass(element, 'page-head'));
  const afterIntro = intro ? mainChildren[mainChildren.indexOf(intro) + 1] : undefined;
  const heroKinds = new Set((afterIntro ? home.within(afterIntro) : []).filter((element) => hasClass(element, 'dg-view')).flatMap((element) => (element.attrs.get('class') ?? '').split(/\s+/).filter((name) => name.startsWith('dg-view--'))));
  if (!afterIntro || !hasClass(afterIntro, 'hero-views') || heroKinds.size < 2) fail('recorded views of at least two different kinds must directly follow the home introduction');
  for (const route of ROUTES.filter((r) => r.nav)) if (!home.within(home.main).some((a) => a.name === 'a' && a.attrs.get('href') === route.path)) fail(`the home page must link to ${route.path}`);

  // Examples: each gallery entry states its question, shows one recorded figure, and says
  // what the view shows and what it leaves out.
  const examples = pageByFile.get('examples/index.html');
  const entries = examples.doc.elements.filter((element) => element.name === 'section' && hasClass(element, 'example'));
  if (!entries.length) fail('/examples/ needs gallery entries');
  for (const entry of entries) {
    const at = `/examples/ #${entry.attrs.get('id')}`;
    const inside = examples.within(entry);
    if (!inside.some((element) => element.name === 'h2' && element.parent === entry)) fail(`${at}: needs an h2 naming the reader's question`);
    if (!inside.some((element) => hasClass(element, 'task'))) fail(`${at}: needs its question in a .task paragraph`);
    if (inside.filter((element) => hasClass(element, 'dg-figure')).length !== 1) fail(`${at}: needs exactly one recorded figure`);
    const notes = inside.find((element) => element.name === 'dl' && hasClass(element, 'example-notes'));
    const terms = notes ? examples.children(notes).filter((element) => element.name === 'dt').map((dt) => normalize(examples.doc.text(dt))) : [];
    if (terms.join('|') !== 'What it shows|What it leaves out') fail(`${at}: needs "What it shows" and "What it leaves out"`);
  }
  // The on-page list names every gallery entry, in page order, by its heading.
  const onPage = examples.doc.elements.find((element) => element.name === 'nav' && hasClass(element, 'on-page'));
  const listed = (onPage ? examples.within(onPage) : []).filter((element) => element.name === 'a').map((a) => a.attrs.get('href'));
  const expected = entries.map((entry) => `#${entry.attrs.get('id')}`);
  if (listed.filter((href) => expected.includes(href)).join(' ') !== expected.join(' ')) fail('/examples/: the on-page list must name every gallery entry in page order');
  for (const entry of entries) {
    const link = onPage && examples.within(onPage).find((a) => a.name === 'a' && a.attrs.get('href') === `#${entry.attrs.get('id')}`);
    const heading = examples.within(entry).find((element) => element.name === 'h2');
    if (link && heading && normalize(examples.doc.text(link)) !== normalize(examples.doc.text(heading))) fail(`/examples/: the on-page link to #${entry.attrs.get('id')} must read "${normalize(examples.doc.text(heading))}"`);
  }

  // Reference: the reading guides, the evidence distinctions and the glossary.
  const reference = pageByFile.get('reference/index.html');
  for (const id of ['recorded-views', 'reading-the-views', 'quantifier-flow', 'relation-map', 'semantic-map', 'guided-reading', 'specialised-figures', 'structure-and-evidence', 'checking-evidence', 'relations-between-expressions', 'setup-and-support', 'generality-and-formal-foundations', 'glossary']) {
    if (!reference.ids.has(id)) fail(`/reference/ needs the #${id} section`);
  }
  const note = reference.ids.get('recorded-axiom-note');
  const listing = reference.all('code').find((code) => code.attrs.get('data-source') === 'RecordedAxiom.lean');
  if (!note || !listing) {
    fail('/reference/ needs the RecordedAxiom.lean listing and #recorded-axiom-note');
  } else {
    if ([...note.ancestors, ...listing.ancestors].some((a) => a.name === 'details')) fail('/reference/: the RecordedAxiom.lean listing and its axiom note must not be collapsed');
    const figure = listing.ancestors.findLast((a) => a.name === 'figure');
    const siblings = reference.children(note.parent);
    if (!figure || figure.parent !== note.parent || Math.abs(siblings.indexOf(note) - siblings.indexOf(figure)) !== 1) fail('/reference/: #recorded-axiom-note must sit directly beside the RecordedAxiom.lean listing');
    const text = normalize(reference.doc.text(note));
    if (!text.includes('sorryAx') || !text.includes('Neither declaration independently establishes the false equation 2 + 2 = 5.')) fail('/reference/: #recorded-axiom-note must keep its sorryAx explanation');
  }
  const glossary = reference.doc.elements.find((element) => element.name === 'dl' && hasClass(element, 'glossary'));
  const glossaryTerms = glossary ? reference.children(glossary).filter((element) => element.name === 'dt').map((dt) => normalize(reference.doc.text(dt))) : [];
  if (glossaryTerms.length < 8) fail('/reference/: the glossary needs the labels the views use');
  const sorted = [...glossaryTerms].sort((a, b) => a.localeCompare(b, 'en', { sensitivity: 'base' }));
  if (glossaryTerms.join('|') !== sorted.join('|')) fail('/reference/: glossary terms are in alphabetical order');

  // Setup: release status and trust cautions stay stated; the qualified guide stays linked.
  const install = pageByFile.get('install/index.html');
  const installText = normalize(install.doc.text(install.main));
  for (const phrase of [
    'no qualified installer or Marketplace release is provided.',
    'Keep the reader, native engine and editor controller at the same source revision.',
    'The figures on this site are recordings with stated dates',
    'Packaging the VSIX alone does not assemble a working installation.',
    'Dependency installation uses npm ci --ignore-scripts.',
    'The build, setup and packaging commands you run afterwards still execute code.',
    'The separate engine process does not provide a security sandbox.',
    'Native Windows linking is not implemented.',
  ]) {
    if (!installText.includes(phrase)) fail(`/install/ must keep: "${phrase}"`);
  }
  if (!install.all('a').some((a) => a.attrs.get('href') === '/install/local-setup/')) fail('/install/ must link to the local setup guide');
  if (!install.ids.has('try-it-yourself')) fail('/install/ needs the #try-it-yourself section');
  if (!home.within(home.main).some((a) => a.name === 'a' && a.attrs.get('href') === '/install/#try-it-yourself')) fail('the home page must link to /install/#try-it-yourself');

  for (const page of pages) {
    const footer = page.all('footer').find((element) => !element.ancestors.includes(page.main));
    const text = footer ? normalize(page.doc.text(footer)) : '';
    if (!text.includes('free to read and require no account')) fail(`${page.file}: the footer must say the material is free to read and requires no account`);
    if (/no analytics/i.test(text)) fail(`${page.file}: the footer must not make claims about hosting analytics`);
  }

  const notFound = pageByFile.get('404.html');
  const notFoundLinks = new Set(notFound.within(notFound.main).filter((element) => element.name === 'a').map((a) => a.attrs.get('href')));
  for (const route of ROUTES.filter((r) => r.path === '/' || r.nav)) if (!notFoundLinks.has(route.path)) fail(`the 404 page must link to ${route.path}`);
  return `home opens with ${heroKinds.size} kinds of recorded view; reviewed scope; ${entries.length} gallery entries with question, figure, shows and leaves out; reference guides, adjacent axiom note and sorted glossary; setup cautions; footer; 404 links`;
});

await group('preview server: routing, types, statuses', async (fail) => {
  const server = createPreviewServer(DIST);
  await new Promise((resolve, reject) => {
    server.once('error', reject);
    server.listen(0, '127.0.0.1', resolve);
  });
  const { port } = server.address();
  const notFoundBody = await readFile(path.join(DIST, '404.html'));
  const home = await readFile(path.join(DIST, 'index.html'));
  const missing = (requestPath, method = 'GET') => ({ method, path: requestPath, status: 404, type: 'text/html', body: method === 'GET' ? notFoundBody : undefined, empty: method === 'HEAD', secured: true, revalidate: true });
  const binary = async (output) => ({ path: `/${output}`, status: 200, type: 'image/png', body: await readFile(path.join(DIST, output)), secured: true, revalidate: true });
  const cases = [
    { path: '/', status: 200, type: 'text/html', body: home, secured: true },
    ...PAGES.filter((page) => page.path !== '/').map((page) => ({ path: page.path, status: 200, type: 'text/html', secured: true, revalidate: true })),
    { path: '/learn', status: 307, location: '/learn/' },
    { path: '/learn/follow-the-scope?from=check&x=1', status: 307, location: '/learn/follow-the-scope/?from=check&x=1' },
    { path: '/learn/example-notes/index.html?from=check', status: 307, location: '/learn/example-notes/?from=check' },
    { path: '/install?from=check&x=1', status: 307, location: '/install/?from=check&x=1' },
    { path: '/reference/index.html?from=check', status: 307, location: '/reference/?from=check' },
    { path: '/examples/?from=check', status: 200, type: 'text/html' },
    ...REDIRECTS.flatMap(({ from, to }) => [{ path: from, status: 301, location: to }, { path: from.replace(/\/$/, ''), status: 301, location: to }]),
    { method: 'HEAD', path: '/learn/', status: 200, empty: true },
    ...(await Promise.all(DOWNLOADS.map(async ({ output, type }) => ({
      path: `/${output}`, status: 200, type, body: await readFile(path.join(DIST, output)), secured: true, revalidate: true,
    })))),
    ...(await Promise.all(built.used.illustrations.map(async ({ source, output }) => ({
      path: `/${output}`, status: 200, type: 'image/svg+xml', body: await readFile(path.join(ROOT, source)), secured: true, revalidate: true,
    })))),
    ...(await Promise.all(built.used.mathAssets.map(async ({ output, mime }) => ({ path: `/${output}`, status: 200, type: mime, body: await readFile(path.join(DIST, output)), secured: true, revalidate: true })))),
    { path: `/assets/${built.stylesheet}`, status: 200, type: 'text/css', cache: /immutable/ },
    ...(await Promise.all(built.used.images.map(({ output }) => binary(output)))),
    ...(await Promise.all(built.used.captures.map(({ contextOutput }) => binary(contextOutput)))),
    ...MISSING_PATHS.map((requestPath) => missing(requestPath)),
    missing('/assets/missing.js', 'HEAD'),
    missing('/learn/figures/missing.svg', 'HEAD'),
    missing('/..%2fpackage.json'),
    missing('/%2e%2e/package.json'),
    { method: 'POST', path: '/', status: 405 },
  ];
  try {
    for (const c of cases) {
      const method = c.method ?? 'GET';
      const label = `${method} ${c.path}`;
      const res = await request(port, method, c.path);
      if (res.status !== c.status) {
        fail(`${label}: status ${res.status}, expected ${c.status}`);
        continue;
      }
      if (c.location && res.headers.location !== c.location) fail(`${label}: Location ${res.headers.location}, expected ${c.location}`);
      if (c.type && !String(res.headers['content-type']).startsWith(c.type)) fail(`${label}: Content-Type ${res.headers['content-type']}, expected ${c.type}`);
      if (c.body && !res.body.equals(c.body)) fail(`${label}: unexpected body`);
      if (c.empty && res.body.length) fail(`${label}: HEAD response has a body`);
      if (c.cache && !c.cache.test(res.headers['cache-control'] ?? '')) fail(`${label}: Cache-Control ${res.headers['cache-control']}`);
      if (c.revalidate && /immutable|max-age=[1-9]/.test(res.headers['cache-control'] ?? '')) fail(`${label}: must not be cached long (Cache-Control ${res.headers['cache-control']})`);
      if (c.secured && !(res.headers['content-security-policy'] && res.headers['x-content-type-options'] === 'nosniff')) fail(`${label}: security headers not applied`);
    }
  } finally {
    server.close();
  }
  return `${cases.length} requests on 127.0.0.1: ${PAGES.length} pages, query-preserving slash redirects, download, image and graphic types and bytes, 404 without long caching for missing pages, files, graphics, assets and API paths`;
});

// Inputs that exist but are not read by the build (for example drafts) are reported, not failed.
{
  const used = new Set([
    ...ROUTES.filter((route) => route.content).map((route) => `content/${route.content}`),
    `content/${NOT_FOUND.content}`,
    TEMPLATE, STYLESHEET, FAVICON, HEADERS,
    ...TUTORIAL.map(({ source }) => source),
    ...DOWNLOADS.map(({ source }) => source),
    ...built.used.images.map(({ source }) => source),
    ...built.used.illustrations.map(({ source }) => source),
    READER_VIEWS,
    ...(built.views.present ? [VIEWS_MANIFEST] : []),
    ...[...built.views.views.values()].flatMap((view) => [view.fragmentPath, view.sourcePath, view.contextPath].filter(Boolean)),
    ...built.views.batches.map((batch) => batch.cssPath),
  ]);
  for (const dir of ['content', 'templates', 'source-assets', 'tutorial']) {
    for (const file of await listFiles(path.join(ROOT, dir), dir)) {
      if (used.has(file)) continue;
      if (IMAGES.some((image) => image.source === file)) continue; // reported with the recorded views
      if (ILLUSTRATIONS.some((figure) => figure.source === file)) continue; // reported with the tutorial
      warnings.push(`${file} is not used by the build`);
    }
  }
}

function request(port, method, requestPath) {
  return new Promise((resolve, reject) => {
    const req = http.request({ host: '127.0.0.1', port, method, path: requestPath, agent: false }, (res) => {
      const chunks = [];
      res.on('data', (chunk) => chunks.push(chunk));
      res.on('end', () => resolve({ status: res.statusCode, headers: res.headers, body: Buffer.concat(chunks) }));
    });
    req.on('error', reject);
    req.end();
  });
}

// JSONC: removes // and /* */ comments outside strings. Trailing commas are not accepted.
function stripJsonComments(text) {
  let out = '';
  let inString = false;
  for (let i = 0; i < text.length; i += 1) {
    const ch = text[i];
    if (inString) {
      out += ch;
      if (ch === '\\') out += text[++i] ?? '';
      else if (ch === '"') inString = false;
    } else if (ch === '"') {
      inString = true;
      out += ch;
    } else if (ch === '/' && text[i + 1] === '/') {
      while (i < text.length && text[i] !== '\n') i += 1;
      out += '\n';
    } else if (ch === '/' && text[i + 1] === '*') {
      const end = text.indexOf('*/', i + 2);
      if (end === -1) throw new Error('unterminated comment in wrangler.jsonc');
      i = end + 1;
    } else {
      out += ch;
    }
  }
  return out;
}

let failed = 0;
for (const { name, failures, summary } of results) {
  if (failures.length) {
    failed += 1;
    console.log(`✗ ${name}`);
    for (const failure of failures) console.log(`    ${failure}`);
  } else {
    console.log(`✓ ${name}: ${summary}`);
  }
}
for (const warning of warnings) console.log(`! ${warning}`);
console.log(failed ? `\n${failed} of ${results.length} check groups failed.` : `\nAll ${results.length} check groups passed.`);
process.exitCode = failed ? 1 : 0;
