// Builds dist/ from the inputs named in site.mjs. Pages come from HTML fragments in
// content/ and, for the tutorial, from Markdown in tutorial/ rendered with the pinned
// marked devDependency. Recorded Definograph views come from the allowlist in
// source-assets/views/ (see views.mjs). Output is written to dist.partial/ first and
// swapped into place only when it matches the allowlist exactly, so a failed build never
// leaves a half-written dist/. Nothing the build runs is sent to the browser.
import { createHash } from 'node:crypto';
import { lstat, mkdir, readFile, readdir, rename, rm, writeFile } from 'node:fs/promises';
import path from 'node:path';
import { pathToFileURL } from 'node:url';
import { escapeHtml, excerptLines, inspectSvg, renderLean } from './format.mjs';
import { DIRECTIVE, describeMarkdown, renderGuide, renderMarkdown } from './markdown.mjs';
import { readPng } from './png.mjs';
import {
  DIST, DOWNLOADS, FAVICON, HEADERS, ILLUSTRATIONS, IMAGES, LEAN_SOURCES, NOT_FOUND, ORIGIN, PAGES, READER_IMAGE_BATCH, ROOT, ROUTES,
  LESSON_FILE, SITE_NAME, STYLESHEET, TEMPLATE, TITLE_SUFFIX, TUTORIAL, TUTORIAL_LINKS, outputAllowlist, redirectsFile, routeOutput,
} from './site.mjs';
import { adaptationRules, loadViews, provenanceLine, renderCaptureFigure, renderViewFigure, scopeViewCss, sizingRules } from './views.mjs';

// A preview build (`--preview`) renders a visible placeholder wherever a recorded figure is not
// available yet, so lessons can be read before every view is exported. It writes to
// dist-preview/, never to dist/, which is the only directory the host serves; `npm run check`
// always runs the strict build.
export const PREVIEW_DIST = path.join(ROOT, 'dist-preview');
const outputDirs = (preview) => (preview
  ? { dist: PREVIEW_DIST, staging: path.join(ROOT, 'dist-preview.partial'), name: 'dist-preview' }
  : { dist: DIST, staging: path.join(ROOT, 'dist.partial'), name: 'dist' });

function placeholder(kind, name) {
  return [
    `<figure class="dg-figure dg-placeholder" id="missing-${kind}-${name}">`,
    `<p class="dg-provenance"><strong>Placeholder</strong> · preview build, not for release</p>`,
    `<p class="dg-placeholder-text">The recorded ${kind === 'capture' ? 'screenshot' : kind === 'image' ? 'image' : 'view'} <code>${escapeHtml(name)}</code> is not available yet.</p>`,
    '<figcaption class="dg-caption">A release build refuses to run until this figure exists.</figcaption>',
    '</figure>',
  ].join('\n');
}

// The allowlisted recorded views, validated; any problem stops the build.
export function loadSiteViews() {
  const loaded = loadViews(ROOT);
  if (loaded.errors.length) throw new Error(`recorded views are invalid:\n  ${loaded.errors.join('\n  ')}`);
  return loaded;
}

// {{source:Name.lean}} inserts that example verbatim; {{source:Name.lean:3-5}} inserts lines
// 3 to 5 of it. Both come from the approved file, never retyped.
function sourceListing(name, from, to, sources, label, directive) {
  if (!sources.has(name)) throw new Error(`${label}: ${directive} does not name a listed Lean source`);
  let text = sources.get(name);
  let attributes = `data-source="${escapeHtml(name)}"`;
  if (from) {
    text = excerptLines(text, Number(from), Number(to));
    if (text === null) throw new Error(`${label}: ${directive} is outside ${name}`);
    attributes += ` data-lines="${from}-${to}"`;
  }
  const listingName = `Lean source: ${name}${from ? `, lines ${from} to ${to}` : ''}`;
  return `<pre class="source" tabindex="0" role="group" aria-label="${escapeHtml(listingName)}"><code ${attributes}>${renderLean(text)}</code></pre>`;
}

// An accepted reader PNG, presented like a recorded view: provenance, the exact Lean file,
// the image with a full-size link, and its approved caption and explanation.
function renderImageFigure(image, sources) {
  const text = sources.get(image.lean);
  if (text === undefined) throw new Error(`reader image ${image.name}: ${image.lean} is not a listed Lean source`);
  const recorded = READER_IMAGE_BATCH.recorded;
  return [
    `<figure class="dg-figure dg-figure-image" id="image-${image.name}">`,
    provenanceLine('Recorded Definograph image', recorded, READER_IMAGE_BATCH.lean),
    '<div class="dg-source">',
    `<p class="dg-source-label">Lean source file: <a class="filename" href="${image.sourceHref}" download>${escapeHtml(image.lean)}</a></p>`,
    `<pre class="source" tabindex="0" role="group" aria-label="${escapeHtml(`Lean source: ${image.lean}`)}"><code class="language-lean" data-source="${escapeHtml(image.lean)}">${renderLean(text)}</code></pre>`,
    '</div>',
    `<div class="dg-image"><a href="/${image.output}" aria-label="Open the full-size image: ${escapeHtml(image.title)}"><img src="/${image.output}" width="${image.width}" height="${image.height}" alt="${escapeHtml(image.alt)}" loading="lazy" decoding="async"></a></div>`,
    `<figcaption class="dg-caption">${image.caption} ${image.explanationHtml} <a href="/${image.output}">Open the full-size image</a>.</figcaption>`,
    '</figure>',
  ].join('\n');
}

// Figures placed by directives, and a record of what each page uses. A view, capture or
// image may appear at most once on a page (its ids would repeat).
function figureRenderer({ views, sources, downloads }) {
  const used = { views: new Map(), captures: new Map(), images: new Map(), illustrations: new Map() };
  // Problems that need a view exported or a caption reviewed are collected, so one build
  // reports every one of them.
  const unavailable = [];
  const downloadFor = (text) => downloads.find(({ output, bytes }) => output.endsWith('.lean') && bytes.toString('utf8') === text);
  const onPage = new Map();
  const render = (kind, name, label, { sourceShown = false } = {}) => {
    const seen = onPage.get(label) ?? new Set();
    onPage.set(label, seen);
    if (seen.has(`${kind}:${name}`)) throw new Error(`${label}: {{${kind}:${name}}} is used twice on one page`);
    seen.add(`${kind}:${name}`);
    if (kind === 'view' || kind === 'capture') {
      const view = views.views.get(name);
      if (!view || (kind === 'view' && view.captionDraft)) {
        unavailable.push(`${label}: {{${kind}:${name}}} ${view ? 'still has an imported draft caption; review it first' : 'names no view in the recorded-view allowlist'}`);
        return placeholder(kind, name);
      }
      if (kind === 'view') {
        if (view.captureOnly) {
          unavailable.push(`${label}: {{view:${name}}} is a screenshot without a recorded view; use {{capture:${name}}}`);
          return placeholder(kind, name);
        }
        used.views.set(name, view);
        return renderViewFigure(view, { downloadFor, sourceShown });
      }
      if (!view.contextPath || view.contextIncomplete || view.contextDraft) {
        unavailable.push(`${label}: {{capture:${name}}} ${!view.contextPath ? 'names a view without a context capture' : view.contextIncomplete ? 'needs its alt text and caption' : 'has alt text and a caption written for an earlier screenshot; review them first'}`);
        return placeholder(kind, name);
      }
      used.captures.set(name, view);
      return renderCaptureFigure(view, { downloadFor, sourceShown });
    }
    const image = IMAGES.find((candidate) => candidate.name === name);
    if (!image) throw new Error(`${label}: {{image:${name}}} names no reader image`);
    used.images.set(name, image);
    return renderImageFigure(image, sources);
  };
  return { render, used, unavailable, viewSource: (name) => views.views.get(name)?.sourceText };
}

// Expands a content fragment's directives in one pass, so inserted text is never rescanned.
// Figure directives stand on a line of their own; source and lesson directives may appear
// anywhere. {{lesson:NN-slug.md}} becomes a link to that lesson, named by its own title, once
// the tutorial index publishes it, and a link to the tutorial until then. {{guide:name.md}}, on
// a line of its own, shows a published Markdown download (DOWNLOADS) as HTML (renderGuide).
const CONTENT_DIRECTIVES = /^[ \t]*\{\{(view|capture|image):([a-z0-9][a-z0-9-]*)\}\}[ \t]*$|\{\{source:([^{}:]*)(?::(\d+)-(\d+))?\}\}|\{\{lesson:([^{}]+)\}\}|^[ \t]*\{\{guide:([a-z0-9-]+\.md)\}\}[ \t]*$/gm;
function expandContent(fragment, label, { sources, render, lesson, guide }) {
  const figures = fragment.match(/\{\{(?:view|capture|image):/g)?.length ?? 0;
  const blocks = fragment.match(/^[ \t]*\{\{(?:view|capture|image):[a-z0-9][a-z0-9-]*\}\}[ \t]*$/gm)?.length ?? 0;
  if (figures !== blocks) throw new Error(`${label}: a {{view:…}}, {{capture:…}} or {{image:…}} directive must be on a line of its own`);
  return fragment.replace(CONTENT_DIRECTIVES, (directive, kind, name, file, from, to, lessonFile, guideFile) => {
    if (kind) return render(kind, name, label);
    if (lessonFile) return lesson(lessonFile, label);
    if (guideFile) return guide(guideFile, label);
    return sourceListing(file, from, to, sources, label, directive);
  });
}

// A link to a lesson by its file name, and a warning while that lesson is not published.
function lessonLinker(tutorial, warnings) {
  return (file, label) => {
    if (!LESSON_FILE.test(file)) throw new Error(`${label}: {{lesson:${file}}} does not name a lesson file (NN-slug.md)`);
    const page = tutorial.find((entry) => entry.source === `tutorial/${file}`);
    if (!page) {
      warnings.push(`${label}: {{lesson:${file}}} links to the tutorial index until the index publishes that lesson`);
      return '<a href="/learn/">the tutorial</a>';
    }
    const title = page.h1.replace(/^\d+\.\s*/, '');
    return `<a href="${page.path}">Lesson ${Number(LESSON_FILE.exec(file)[1])}: ${escapeHtml(title)}</a>`;
  };
}

// A tutorial link, resolved against the directory of the Markdown file that contains it
// and mapped to its published route. Unmapped relative links stop the build.
function tutorialResolver(source) {
  return (href) => {
    if (/^[a-z][a-z0-9+.-]*:/i.test(href) || href.startsWith('#')) return href;
    const [target, fragment] = href.split('#');
    const file = path.posix.normalize(path.posix.join(path.posix.dirname(source), target));
    const route = TUTORIAL_LINKS.get(file);
    if (!route) throw new Error(`${source}: link "${href}" (${file}) has no published route`);
    return fragment === undefined ? route : `${route}#${fragment}`;
  };
}

// Tutorial navigation: the sidebar of all tutorial pages with the current page's
// sections, the same sections for narrow screens, and previous and next links.
function tutorialNavigation(page, pages) {
  const sections = page.headings.filter((heading) => heading.depth === 2);
  const sectionList = (className) => `<ul class="${className}">\n${sections.map((heading) => `<li><a href="#${heading.id}">${escapeHtml(heading.text)}</a></li>`).join('\n')}\n</ul>`;
  const items = pages.map((other) => {
    const current = other === page;
    const sublist = current && sections.length ? `\n${sectionList('sidebar-sections')}\n` : '';
    return `<li><a href="${other.path}"${current ? ' aria-current="page"' : ''}>${escapeHtml(other.label)}</a>${sublist}</li>`;
  });
  const sidebar = [
    '<nav class="doc-sidebar" aria-labelledby="tutorial-contents">',
    '<p class="sidebar-title" id="tutorial-contents">Tutorial contents</p>',
    `<ul class="sidebar-pages">\n${items.join('\n')}\n</ul>`,
    '</nav>',
  ].join('\n');
  const toc = sections.length
    ? `<nav class="page-toc" aria-labelledby="page-toc-title">\n<p class="toc-title" id="page-toc-title">On this page</p>\n${sectionList('toc-sections')}\n</nav>\n`
    : '';
  const index = pages.indexOf(page);
  const previous = pages[index - 1];
  const next = pages[index + 1];
  const pager = [
    '<nav class="pager" aria-label="Previous and next">',
    previous ? `<a class="pager-previous" href="${previous.path}" rel="prev"><span class="pager-label">Previous</span> ${escapeHtml(previous.label)}</a>` : '',
    next ? `<a class="pager-next" href="${next.path}" rel="next"><span class="pager-label">Next</span> ${escapeHtml(next.label)}</a>` : '',
    '</nav>',
  ].filter(Boolean).join('\n');
  return { sidebar, toc, pager };
}

function tutorialBody(page, pages) {
  const { sidebar, toc, pager } = tutorialNavigation(page, pages);
  const article = page.html.replace(/<\/h1>\n/, (end) => `${end}${toc}`);
  return `<div class="doc-layout">\n<main id="main" class="doc-main" tabindex="-1">\n<article class="doc">\n${article}</article>\n${pager}\n</main>\n${sidebar}\n</div>`;
}

function fill(template, values, label) {
  return template.replace(/\{\{([a-z]+)\}\}/g, (token, key) => {
    if (!Object.hasOwn(values, key)) throw new Error(`${label}: unknown placeholder ${token}`);
    return values[key];
  });
}

// page: { path (null for 404), title, description, inTutorial }.
function renderPage(template, page, body, stylesheetHref) {
  const canonical = page.path ? `${ORIGIN}${page.path}` : null;
  const meta = canonical
    ? [
        `<link rel="canonical" href="${canonical}">`,
        '<meta property="og:type" content="website">',
        `<meta property="og:site_name" content="${SITE_NAME}">`,
        `<meta property="og:title" content="${escapeHtml(page.title)}">`,
        `<meta property="og:description" content="${escapeHtml(page.description)}">`,
        `<meta property="og:url" content="${canonical}">`,
      ].join('\n')
    : '<meta name="robots" content="noindex">';
  const nav = ROUTES.filter((route) => route.nav).map((route) => {
    let current = '';
    if (route.path === page.path) current = ' aria-current="page"';
    else if (route.tutorial && page.inTutorial) current = ' aria-current="true"';
    else if (page.section === route.path) current = ' aria-current="true"';
    return `        <li><a href="${route.path}"${current}>${escapeHtml(route.nav)}</a></li>`;
  }).join('\n');
  return fill(
    template,
    {
      title: escapeHtml(page.title),
      description: escapeHtml(page.description),
      meta,
      stylesheet: stylesheetHref,
      home: page.path === '/' ? ' aria-current="page"' : '',
      nav,
      body: body.trim(),
    },
    TEMPLATE,
  );
}

function robotsTxt() {
  return `User-agent: *\nAllow: /\n\nSitemap: ${ORIGIN}/sitemap.xml\n`;
}

function sitemapXml() {
  return [
    '<?xml version="1.0" encoding="UTF-8"?>',
    '<urlset xmlns="http://www.sitemaps.org/schemas/sitemap/0.9">',
    ...PAGES.map((page) => `  <url><loc>${ORIGIN}${page.path}</loc></url>`),
    '</urlset>',
    '',
  ].join('\n');
}

// Relative POSIX paths of every entry under dir. Anything that is not a plain
// file or directory (for example a symlink) is reported so callers can reject it.
export async function listFiles(dir, prefix = '') {
  const found = [];
  for (const entry of await readdir(dir, { withFileTypes: true })) {
    const rel = prefix ? `${prefix}/${entry.name}` : entry.name;
    if (entry.isDirectory()) found.push(...(await listFiles(path.join(dir, entry.name), rel)));
    else if (entry.isFile()) found.push(rel);
    else found.push(`${rel} (not a regular file)`);
  }
  return found;
}

// A tutorial page's description: its own description comment, else its first paragraph.
export function tutorialDescription(source, markdown) {
  return describeMarkdown(markdown);
}

// Renders every tutorial page. `figures` supplies recorded figures (render), the sources of
// recorded views (viewSource) and a record of the teaching graphics pages use.
export async function renderTutorial({ render, viewSource, used }) {
  const read = (rel) => readFile(path.join(ROOT, rel), 'utf8');
  const leanFiles = new Map();
  for (const { source } of LEAN_SOURCES) leanFiles.set(path.posix.basename(source), await read(source));
  const illustration = (url) => {
    const figure = ILLUSTRATIONS.find(({ output }) => `/${output}` === url);
    if (figure) used.illustrations.set(figure.output, figure);
    return figure;
  };
  const pages = [];
  for (const entry of TUTORIAL) {
    const markdown = await read(entry.source);
    const rendered = renderMarkdown(markdown, {
      source: entry.source,
      resolve: tutorialResolver(entry.source),
      leanFiles,
      illustration,
      viewSource,
      directive: (kind, name, options) => render(kind, name, entry.source, options),
    });
    const title = rendered.title.includes(SITE_NAME) ? rendered.title : `${rendered.title}${TITLE_SUFFIX}`;
    pages.push({
      ...entry,
      markdown,
      html: rendered.html,
      headings: rendered.headings,
      directives: rendered.directives,
      h1: rendered.title,
      label: entry.label ?? rendered.title,
      title,
      description: tutorialDescription(entry.source, markdown),
    });
  }
  return pages;
}

export async function build({ preview = false } = {}) {
  const read = (rel) => readFile(path.join(ROOT, rel));
  const { dist: DIST_DIR, staging: STAGING, name: DIST_NAME } = outputDirs(preview);

  const template = String(await read(TEMPLATE));
  const siteCss = await read(STYLESHEET);
  const favicon = await read(FAVICON);
  const headersTemplate = String(await read(HEADERS));
  const views = loadSiteViews();

  const downloads = [];
  for (const download of DOWNLOADS) {
    const bytes = await read(download.source);
    if (!Buffer.from(bytes.toString('utf8'), 'utf8').equals(bytes)) throw new Error(`${download.source} is not valid UTF-8`);
    downloads.push({ ...download, bytes });
  }
  const sources = new Map(
    LEAN_SOURCES.map(({ source }) => [path.posix.basename(source), downloads.find((d) => d.source === source).bytes.toString('utf8')]),
  );
  const figures = figureRenderer({ views, sources, downloads });
  const { render, used } = figures;

  // Page bodies first: they determine which images, captures, graphics and view styles are
  // published. The tutorial comes first so content pages can link its lessons by title.
  const bodies = [];
  const buildWarnings = [...views.warnings];
  const tutorial = await renderTutorial(figures);
  const lesson = lessonLinker(tutorial, buildWarnings);
  // A Markdown download shown as HTML: the published file with that name.
  const guide = (name, label) => {
    const download = downloads.find(({ output }) => path.posix.basename(output) === name && output.endsWith('.md'));
    if (!download) throw new Error(`${label}: {{guide:${name}}} names no published Markdown download`);
    return renderGuide(download.bytes.toString('utf8'), `${label} {{guide:${name}}}`);
  };
  for (const route of ROUTES.filter((r) => !r.tutorial)) {
    const label = `content/${route.content}`;
    const fragment = expandContent(String(await read(label)), label, { sources, render, lesson, guide });
    bodies.push({ output: routeOutput(route), page: route, body: `<main id="main" class="page" tabindex="-1">\n${fragment.trim()}\n</main>` });
  }
  for (const page of tutorial) {
    bodies.push({ output: routeOutput(page), page: { ...page, inTutorial: page.path !== '/learn/' }, body: tutorialBody(page, tutorial) });
  }
  const notFoundLabel = `content/${NOT_FOUND.content}`;
  const notFoundBody = `<main id="main" class="page" tabindex="-1">\n${expandContent(String(await read(notFoundLabel)), notFoundLabel, { sources, render, lesson, guide }).trim()}\n</main>`;
  bodies.push({ output: NOT_FOUND.output, page: { ...NOT_FOUND, path: null }, body: notFoundBody });
  if (figures.unavailable.length && !preview) {
    throw new Error(`${figures.unavailable.length} recorded figure(s) cannot be placed yet:\n  ${figures.unavailable.join('\n  ')}`);
  }

  // Teaching graphics are published unchanged, and only if they are inert.
  const illustrations = [];
  for (const illustration of used.illustrations.values()) {
    const bytes = await read(illustration.source);
    const svg = inspectSvg(bytes.toString('utf8'));
    if (svg.problems.length) throw new Error(`${illustration.source} contains ${svg.problems.join(', ')}`);
    if (svg.width !== illustration.width || svg.height !== illustration.height) {
      throw new Error(`${illustration.source} is ${svg.width}×${svg.height}, but the manifest says ${illustration.width}×${illustration.height}`);
    }
    illustrations.push({ ...illustration, bytes });
  }

  // Reader images are binary: read as bytes, never decoded as text, and published unchanged.
  const images = [];
  for (const image of used.images.values()) {
    const bytes = await read(image.source);
    const png = readPng(bytes);
    if (png.errors.length) throw new Error(`${image.source}: ${png.errors.join('; ')}`);
    if (png.width !== image.width || png.height !== image.height) {
      throw new Error(`${image.source} is ${png.width}×${png.height} pixels, but the manifest says ${image.width}×${image.height}`);
    }
    images.push({ ...image, bytes });
  }

  // One stylesheet: the site's, then the reader's own styles for each batch that pages use,
  // scoped to that batch's figures so no batch restyles another's, then generated widths.
  const batches = views.batches.filter((batch) => batch.views.some((view) => used.views.has(view.id)));
  const css = Buffer.from(publishedStylesheet(String(siteCss), batches, [...used.views.values()]));
  const stylesheet = `site.${createHash('sha256').update(css).digest('hex').slice(0, 10)}.css`;
  const stylesheetHref = `/assets/${stylesheet}`;

  // Immutable caching is granted to this exact stylesheet path only, never to a
  // pattern that would also match missing files under /assets/.
  const placeholders = headersTemplate.match(/^\{\{stylesheet\}\}$/gm) ?? [];
  if (placeholders.length !== 1) throw new Error(`${HEADERS} must contain exactly one {{stylesheet}} path line`);
  const headers = headersTemplate.replace(/^\{\{stylesheet\}\}$/m, stylesheetHref);
  if (headers.includes('{{')) throw new Error(`${HEADERS} contains an unknown placeholder`);

  await rm(STAGING, { recursive: true, force: true });
  await mkdir(STAGING);
  const emit = async (rel, data) => {
    const target = path.join(STAGING, ...rel.split('/'));
    await mkdir(path.dirname(target), { recursive: true });
    await writeFile(target, data, { flag: 'wx' });
  };

  const usedLists = { images: [...used.images.values()], captures: [...used.captures.values()], views: [...used.views.values()], illustrations: [...used.illustrations.values()] };
  const expected = outputAllowlist(stylesheet, usedLists);
  try {
    const banner = preview ? '<p class="preview-banner">Preview build with placeholders for recorded figures that are not available yet. Not for release.</p>\n' : '';
    for (const { output, page, body } of bodies) await emit(output, renderPage(template, page, `${banner}${body}`, stylesheetHref));
    await emit(`assets/${stylesheet}`, css);
    await emit('favicon.svg', favicon);
    for (const { output, bytes } of downloads) await emit(output, bytes);
    for (const { output, bytes } of images) await emit(output, bytes);
    for (const view of used.captures.values()) await emit(view.contextOutput, view.contextBytes);
    for (const { output, bytes } of illustrations) await emit(output, bytes);
    await emit('_headers', headers);
    await emit('_redirects', redirectsFile());
    await emit('robots.txt', robotsTxt());
    await emit('sitemap.xml', sitemapXml());

    const actual = (await listFiles(STAGING)).sort();
    const extra = actual.filter((file) => !expected.includes(file));
    const missing = expected.filter((file) => !actual.includes(file));
    if (extra.length || missing.length) {
      throw new Error(`output does not match the allowlist (extra: ${extra.join(', ') || 'none'}; missing: ${missing.join(', ') || 'none'})`);
    }
  } catch (error) {
    await rm(STAGING, { recursive: true, force: true });
    throw error;
  }

  // Replace the output directory only after the staged output is complete.
  if (path.dirname(DIST_DIR) !== ROOT || path.basename(DIST_DIR) !== DIST_NAME) throw new Error(`refusing to replace ${DIST_DIR}`);
  const existing = await lstat(DIST_DIR).catch(() => null);
  if (existing && !existing.isDirectory()) throw new Error(`${DIST_NAME} exists and is not a directory`);
  await rm(DIST_DIR, { recursive: true, force: true });
  await rename(STAGING, DIST_DIR);
  return { files: expected, stylesheet, used: usedLists, batches, views, warnings: buildWarnings, unavailable: figures.unavailable, dist: DIST_DIR };
}

// The published stylesheet: site.css, each used batch's styles scoped to its own figures, and
// the generated widths. The checks rebuild it with the same function and compare the bytes.
export function publishedStylesheet(siteCss, batches, usedViews) {
  return [
    siteCss,
    ...batches.map((batch) => `\n/* Recorded Definograph views (${batch.name}): Definograph's own styles, for the figures of this set only. */\n${scopeViewCss(batch.css, batch.name, batch.keyframePlan)}/* Adaptations for a static page (RECORDING_ADAPTATIONS in scripts/views.mjs). */\n${adaptationRules(batch.name)}\n`),
    sizingRules(usedViews),
  ].join('');
}

// Kept for scripts that only need to know whether a paragraph is a figure directive.
export { DIRECTIVE };

const invokedDirectly = process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
if (invokedDirectly) {
  try {
    const preview = process.argv.includes('--preview');
    const { files, warnings, unavailable } = await build({ preview });
    console.log(`Built ${files.length} files into ${preview ? 'dist-preview/ (preview build, not for release)' : 'dist/'}:`);
    for (const file of files) console.log(`  ${file}`);
    for (const warning of warnings) console.log(`! ${warning}`);
    for (const missing of unavailable) console.log(`! placeholder: ${missing}`);
  } catch (error) {
    console.error(`Build failed: ${error.message}`);
    process.exitCode = 1;
  }
}
