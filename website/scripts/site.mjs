// Site manifest: routes, the inputs the build may read, and the explicit output allowlist.
// The build reads only the files named here or found by the tutorial's naming rule; it never
// copies directories wholesale.
import { existsSync, readFileSync, readdirSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { Lexer } from 'marked';

export const ROOT = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
export const DIST = path.join(ROOT, 'dist');
export const ORIGIN = 'https://definograph.com';
export const SITE_NAME = 'Definograph';
export const TITLE_SUFFIX = ' · Definograph';

export const TEMPLATE = 'templates/page.html';
export const STYLESHEET = 'source-assets/site.css';
export const FAVICON = 'source-assets/favicon.svg';
export const HEADERS = 'source-assets/_headers';

// Pages built from HTML fragments in content/, and the tutorial, rendered from Markdown.
// Routes with `nav` form the primary navigation, in this order; the site name links home.
export const ROUTES = [
  {
    path: '/',
    content: 'index.html',
    title: 'Definograph: the structure of mathematical statements in Lean',
    description:
      'An experimental reader that draws the logical structure of mathematical statements written in Lean: choices, dependencies, objects and relations.',
  },
  { path: '/learn/', nav: 'Tutorial', tutorial: true },
  {
    path: '/examples/',
    nav: 'Examples',
    content: 'examples.html',
    title: 'Examples · Definograph',
    description: 'Recorded Definograph views of real statements, each with its Lean source, what the view shows and what it leaves out.',
  },
  {
    path: '/reference/',
    nav: 'Reference',
    content: 'reference.html',
    title: 'Reference · Definograph',
    description: 'How to read each Definograph view, what its checking evidence means, and the labels the views use.',
  },
  {
    path: '/install/',
    nav: 'Setup',
    content: 'install.html',
    title: 'Setup and release status · Definograph',
    description:
      'How to try Definograph yourself: what is published, what it needs, and how it is assembled from source.',
  },
  {
    path: '/install/local-setup/',
    // Not in the primary navigation; Setup is marked as its section.
    section: '/install/',
    content: 'local-setup.html',
    title: 'Local setup guide · Definograph',
    description: 'How to assemble Definograph from a matching source checkout, and which parts of that assembly have been checked.',
  },
];

// The tutorial, in reading order: tutorial/README.md at /learn/, then the lessons the index
// links to (files named NN-slug.md in tutorial/, in numeric order) at /learn/slug/, then
// tutorial/examples/README.md at /learn/example-notes/. A lesson is published once the index
// links it; other files in tutorial/ (plans, drafts, earlier lessons) are not read.
// A page's title is its h1 plus TITLE_SUFFIX (left off when the h1 already names
// Definograph). Its description is a first line of the form <!-- description: ... --> in the
// file, or else its first paragraph (describeMarkdown in markdown.mjs). `label` replaces the
// h1 in the tutorial navigation.
export const LESSON_FILE = /^(\d{2})-([a-z0-9]+(?:-[a-z0-9]+)*)\.md$/;
// Lessons that keep an earlier public route.
const ROUTE_OVERRIDES = new Map([
  ['01-order-of-choices.md', '/learn/follow-the-scope/'],
  ['05-inspect-in-the-editor.md', '/learn/follow-an-inspection/'],
  ['07-unfamiliar-structure.md', '/learn/read-an-unfamiliar-structure/'],
]);
// Lesson files linked from the index, in numeric order.
export function linkedLessons(markdown) {
  const found = new Set();
  const visit = (tokens = []) => {
    for (const token of tokens) {
      if (token.type === 'link') {
        const target = token.href.split('#')[0];
        if (LESSON_FILE.test(target)) found.add(target);
      }
      visit(token.tokens);
      visit(token.items);
      if (token.type === 'table') [...token.header, ...token.rows.flat()].forEach((cell) => visit(cell.tokens));
    }
  };
  visit(new Lexer({ gfm: true }).lex(markdown));
  return [...found].sort();
}

function discoverTutorial() {
  const pages = [{ path: '/learn/', source: 'tutorial/README.md' }];
  const routes = new Set(['/learn/', '/learn/example-notes/', '/learn/examples/', '/learn/figures/']);
  for (const file of linkedLessons(readFileSync(path.join(ROOT, 'tutorial/README.md'), 'utf8'))) {
    if (!existsSync(path.join(ROOT, 'tutorial', file))) throw new Error(`tutorial/README.md links ${file}, which does not exist`);
    const route = ROUTE_OVERRIDES.get(file) ?? `/learn/${LESSON_FILE.exec(file)[2]}/`;
    if (routes.has(route)) throw new Error(`tutorial/${file}: the route ${route} is already taken`);
    routes.add(route);
    pages.push({ path: route, source: `tutorial/${file}` });
  }
  if (existsSync(path.join(ROOT, 'tutorial/examples/README.md'))) {
    pages.push({ path: '/learn/example-notes/', source: 'tutorial/examples/README.md', label: 'Example notes' });
  }
  return pages;
}
export const TUTORIAL = discoverTutorial();

// Permanent redirects for retired routes, published as dist/_redirects (the host's format:
// "source destination status"). Each rule is written with and without its trailing slash.
// A retired lesson points to the lesson that now holds its main example.
export const REDIRECTS = [
  // Old lesson 2, "Form a proposition, supply a proof": its proofs (QuantifierProofs.lean,
  // each_has_equal and no_one_equals_all) are in lesson 6.
  { from: '/learn/propositions-and-proofs/', to: '/learn/checking-evidence/', status: 301 },
  // Old lesson 4, "Keep a law with its owner": its Rotor structure (RotorLaw.lean), the
  // owner and the field catalogue are in lesson 5.
  { from: '/learn/laws-and-owners/', to: '/learn/follow-an-inspection/', status: 301 },
];

export function redirectsFile() {
  const lines = ['# Retired routes and where their material is now. Generated by scripts/build.mjs from scripts/site.mjs.'];
  for (const { from, to, status } of REDIRECTS) {
    lines.push(`${from} ${to} ${status}`);
    if (from.endsWith('/')) lines.push(`${from.slice(0, -1)} ${to} ${status}`);
  }
  return `${lines.join('\n')}\n`;
}

export const NOT_FOUND = {
  output: '404.html',
  content: '404.html',
  title: 'Page not found · Definograph',
  description: 'This page could not be found.',
};

// Public downloads, published byte for byte at their canonical paths. The digests pin
// the approved files: `npm run check` fails if a source or its published copy changes.
// `type` is the Content-Type that dist/_headers must assign.
const TEXT = 'text/plain; charset=utf-8';
export const DOWNLOADS = [
  { source: 'tutorial/examples/Scope.lean', output: 'learn/examples/Scope.lean', type: TEXT, sha256: 'f5f6215db37213d0d82da34f464f095a4612e10618257c414772299771b09f0d' },
  { source: 'tutorial/examples/QuantifierForallExists.lean', output: 'learn/examples/QuantifierForallExists.lean', type: TEXT, sha256: 'add32a64e6e65ad28d013391230c6840731d87336df3b49c3343a98f72e2efb5' },
  { source: 'tutorial/examples/QuantifierExistsForall.lean', output: 'learn/examples/QuantifierExistsForall.lean', type: TEXT, sha256: 'b028d46387557bef029c439599d9a16fd33e4babf00b472fa7acadf889426c81' },
  { source: 'tutorial/examples/QuantifierProofs.lean', output: 'learn/examples/QuantifierProofs.lean', type: TEXT, sha256: 'a266a13dd004300c9888eec23bb2eaf50c342f0a2734a983020bd47d0574ef91' },
  { source: 'tutorial/examples/RotorLaw.lean', output: 'learn/examples/RotorLaw.lean', type: TEXT, sha256: 'a43c0b6cc82c084730702a211d54355359f96e45281c7a50005ec4d95e7ee7b1' },
  { source: 'tutorial/examples/RotorExamples.lean', output: 'learn/examples/RotorExamples.lean', type: TEXT, sha256: 'cc1455bd2119b83c246b987f38a9ba78dedea9768bd4ac3727d4cdc2c0e4a84d' },
  { source: 'tutorial/examples/Evidence.lean', output: 'learn/examples/Evidence.lean', type: TEXT, sha256: 'd08b151d13dc4b093abec35848290ae5f96bd79a9daeb8c18909f381bff3f9b4' },
  { source: 'tutorial/examples/ReturnMap.lean', output: 'learn/examples/ReturnMap.lean', type: TEXT, sha256: '21ebbb3dd5b0fe4fea31f7b6f9e049378b037a2fd0701210ab032d46cec1b409' },
  { source: 'source-assets/examples/RecordedAxiom.lean', output: 'learn/examples/RecordedAxiom.lean', type: TEXT, sha256: '19e978d4d579aec7d354c8282f546a32bbcb5cf0ae5b6466d566517f18f4e1bc' },
  { source: 'source-assets/contracts/local-setup.md', output: 'reference/contracts/local-setup.md', type: TEXT, sha256: '6bae7270050ec88f561ddc95a7788fe4a89cf0bd90fe0738b821097253568d56' },
  { source: 'source-assets/contracts/reader-relations.md', output: 'reference/contracts/reader-relations.md', type: TEXT, sha256: '846d9d226d707be14e4b5b6ae8e224e2f8246509bb863d6e12cb0e0b9fab0bab' },
];

// Lean files that pages may display: content fragments with {{source:Name.lean}}, and
// tutorial code blocks, which are matched against them.
export const LEAN_SOURCES = DOWNLOADS.filter(({ source }) => source.endsWith('.lean'));

// Reader images: the two accepted PNG captures of the quantifier-flow view, published only
// where a page places one with {{image:name}}. They remain until recorded HTML views of the
// same statements replace them. The file is read at build time and never published.
export const READER_VIEWS = 'source-assets/reader/public-views.json';
const readerViews = existsSync(path.join(ROOT, READER_VIEWS)) ? JSON.parse(readFileSync(path.join(ROOT, READER_VIEWS), 'utf8')) : null;
export const READER_IMAGE_BATCH = { recorded: readerViews?.recorded ?? null, lean: readerViews?.lean ?? null };
export const IMAGES = (readerViews?.images ?? []).map((view) => ({
  name: path.posix.basename(String(view.path), '.png'),
  source: view.source,
  output: String(view.path).replace(/^\//, ''),
  width: view.width,
  height: view.height,
  sha256: view.sha256,
  lean: view.leanFilename,
  sourceHref: view.sourceHref,
  sourceCode: view.sourceCode,
  title: view.title,
  alt: view.alt,
  caption: view.caption,
  explanationHtml: view.explanationHtml,
}));

// Authored teaching graphics: published byte for byte, only when a lesson shows one, and
// never presented as reader output. width and height are the SVG's own attributes.
export const ILLUSTRATIONS = [
  { source: 'tutorial/figures/quantifier-scope.svg', output: 'learn/figures/quantifier-scope.svg', width: 530, height: 690, sha256: 'b018594857322445b24812c4884feea83c946cdbe97d6c9c780ca7db097a3b3a' },
].filter(({ source }) => existsSync(path.join(ROOT, source)));

// Where the tutorial's relative links lead once published. Keys are site-relative source
// paths, after resolving a link against the directory of the file that contains it.
export const TUTORIAL_LINKS = new Map([
  ...TUTORIAL.map(({ source, path: route }) => [source, route]),
  ['content/reference.md', '/reference/'],
  ['content/examples.md', '/examples/'],
  ['content/install.md', '/install/'],
  ['content/index.md', '/'],
  ...DOWNLOADS.map(({ source, output }) => [source, `/${output}`]),
  ...ILLUSTRATIONS.map(({ source, output }) => [source, `/${output}`]),
]);

// The only external destinations pages may link to.
export const EXTERNAL_LINKS = new Set([
  'https://github.com/N-Y-L/definograph',
  'https://github.com/N-Y-L/definograph/issues',
]);

export function routeOutput(route) {
  return route.path === '/' ? 'index.html' : `${route.path.slice(1)}index.html`;
}

// Every page, in navigation order: the routes, with the tutorial's pages in place of /learn/.
export const PAGES = ROUTES.flatMap((route) => (route.tutorial ? TUTORIAL : [route]));

// The reader images, screenshots and teaching graphics that pages place, read from the page
// sources. The build finds the same set while rendering; the check compares the two.
export function placedFigures() {
  const sources = [
    ...ROUTES.filter((route) => route.content).map((route) => `content/${route.content}`),
    `content/${NOT_FOUND.content}`,
    ...TUTORIAL.map(({ source }) => source),
  ].map((rel) => readFileSync(path.join(ROOT, rel), 'utf8'));
  const text = sources.join('\n');
  const named = (kind) => [...new Set([...text.matchAll(new RegExp(`^[ \\t]*\\{\\{${kind}:([a-z0-9][a-z0-9-]*)\\}\\}[ \\t]*$`, 'gm'))].map((match) => match[1]))];
  const viewsFile = path.join(ROOT, 'source-assets/views/views.json');
  const allowlist = existsSync(viewsFile) ? JSON.parse(readFileSync(viewsFile, 'utf8')) : { batches: [] };
  const batchOf = new Map(allowlist.batches.flatMap((batch) => (batch.views ?? []).filter((view) => view.context).map((view) => [view.id, batch.batch])));
  return {
    images: named('image').map((name) => IMAGES.find((image) => image.name === name)).filter(Boolean),
    captures: named('capture').filter((id) => batchOf.has(id)).map((id) => ({ id, contextOutput: `images/views/${batchOf.get(id)}/${id}-context-2x.png` })),
    illustrations: ILLUSTRATIONS.filter(({ source }) => sources.some((markdown) => markdown.includes(`figures/${path.posix.basename(source)}`))),
  };
}

// Every file dist/ may contain, relative to dist/. `stylesheet` is the content-hashed CSS
// name; `used` lists the reader images, screenshots and teaching graphics that pages place.
export function outputAllowlist(stylesheet, used = placedFigures()) {
  return [
    ...PAGES.map(routeOutput),
    NOT_FOUND.output,
    `assets/${stylesheet}`,
    'favicon.svg',
    ...DOWNLOADS.map(({ output }) => output),
    ...used.images.map(({ output }) => output),
    ...used.captures.map(({ contextOutput }) => contextOutput),
    ...used.illustrations.map(({ output }) => output),
    '_headers',
    '_redirects',
    'robots.txt',
    'sitemap.xml',
  ].sort();
}
