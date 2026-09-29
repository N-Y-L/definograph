// Self-test of the recorded-view pipeline, run by `npm run check`. It imports the hand-written
// fixture batch (scripts/fixtures/views/fixture-1, not Definograph output and never published)
// into a temporary directory, renders its figure, and confirms that each rule rejects a
// deliberately broken fragment or stylesheet. Returns a list of failures.
import { createHash } from 'node:crypto';
import { cpSync, existsSync, mkdirSync, mkdtempSync, readFileSync, readdirSync, rmSync, statSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { crc32, deflateSync } from 'node:zlib';
import { hasClass, parseHtml } from './html.mjs';
import { importBatch, sizing } from './import-views.mjs';
import { fragmentBody, keyframePlan, loadViews, renderViewFigure, samePlan, scopeViewCss, validateFragment, validateViewCss, VIEWS_MANIFEST } from './views.mjs';

const hash = (data) => createHash('sha256').update(data).digest('hex');

// A tiny valid PNG (grey pixels), for the capture-only case.
function makePng(width, height) {
  const chunk = (type, data) => {
    const out = Buffer.alloc(12 + data.length);
    out.writeUInt32BE(data.length, 0);
    out.write(type, 4, 'latin1');
    data.copy(out, 8);
    out.writeUInt32BE(crc32(Buffer.concat([Buffer.from(type, 'latin1'), data])), 8 + data.length);
    return out;
  };
  const header = Buffer.alloc(13);
  header.writeUInt32BE(width, 0);
  header.writeUInt32BE(height, 4);
  header[8] = 8; // bit depth
  header[9] = 0; // greyscale
  const rows = Buffer.alloc((width + 1) * height, 0x80);
  for (let y = 0; y < height; y += 1) rows[y * (width + 1)] = 0;
  return Buffer.concat([Buffer.from([0x89, 0x50, 0x4e, 0x47, 0x0d, 0x0a, 0x1a, 0x0a]), chunk('IHDR', header), chunk('IDAT', deflateSync(rows)), chunk('IEND', Buffer.alloc(0))]);
}

function filesUnder(dir) {
  return readdirSync(dir).flatMap((name) => {
    const file = path.join(dir, name);
    return statSync(file).isDirectory() ? filesUnder(file) : [file];
  });
}

const FRAGMENT_CASES = [
  ['style attribute', (f) => f.replace('<section class="fx-card"', '<section style="color:red" class="fx-card"'), /style attribute/],
  ['script element', (f) => f.replace('</section>', '<script>alert(1)</script></section>'), /<script>/],
  ['event handler', (f) => f.replace('<section class="fx-card"', '<section onclick="go()" class="fx-card"'), /event handler/],
  ['link to another page', (f) => f.replace('</section>', '<a href="https://example.com/">out</a></section>'), /<a>/],
  ['external url() reference', (f) => f.replace('url(#fixture-card-arrow)', 'url(https://example.com/a.svg#m)'), /url\(/],
  ['id without the view prefix', (f) => f.replace('id="fixture-card-title"', 'id="title"').replace('aria-labelledby="fixture-card-title"', 'aria-labelledby="title"'), /must start with/],
  ['reference outside the view', (f) => f.replace('aria-labelledby="fixture-card-title"', 'aria-labelledby="fixture-card-missing"'), /not in this view/],
  ['form control', (f) => f.replace('</section>', '<button type="button">go</button></section>'), /<button>/],
  ['interactive role', (f) => f.replace('role="group"', 'role="button"'), /operable widget/],
  ['pressed state', (f) => f.replace('role="group"', 'role="group" aria-pressed="false"'), /aria-pressed/],
  ['positive tabindex', (f) => f.replace('<section class="fx-card"', '<section tabindex="2" class="fx-card"'), /tabindex/],
  ['unnamed focus stop', (f) => f.replace('<p class="fx-note">', '<p class="fx-note" tabindex="0">'), /accessible name/],
  ['image', (f) => f.replace('</section>', '<img src="/x.png" alt="x" width="1" height="1"></section>'), /<img>/],
  ['local path', (f) => f.replace('Test fixture for', 'In /Users/someone/work: test fixture for'), /home directory/],
  ['omission marker hidden from assistive technology', (f) => f.replace('</section>', '<div data-dg-gap="" aria-hidden="true"></div></section>'), /must not be aria-hidden/],
  ['omission marker without text', (f) => f.replace('</section>', '<div data-dg-gap=""></div></section>'), /needs text that announces the omission/],
  ['temporary path', (f) => f.replace('Test fixture for', 'From /private/tmp/run: test fixture for'), /private system path|temporary/],
  ['run identifier', (f) => f.replace('data-view-id="fixture-card"', 'data-view-id="fixture-card" data-run="3f2a9c1e-0b7d-4e5f-9a8b-1c2d3e4f5a6b"'), /UUID/],
  ['short attempt id', (f) => f.replace('inert control</span>', 'attempt 1 (19da1ecd)</span>'), /short hexadecimal identifier/],
  ['Linux home path', (f) => f.replace('Test fixture for', 'Saved from /home/alice/work: test fixture for'), /Linux home directory/],
  ['wrong view id on the root', (f) => f.replace('data-view-id="fixture-card"', 'data-view-id="other"'), /data-view-id/],
  ['two roots', (f) => `${f}<div class="dg-view dg-view--fixture" data-view-id="fixture-card"></div>`, /exactly one root/],
  ['directive text', (f) => f.replace('inert control</span>', '{{view:other}}</span>'), /reserves/],
  ['comment', (f) => f.replace('</section>', '<!-- note --></section>'), /comment/],
  ['foreignObject', (f) => f.replace('</svg>', '<foreignObject><p>x</p></foreignObject></svg>'), /foreignobject/],
  ['reference to another document', (f) => f.replace('</defs>', '</defs><use href="/other.svg#a"></use>'), /href/],
];

const CSS_CASES = [
  ['unscoped selector', (c) => `${c}\np{color:red}`, /not scoped/],
  ['root selector', (c) => `${c}\n:root{--x:1}`, /not scoped/],
  ['body selector', (c) => `${c}\nbody .dg-view{color:red}`, /not scoped/],
  ['modifier class alone', (c) => `${c}\n.dg-view--fixture .x{color:red}`, /not scoped/],
  ['sibling of the root', (c) => `${c}\n.dg-view ~ p{color:red}`, /sibling/],
  ['@import', (c) => `@import "other.css";\n${c}`, /@import/],
  ['@font-face', (c) => `${c}\n@font-face{font-family:x;src:local(x)}`, /@font-face/],
  ['external url()', (c) => `${c}\n.dg-view .x{background:url(https://example.com/a.png)}`, /url\(\)/],
  ['data url()', (c) => `${c}\n.dg-view .x{background:url(data:image/png;base64,AAAA)}`, /url\(\)/],
  ['position: fixed', (c) => `${c}\n.dg-view .x{position:fixed}`, /position: fixed/],
  ['@layer', (c) => `${c}\n@layer x{.dg-view .y{color:red}}`, /@layer/],

  ['nested rule', (c) => `${c}\n.dg-view .x{color:red;.y{color:blue}}`, /nested/],
  ['animation without its keyframes', (c) => `${c}\n.dg-view .fx-card{animation:vanish 1s}`, /does not define/],
  ['keyframes named like a keyword', (c) => `${c}\n@keyframes ease{to{opacity:1}}`, /keyword of the animation property/],
  ['animation name from a variable', (c) => `${c}\n.dg-view .fx-card{animation:var(--motion) 1s}`, /name its keyframes directly/],
  ['local path in a comment', (c) => `/* built in /Users/someone/project */\n${c}`, /home directory/],
];

export function runViewSelfTest(root) {
  const failures = [];
  const fixture = path.join(root, 'scripts/fixtures/views/fixture-1');
  const fragment = readFileSync(path.join(fixture, 'fixture-card/fragment.html'), 'utf8');
  const css = readFileSync(path.join(fixture, 'views.css'), 'utf8');

  // The fixture itself passes, and each broken variant is rejected for the expected reason.
  const good = validateFragment(fragment, { id: 'fixture-card', kind: 'fixture' });
  if (good.errors.length) failures.push(`the fixture fragment should pass: ${good.errors.join('; ')}`);
  // An identifier the batch declares as displayed by the reader is allowed; any other is not.
  const attempt = fragment.replace('inert control</span>', 'attempt 4 (eb5d6a75)</span>');
  const declared = validateFragment(attempt, { id: 'fixture-card', kind: 'fixture', displayed: ['eb5d6a75'] });
  if (declared.errors.length) failures.push(`a declared displayed identifier must be allowed: ${declared.errors.join('; ')}`);
  const other = validateFragment(attempt.replace('</section>', '<span class="fx-note">attempt 5 (1e99cbdf)</span></section>'), { id: 'fixture-card', kind: 'fixture', displayed: ['eb5d6a75'] });
  if (!other.errors.some((error) => /short hexadecimal identifier/.test(error))) failures.push('an identifier the batch does not declare must still be rejected');
  const absent = validateFragment(fragment, { id: 'fixture-card', kind: 'fixture', displayed: ['eb5d6a75'] });
  if (!absent.errors.some((error) => /does not show/.test(error))) failures.push('a declared identifier the fragment does not show must be reported');
  // Only in visible text: the same declared string in an attribute, or in an SVG tooltip,
  // still fails.
  const inAttribute = attempt.replace('role="group"', 'role="group" data-attempt="attempt 4 (eb5d6a75)"');
  if (!validateFragment(inAttribute, { id: 'fixture-card', kind: 'fixture', displayed: ['attempt 4 (eb5d6a75)'] }).errors.some((error) => /short hexadecimal identifier/.test(error))) failures.push('a declared identifier inside an attribute must be rejected');
  const inTooltip = attempt.replace('Two boxes joined by an arrow (test fixture)', 'Two boxes (attempt 4 (eb5d6a75))');
  if (!validateFragment(inTooltip, { id: 'fixture-card', kind: 'fixture', displayed: ['attempt 4 (eb5d6a75)'] }).errors.some((error) => /short hexadecimal identifier/.test(error))) failures.push('a declared identifier inside an SVG title must be rejected');
  const fullLabel = validateFragment(attempt, { id: 'fixture-card', kind: 'fixture', displayed: ['attempt 4 (eb5d6a75)'] });
  if (fullLabel.errors.length) failures.push(`a declared full label in visible text must be allowed: ${fullLabel.errors.join('; ')}`);
  // An internal node path that merely contains "/home/" is not a home directory.
  const nodePath = validateFragment(fragment.replace('data-view-id="fixture-card"', 'data-view-id="fixture-card" data-node="node:checking/steps/1/output/result/home/telescope/1"'), { id: 'fixture-card', kind: 'fixture' });
  if (nodePath.errors.length) failures.push(`an internal node path is not a private path: ${nodePath.errors.join('; ')}`);
  const announced = fragment.replace('</section>', '<div data-dg-gap=""><span class="dg-visually-hidden">Part of the panel is left out here</span></div></section>');
  const announcedResult = validateFragment(announced, { id: 'fixture-card', kind: 'fixture' });
  if (announcedResult.errors.length) failures.push(`an announced omission marker should pass: ${announcedResult.errors.join('; ')}`);
  for (const [name, mutate, reason] of FRAGMENT_CASES) {
    const broken = mutate(fragment);
    if (broken === fragment) failures.push(`fragment case "${name}" did not change the fixture`);
    const { errors } = validateFragment(broken, { id: 'fixture-card', kind: 'fixture' });
    if (!errors.some((error) => reason.test(error))) failures.push(`fragment rule not enforced: ${name} (${errors.join('; ') || 'no errors'})`);
  }
  const goodCss = validateViewCss(css);
  if (goodCss.errors.length) failures.push(`the fixture stylesheet should pass: ${goodCss.errors.join('; ')}`);
  for (const [name, mutate, reason] of CSS_CASES) {
    const { errors } = validateViewCss(mutate(css));
    if (!errors.some((error) => reason.test(error))) failures.push(`stylesheet rule not enforced: ${name} (${errors.join('; ') || 'no errors'})`);
  }

  // Publishing keeps a batch's @keyframes, renamed dg-<batch>-<name> with every use, when a rule
  // that could apply to one of its fragments uses them (classes inside :not() are not
  // required); it drops the others (unused, or used only by rules no fragment can match), and
  // those rules name none instead.
  const animatedCss = `${css}\n@keyframes spin{to{opacity:1}}\n.dg-view .fx-card{animation:spin 1s linear infinite}\n@keyframes glow{to{opacity:1}}\n.dg-view .fx-note:not(.fx-absent){animation-name:glow}\n@keyframes pulse{to{opacity:1}}\n.dg-view .fx-spinner{animation:pulse 2s ease-in-out}`;
  const plan = keyframePlan(animatedCss, 'fixture-1', [validateFragment(fragment, { id: 'fixture-card', kind: 'fixture' }).classes]);
  if (!samePlan(plan, { renamed: { spin: 'dg-fixture-1-spin', glow: 'dg-fixture-1-glow' }, dropped: ['dg-fixture-fade', 'pulse'] })) failures.push(`unexpected keyframes plan ${JSON.stringify(plan)}`);
  const animated = scopeViewCss(animatedCss, 'fixture-1', plan);
  if (!/@keyframes dg-fixture-1-spin\{/.test(animated) || !/animation:dg-fixture-1-spin 1s linear infinite/.test(animated) || !/@keyframes dg-fixture-1-glow\{/.test(animated) || !/animation-name:dg-fixture-1-glow/.test(animated)) failures.push('published styles must rename used @keyframes and every use to dg-<batch>-<name>');
  if (/@keyframes (?:pulse|dg-fixture-1-pulse|dg-fixture-fade|dg-fixture-1-dg-fixture-fade)\b/.test(animated) || !/animation:none 2s ease-in-out/.test(animated) || /[\s:,](?:spin|glow|pulse)[\s;},]/.test(animated)) failures.push('published styles must drop unused @keyframes and name none where a rule used one');
  // A selector with escapes cannot be read reliably, so its keyframes are kept.
  const escaped = keyframePlan(`${css}\n@keyframes wave{to{opacity:1}}\n.dg-view .fx\\:wave{animation:wave 1s}`, 'fixture-1', [validateFragment(fragment, { id: 'fixture-card', kind: 'fixture' }).classes]);
  if (escaped.renamed.wave !== 'dg-fixture-1-wave') failures.push('keyframes used by a selector with escapes must be kept');
  try {
    scopeViewCss(animatedCss, 'fixture-1', { renamed: {}, dropped: [] });
    failures.push('publishing must refuse @keyframes that the recorded plan does not cover');
  } catch {
    // expected
  }

  // Widths: a width the site recorded itself wins over a batch that says the view reflows, and
  // stays across recordings; otherwise the batch decides, then an earlier import, then nothing.
  const siteWidth = { minWidthPx: 700, target: 'root', from: 'site: test' };
  const reflowing = { id: 'x', layout: { reflows: true, minWidthPx: 280 } };
  if (sizing(reflowing, '<svg></svg>', null, { siteWidth }).size !== siteWidth) failures.push('a width the site recorded wins over a batch that says the view reflows');
  if (sizing(reflowing, '<svg></svg>', null, { siteWidth: { ...siteWidth, from: 'batch manifest minWidthPx' } }).size !== null) failures.push('a reflowing view has no width unless the site recorded one');
  if (sizing({ id: 'x', layout: { reflows: false, minWidthPx: 820 } }, '<svg></svg>', null).size?.minWidthPx !== 820) failures.push('a batch minWidthPx gives the view its width');

  const scratch = mkdtempSync(path.join(os.tmpdir(), 'definograph-view-selftest-'));
  try {
    // Import: pinned hashes, draft caption, nothing private copied.
    const site = path.join(scratch, 'site');
    const first = importBatch(fixture, site);
    if (!first.drafts.includes('fixture-card')) failures.push('a newly imported view must carry a draft caption');
    if (first.batch.ready?.file !== 'READY-fixture.json' || first.batch.ready?.at !== '2026-09-27T12:00:00Z') failures.push(`the import must record the READY declaration it accepted the batch under (got ${JSON.stringify(first.batch.ready)})`);
    const copied = filesUnder(site);
    if (copied.some((file) => file.endsWith('meta.json'))) failures.push('the import copied meta.json');
    if (copied.some((file) => readFileSync(file, 'latin1').includes('PRIVATE-FIXTURE-RUN-ID'))) failures.push('the import copied private metadata');
    let loaded = loadViews(site);
    if (loaded.errors.length) failures.push(`the imported fixture should load: ${loaded.errors.join('; ')}`);
    // The import records the keyframes plan; a record that no longer matches is refused.
    if (!samePlan(first.batch.keyframes, { renamed: {}, dropped: ['dg-fixture-fade'] })) failures.push(`the import must record the keyframes plan (got ${JSON.stringify(first.batch.keyframes)})`);
    const recordFile = path.join(site, VIEWS_MANIFEST);
    const recordText = readFileSync(recordFile, 'utf8');
    const edited = JSON.parse(recordText);
    edited.batches[0].keyframes = { renamed: { 'dg-fixture-fade': 'dg-fixture-1-dg-fixture-fade' }, dropped: [] };
    writeFileSync(recordFile, JSON.stringify(edited));
    if (!loadViews(site).errors.some((error) => /keyframes .* is not what the stylesheet and fragments give/.test(error))) failures.push('a keyframes record that disagrees with the batch must be refused');
    delete edited.batches[0].keyframes;
    writeFileSync(recordFile, JSON.stringify(edited));
    if (!loadViews(site).errors.some((error) => /keyframes .*is missing/.test(error))) failures.push('a batch without its keyframes record must be refused');
    const unready = JSON.parse(recordText);
    delete unready.batches[0].ready;
    writeFileSync(recordFile, JSON.stringify(unready));
    if (!loadViews(site).errors.some((error) => /ready \(the READY declaration .*is missing/.test(error))) failures.push('a batch without the READY declaration it was accepted under must be refused');
    writeFileSync(recordFile, recordText);

    const publicSite = path.join(scratch, 'public-site');
    mkdirSync(path.join(publicSite, 'source-assets/views'), { recursive: true });
    writeFileSync(path.join(publicSite, VIEWS_MANIFEST), JSON.stringify({ version: 2, batches: [] }));
    importBatch(fixture, publicSite);
    const publicFile = path.join(publicSite, VIEWS_MANIFEST);
    const publicText = readFileSync(publicFile, 'utf8');
    const publicManifest = JSON.parse(publicText);
    if (publicManifest.version !== 2 || loadViews(publicSite).errors.length) failures.push('an import into the public manifest must remain valid version 2');
    if (['product', 'manifest', 'ready'].some((key) => key in publicManifest.batches[0])) failures.push('public manifests must not retain private capture provenance');
    publicManifest.batches[0].product = first.batch.product;
    writeFileSync(publicFile, JSON.stringify(publicManifest));
    if (!loadViews(publicSite).errors.some((e) => /unexpected public batch field product/.test(e))) failures.push('public manifests must reject private provenance');
    delete publicManifest.batches[0].product;
    publicManifest.batches[0].stylesheet.sha256 = '0'.repeat(64);
    writeFileSync(publicFile, JSON.stringify(publicManifest));
    if (!loadViews(publicSite).errors.some((e) => /pinned SHA-256/.test(e))) failures.push('public manifests must enforce stylesheet integrity');
    writeFileSync(publicFile, publicText);
    importBatch(fixture, publicSite);
    if (loadViews(publicSite).errors.length || JSON.parse(readFileSync(publicFile, 'utf8')).version !== 2) failures.push('re-import must preserve public manifest validity');

    // The import accepts a batch only when a READY file beside it (in <pipeline>, for a batch in
    // <pipeline>/public-candidates/<batch>) declares its manifest.json with the same SHA-256.
    const fixtureManifestSha = hash(readFileSync(path.join(fixture, 'manifest.json')));
    const candidate = (pipeline) => {
      const dir = path.join(scratch, pipeline, 'public-candidates', 'fixture-1');
      mkdirSync(path.dirname(dir), { recursive: true });
      cpSync(fixture, dir, { recursive: true });
      return dir;
    };
    const declare = (pipeline, file, sha, { status = 'ready', createdAt = '2026-09-28T00:00:00Z' } = {}) => writeFileSync(path.join(scratch, pipeline, file), JSON.stringify({ status, createdAt, batch: { manifest: 'public-candidates/fixture-1/manifest.json', manifestSha256: sha } }));
    const refused = (dir, pattern, what) => {
      try {
        importBatch(dir, path.join(scratch, 'site-guard'), { dryRun: true });
        failures.push(`the import must refuse ${what}`);
      } catch (error) {
        if (!pattern.test(error.message)) failures.push(`${what}: unexpected refusal: ${error.message}`);
      }
    };
    refused(candidate('undeclared'), /no READY-\*\.json/, 'a batch that no READY file declares');
    const draft = candidate('draft');
    declare('draft', 'READY-phase1.json', hash('an earlier manifest'));
    refused(draft, /declares this batch's manifest with SHA-256 [0-9a-f]{64}, but .* has [0-9a-f]{64}: a draft/, 'a manifest other than the declared one (a draft)');
    const notReady = candidate('not-ready');
    declare('not-ready', 'READY-phase1.json', fixtureManifestSha, { status: 'in progress' });
    refused(notReady, /status is "in progress"/, 'a batch declared in a READY file whose status is not ready');
    // The most recent READY file that declares the manifest decides.
    const layered = candidate('layered');
    declare('layered', 'READY-phase1.json', fixtureManifestSha, { createdAt: '2026-09-28T00:00:00Z' });
    declare('layered', 'READY-phase2.json', hash('a rebuilt manifest'), { createdAt: '2026-09-28T01:00:00Z' });
    refused(layered, /READY-phase2\.json \(2026-09-28T01:00:00Z\) declares this batch's manifest/, 'a batch whose most recent declaration names another manifest');
    declare('layered', 'READY-phase3.json', fixtureManifestSha, { createdAt: '2026-09-28T02:00:00Z' });
    try {
      const accepted = importBatch(layered, path.join(scratch, 'site-guard'), { dryRun: true });
      if (accepted.batch.ready?.file !== 'READY-phase3.json') failures.push('the most recent matching READY file must be recorded');
    } catch (error) {
      failures.push(`a batch whose most recent declaration matches must be accepted: ${error.message}`);
    }

    // A reviewed caption survives a re-import of the same batch.
    const manifestFile = path.join(site, VIEWS_MANIFEST);
    const allowlist = JSON.parse(readFileSync(manifestFile, 'utf8'));
    Object.assign(allowlist.batches[0].views[0], { caption: 'Reviewed fixture caption.', label: 'Fixture view' });
    delete allowlist.batches[0].views[0].captionDraft;
    writeFileSync(manifestFile, JSON.stringify(allowlist));
    const second = importBatch(fixture, site);
    const kept = second.batch.views[0];
    if (kept.caption !== 'Reviewed fixture caption.' || kept.label !== 'Fixture view' || kept.captionDraft) failures.push('a re-import must keep reviewed captions and labels');

    // The figure: provenance, exact source, focusable named scroll region, unchanged fragment.
    loaded = loadViews(site);
    const view = loaded.views.get('fixture-card');
    const html = renderViewFigure(view);
    const doc = parseHtml(html);
    if (doc.errors.length) failures.push(`the figure does not parse: ${doc.errors.join('; ')}`);
    const figure = doc.elements[0];
    const children = doc.elements.filter((element) => element.parent === figure);
    if (figure?.name !== 'figure' || !hasClass(figure, 'dg-figure')) failures.push('the figure must be <figure class="dg-figure">');
    if (!hasClass(children[0] ?? figure, 'dg-provenance') || !/Recorded Definograph output · Lean 4\.28\.0 · 27 September 2026/.test(doc.text(children[0] ?? figure))) failures.push('the figure must open with its provenance');
    if (!doc.elements.some((element) => element.name === 'time' && element.attrs.get('datetime') === '2026-09-27')) failures.push('the provenance must carry the recording date');
    const scroll = doc.elements.find((element) => hasClass(element, 'dg-scroll'));
    if (scroll?.attrs.get('role') !== 'region' || scroll?.attrs.get('tabindex') !== '0' || !scroll?.attrs.get('aria-label')) failures.push('the view needs a focusable, named scroll region');
    if (!html.includes(fragmentBody(view))) failures.push('the figure must contain the fragment unchanged');
    const code = doc.elements.find((element) => element.attrs.get('data-view-source') === 'fixture-card');
    if (!code || doc.text(code) !== view.sourceText) failures.push('the figure must show the exact source');
    if (children.at(-1)?.name !== 'figcaption') failures.push('the figure must end with its caption');

    // A changed file no longer matches its pin.
    const fragmentFile = path.join(site, 'source-assets/views/fixture-1/fixture-card/fragment.html');
    writeFileSync(fragmentFile, `${readFileSync(fragmentFile, 'utf8')} `);
    if (!loadViews(site).errors.some((error) => /does not match its pinned SHA-256/.test(error))) failures.push('a changed fragment must fail its pinned hash');

    // A later batch supersedes the fixture: the old batch leaves the allowlist and the site,
    // reviewed text is carried over but marked for review because the recording changed, and
    // a screenshot without a recorded view (capture-only) is accepted.
    const next = path.join(scratch, 'pipeline', 'public-candidates', 'fixture-2');
    mkdirSync(path.dirname(next), { recursive: true });
    cpSync(fixture, next, { recursive: true });
    const changed = readFileSync(path.join(next, 'fixture-card/fragment.html'), 'utf8').replace('inert control</span>', 'inert control (changed)</span>');
    writeFileSync(path.join(next, 'fixture-card/fragment.html'), changed);
    mkdirSync(path.join(next, 'fixture-shot'));
    writeFileSync(path.join(next, 'fixture-shot/context@2x.png'), makePng(4, 2));
    const nextManifest = JSON.parse(readFileSync(path.join(next, 'manifest.json'), 'utf8'));
    nextManifest.batch = 'fixture-2';
    nextManifest.views[0].sha256.fragment = hash(changed);
    nextManifest.views.push({ id: 'fixture-shot', kind: 'app-context', title: 'Test fixture screenshot', files: { context: 'fixture-shot/context@2x.png' }, sha256: { context: hash(readFileSync(path.join(next, 'fixture-shot/context@2x.png'))) } });
    writeFileSync(path.join(next, 'manifest.json'), JSON.stringify(nextManifest));
    writeFileSync(path.join(scratch, 'pipeline', 'READY-phase2.json'), JSON.stringify({ status: 'complete', createdAt: '2026-09-28T00:00:00Z', batch: { manifest: 'public-candidates/fixture-2/manifest.json', manifestSha256: hash(readFileSync(path.join(next, 'manifest.json'))) } }));
    const third = importBatch(next, site, { replaces: ['fixture-1'] });
    const after = JSON.parse(readFileSync(manifestFile, 'utf8'));
    if (after.batches.map((batch) => batch.batch).join(' ') !== 'fixture-2' || existsSync(path.join(site, 'source-assets/views/fixture-1'))) failures.push('--replaces must remove the superseded batch from the allowlist and the site');
    const carried = third.batch.views.find((view) => view.id === 'fixture-card');
    if (carried?.caption !== 'Reviewed fixture caption.' || !carried?.captionDraft) failures.push('a changed recording keeps its reviewed caption as text but marks it for review');
    const shot = third.batch.views.find((view) => view.id === 'fixture-shot');
    if (!shot?.context || shot.fragment || shot.caption !== undefined) failures.push('a capture-only entry is imported without a fragment or caption');
    const superseded = loadViews(site);
    if (superseded.errors.length) failures.push(`the superseding batch should load: ${superseded.errors.join('; ')}`);
    else if (!superseded.views.get('fixture-shot')?.captureOnly || !superseded.views.get('fixture-shot')?.contextIncomplete) failures.push('a capture-only entry loads as a capture awaiting its alt text and caption');

    // A new screenshot for the same id keeps the reviewed alt text and caption as text, marked
    // for review (textDraft), and loads as a draft that the build will not publish.
    const reviewed = JSON.parse(readFileSync(manifestFile, 'utf8'));
    Object.assign(reviewed.batches[0].views.find((view) => view.id === 'fixture-shot').context, { alt: 'Reviewed fixture alt text.', caption: 'Reviewed fixture screenshot caption.' });
    writeFileSync(manifestFile, JSON.stringify(reviewed));
    const reviewedShot = loadViews(site);
    if (reviewedShot.errors.length || reviewedShot.views.get('fixture-shot')?.contextIncomplete || reviewedShot.views.get('fixture-shot')?.contextDraft) failures.push('a capture with reviewed alt text and caption loads ready to publish');
    const retaken = path.join(scratch, 'pipeline', 'public-candidates', 'fixture-3');
    cpSync(next, retaken, { recursive: true });
    writeFileSync(path.join(retaken, 'fixture-shot/context@2x.png'), makePng(6, 2));
    const retakenManifest = JSON.parse(readFileSync(path.join(retaken, 'manifest.json'), 'utf8'));
    retakenManifest.batch = 'fixture-3';
    retakenManifest.views.find((view) => view.id === 'fixture-shot').sha256.context = hash(readFileSync(path.join(retaken, 'fixture-shot/context@2x.png')));
    // The same batch brings a new view whose id marks it as an excerpt (part of a panel).
    cpSync(path.join(retaken, 'fixture-card'), path.join(retaken, 'fixture-card-excerpt'), { recursive: true });
    const excerptFragment = readFileSync(path.join(retaken, 'fixture-card-excerpt/fragment.html'), 'utf8').replaceAll('fixture-card', 'fixture-card-excerpt');
    writeFileSync(path.join(retaken, 'fixture-card-excerpt/fragment.html'), excerptFragment);
    // Its public metadata says it is an excerpt and was drawn from a saved record.
    const excerptMeta = JSON.stringify({ ...JSON.parse(readFileSync(path.join(retaken, 'fixture-card-excerpt/meta.json'), 'utf8')), excerpt: { isExcerpt: true }, recordedState: { savedRecord: true } });
    writeFileSync(path.join(retaken, 'fixture-card-excerpt/meta.json'), excerptMeta);
    const cardEntry = retakenManifest.views.find((view) => view.id === 'fixture-card');
    retakenManifest.views.push({
      ...cardEntry,
      id: 'fixture-card-excerpt',
      files: Object.fromEntries(Object.entries(cardEntry.files).map(([key, file]) => [key, file.replace('fixture-card/', 'fixture-card-excerpt/')])),
      sha256: { ...cardEntry.sha256, fragment: hash(excerptFragment), meta: hash(excerptMeta) },
    });
    writeFileSync(path.join(retaken, 'manifest.json'), JSON.stringify(retakenManifest));
    writeFileSync(path.join(scratch, 'pipeline', 'READY-phase3.json'), JSON.stringify({ status: 'complete', createdAt: '2026-09-28T01:00:00Z', batch: { manifest: 'public-candidates/fixture-3/manifest.json', manifestSha256: hash(readFileSync(path.join(retaken, 'manifest.json'))) } }));
    const fourth = importBatch(retaken, site, { replaces: ['fixture-2'] });
    const reshot = fourth.batch.views.find((view) => view.id === 'fixture-shot')?.context;
    if (reshot?.alt !== 'Reviewed fixture alt text.' || reshot?.caption !== 'Reviewed fixture screenshot caption.' || reshot?.textDraft !== true) failures.push('a changed screenshot keeps its reviewed alt text and caption as text but marks them for review');
    if (!fourth.drafts.includes('fixture-shot')) failures.push('the import lists a screenshot whose text waits for review');
    const retakenViews = loadViews(site);
    if (retakenViews.errors.length) failures.push(`the batch with a new screenshot should load: ${retakenViews.errors.join('; ')}`);
    else if (!retakenViews.views.get('fixture-shot')?.contextDraft) failures.push('a screenshot whose text is marked for review loads as a draft');

    // An excerpt and a saved record are marked on import from the view's public metadata; the
    // excerpt's reviewed caption must say that it shows part of a panel, and its figure says
    // so in the provenance line, with dashed frame edges and a note for assistive technology.
    const excerptEntry = fourth.batch.views.find((view) => view.id === 'fixture-card-excerpt');
    if (excerptEntry?.excerpt !== true || excerptEntry?.savedRecord !== true || !excerptEntry?.captionDraft) failures.push('a new view whose metadata says excerpt.isExcerpt and recordedState.savedRecord is imported as an excerpt from a saved record, with a draft caption');
    const plainEntry = fourth.batch.views.find((view) => view.id === 'fixture-card');
    if (plainEntry?.excerpt !== undefined || plainEntry?.savedRecord !== undefined) failures.push('a view whose metadata says neither is not marked as an excerpt or a saved record');
    const withExcerpt = (caption) => {
      const allowlistNow = JSON.parse(readFileSync(manifestFile, 'utf8'));
      const entry = allowlistNow.batches[0].views.find((view) => view.id === 'fixture-card-excerpt');
      entry.caption = caption;
      delete entry.captionDraft;
      writeFileSync(manifestFile, JSON.stringify(allowlistNow));
      return loadViews(site);
    };
    if (!withExcerpt('The fixture card, in part.').errors.some((error) => /an excerpt's caption begins with "Excerpt" or "Part of"/.test(error))) failures.push('an excerpt whose caption does not begin with "Excerpt" or "Part of" is refused');
    if (withExcerpt('Part of the fixture card.').errors.length) failures.push('an excerpt caption may begin with "Part of"');
    const excerptViews = withExcerpt('Excerpt from the fixture card.');
    if (excerptViews.errors.length) failures.push(`an excerpt with a reviewed caption should load: ${excerptViews.errors.join('; ')}`);
    else {
      const excerptFigure = parseHtml(renderViewFigure(excerptViews.views.get('fixture-card-excerpt')));
      const excerptProvenance = excerptFigure.elements.find((element) => hasClass(element, 'dg-provenance'));
      if (!excerptProvenance || !/^Recorded Definograph excerpt · from a saved history · Lean 4\.28\.0 · /.test(excerptFigure.text(excerptProvenance).trim())) failures.push('an excerpt drawn from a saved record opens with the provenance "Recorded Definograph excerpt · from a saved history"');
      const excerptRoot = excerptFigure.elements[0];
      const excerptChildren = excerptFigure.elements.filter((element) => element.parent === excerptRoot);
      const note = excerptChildren.findIndex((element) => hasClass(element, 'visually-hidden'));
      const frame = excerptChildren.findIndex((element) => hasClass(element, 'dg-scroll'));
      if (!hasClass(excerptRoot, 'dg-figure-excerpt') || note === -1 || note > frame || !/rest of the panel is left out/.test(excerptFigure.text(excerptChildren[note]))) failures.push('an excerpt figure has dashed frame edges and says before the view that the rest of the panel is left out');
      const cardFigure = parseHtml(renderViewFigure(excerptViews.views.get('fixture-card')));
      const cardProvenance = cardFigure.text(cardFigure.elements.find((element) => hasClass(element, 'dg-provenance')));
      if (!/^Recorded Definograph output · Lean /.test(cardProvenance.trim())) failures.push('a figure that is not an excerpt or a saved record keeps the provenance "Recorded Definograph output · Lean …"');
      if (hasClass(cardFigure.elements[0], 'dg-figure-excerpt') || cardFigure.elements.some((element) => hasClass(element, 'visually-hidden'))) failures.push('a figure that is not an excerpt is not marked as one');
    }

    // A retaken screenshot can come in a batch of its own (--replaces-view): it moves to that
    // batch with its text kept for review, and the batch that held it keeps its other views.
    const alone = path.join(scratch, 'pipeline', 'public-candidates', 'fixture-4');
    mkdirSync(path.join(alone, 'fixture-shot'), { recursive: true });
    cpSync(path.join(retaken, 'views.css'), path.join(alone, 'views.css'));
    writeFileSync(path.join(alone, 'fixture-shot/context@2x.png'), makePng(8, 2));
    // The same batch brings a new screenshot whose manifest entry proposes its alt text and caption.
    mkdirSync(path.join(alone, 'fixture-panel'), { recursive: true });
    writeFileSync(path.join(alone, 'fixture-panel/context@2x.png'), makePng(10, 2));
    const aloneManifest = { ...retakenManifest, batch: 'fixture-4', views: [
      { id: 'fixture-shot', kind: 'app-context', title: 'Test fixture screenshot', files: { context: 'fixture-shot/context@2x.png' }, sha256: { context: hash(readFileSync(path.join(alone, 'fixture-shot/context@2x.png'))) } },
      { id: 'fixture-panel', kind: 'panel-capture', title: 'Test fixture panel', alt: 'Proposed alt text.', caption: 'Proposed caption <b>as text</b>.', files: { context: 'fixture-panel/context@2x.png' }, sha256: { context: hash(readFileSync(path.join(alone, 'fixture-panel/context@2x.png'))) } },
    ] };
    writeFileSync(path.join(alone, 'manifest.json'), JSON.stringify(aloneManifest));
    writeFileSync(path.join(scratch, 'pipeline', 'READY-phase4.json'), JSON.stringify({ status: 'complete', createdAt: '2026-09-28T02:00:00Z', batch: { manifest: 'public-candidates/fixture-4/manifest.json', manifestSha256: hash(readFileSync(path.join(alone, 'manifest.json'))) } }));
    const refusedAlone = (options, pattern, what) => {
      try {
        importBatch(alone, site, { dryRun: true, ...options });
        failures.push(`the import must refuse ${what}`);
      } catch (error) {
        if (!pattern.test(error.message)) failures.push(`${what}: unexpected refusal: ${error.message}`);
      }
    };
    refusedAlone({}, /another batch in the allowlist already uses this id/, 'a screenshot whose id another batch holds, without --replaces-view');
    refusedAlone({ replacesViews: ['fixture-card'] }, /only a screenshot can be replaced on its own/, 'a recorded view replaced without its batch');
    const fifth = importBatch(alone, site, { replacesViews: ['fixture-shot'] });
    const afterMove = JSON.parse(readFileSync(manifestFile, 'utf8'));
    const holderAfter = afterMove.batches.find((batch) => batch.batch === 'fixture-3');
    if (afterMove.batches.map((batch) => batch.batch).join(' ') !== 'fixture-3 fixture-4' || holderAfter?.views.some((view) => view.id === 'fixture-shot') || holderAfter?.views.length !== 2 || existsSync(path.join(site, 'source-assets/views/fixture-3/fixture-shot')) || !existsSync(path.join(site, 'source-assets/views/fixture-3/fixture-card'))) failures.push('--replaces-view moves the screenshot to the new batch and leaves the rest of its old batch in place');
    const proposedShot = fifth.batch.views.find((view) => view.id === 'fixture-panel')?.context;
    if (proposedShot?.alt !== 'Proposed alt text.' || proposedShot?.caption !== 'Proposed caption &lt;b&gt;as text&lt;/b&gt;.' || proposedShot?.textDraft !== true) failures.push('a new screenshot takes the alt text and caption its batch proposes, as plain text marked for review');
    const movedShot = fifth.batch.views[0]?.context;
    if (movedShot?.textDraft !== true || movedShot?.alt !== 'Reviewed fixture alt text.' || movedShot?.caption !== 'Reviewed fixture screenshot caption.') failures.push('a moved screenshot keeps its text, marked for review');
    const moved = loadViews(site);
    if (moved.errors.length) failures.push(`the allowlist after --replaces-view should load: ${moved.errors.join('; ')}`);

    // The import refuses a batch whose files do not match the batch manifest.
    const tampered = path.join(scratch, 'pipeline', 'public-candidates', 'tampered');
    cpSync(fixture, tampered, { recursive: true });
    writeFileSync(path.join(tampered, 'fixture-card/source.lean'), '∀ n : Nat, n = 0\n');
    writeFileSync(path.join(scratch, 'pipeline', 'READY-tampered.json'), JSON.stringify({ status: 'ready', createdAt: '2026-09-28T00:00:00Z', batch: { manifest: 'public-candidates/tampered/manifest.json', manifestSha256: fixtureManifestSha } }));
    try {
      importBatch(tampered, path.join(scratch, 'site-2'));
      failures.push('the import must refuse a file that does not match the batch manifest');
    } catch (error) {
      if (!/does not match the batch manifest/.test(error.message)) failures.push(`unexpected import failure: ${error.message}`);
    }
  } catch (error) {
    failures.push(`self-test crashed: ${error.stack ?? error.message}`);
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
  return { failures, cases: FRAGMENT_CASES.length + CSS_CASES.length };
}
