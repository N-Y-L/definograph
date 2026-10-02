// Build-time regression fixtures, never Product recordings or published figures.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { importBatch, sizing } from './import-views.mjs';
import { escapeHtml } from './format.mjs';
import { parseHtml } from './html.mjs';
import { MATH_ASSETS, canonicalFontCss, mathAssetOutputs, publishedMathCss, publishedMathFiles, readMathAsset, validateMathAssetContract, validatePublishedMathCss, verifyMathAssets } from './math-assets.mjs';
import { loadViews, validateFragment, validateViewCss, VIEWS_MANIFEST } from './views.mjs';
const hash = data => createHash('sha256').update(data).digest('hex');
export function runMathSelfTest(root) {
  const failures = [];
  let cases = 0;
  const test = (name, run) => { cases += 1; try { run(); } catch (error) { failures.push(`${name}: ${error.message}`); } };
  test('measured math reflow retains its 600px safe floor; legacy reflow unchanged', () => {
    const view = { minWidthPx: 600, reflows: true };
    assert.equal(sizing(view, '<svg></svg>', null, { honorMeasuredMinimum: true }).size.minWidthPx, 600);
    assert.equal(sizing(view, '<svg></svg>', null).size, null);
  });
  test('site-owned sizing cannot undercut a newly measured math floor', () => {
    const view = { minWidthPx: 600, reflows: true };
    for (const previous of [500, 700]) assert.equal(sizing(view, '<svg></svg>', null, { honorMeasuredMinimum: true, siteWidth: { minWidthPx: previous, target: 'root', from: 'site: reviewed width' } }).size.minWidthPx, Math.max(600, previous));
  });
  test('math sizing refuses absent or invalid measured minima', () => {
    for (const minWidthPx of [undefined, null, 0, -1, 400.5]) assert.throws(() => sizing({ minWidthPx, reflows: true }, '<svg></svg>', null, { honorMeasuredMinimum: true }), /positive integer/);
  });
  const fixture = path.join(root, 'scripts/fixtures/math');
  const read = relative => readMathAsset(fixture, relative);
  const fragment = readFileSync(path.join(fixture, 'epsilon.html'), 'utf8');
  const options = { id: 'fixture-math', kind: 'fixture', mathAssetsVerified: true };
  const rejected = (text, reason) => assert.ok(validateFragment(text, options).errors.some(error => reason.test(error)), validateFragment(text, options).errors.join('\n'));
  for (const name of ['depends', 'epsilon']) test(`source-derived ${name} markup and extracted styles pass`, () => {
    assert.deepEqual(validateFragment(readFileSync(path.join(fixture, `${name}.html`), 'utf8'), options).errors, []);
    assert.deepEqual(validateViewCss(readFileSync(path.join(fixture, `${name}.css`), 'utf8')).errors, []);
  });
  for (const [prefix, suffix] of [['center ', ''], ['', ' (either endpoint)'], ['Distance from ', ' · all 2 dimensions'], ['', '']]) test(`Product prose key: ${JSON.stringify([prefix, suffix])}`, () => {
    const doc = parseHtml(fragment);
    const group = doc.elements.find(node => node.name === 'g');
    const source = group.attrs.get('data-diagram-source');
    const key = group.attrs.get('data-math-label');
    let changed = fragment.replace(`data-diagram-source="${escapeHtml(source)}"`, `data-diagram-source="${escapeHtml(prefix + source + suffix)}"`)
      .replace(`aria-label="${escapeHtml(source)}"`, `aria-label="${escapeHtml(prefix + source + suffix)}"`)
      .replace(`<title>${escapeHtml(source)}</title>`, `<title>${escapeHtml(prefix + source + suffix)}</title>`)
      .replace(`data-math-label="${escapeHtml(key)}"`, `data-math-label="${escapeHtml(prefix + '\n' + key + '\n' + suffix)}"`);
    if (prefix) changed = changed.replace('<span class="diagram-math-typeset">', `<span class="diagram-math-prose">${escapeHtml(prefix)}</span><span class="diagram-math-typeset">`);
    if (suffix) changed = changed.replace('<span data-math-baseline=', `<span class="diagram-math-prose">${escapeHtml(suffix)}</span><span data-math-baseline=`);
    assert.deepEqual(validateFragment(changed, options).errors, []);
    if (prefix || suffix) rejected(changed.replace('class="diagram-math-prose">', 'class="diagram-math-prose">wrong '), /measurement key|Product order/);
  });
  test('base36 extracted style classes on MathML', () => {
    const changed = fragment.replace('<math ', '<math class="dg-s-g9zv2" ');
    assert.deepEqual(validateFragment(changed, options).errors, []);
  });
  test('same markup still refused without verified math assets', () => assert.ok(validateFragment(fragment, { ...options, mathAssetsVerified: false }).errors.some(error => /foreignobject/.test(error))));
  const fixtureDoc = parseHtml(fragment);
  const actualKatex = fixtureDoc.elements.find(node => node.attrs.get('class') === 'katex');
  const katexMarkup = fragment.slice(actualKatex.start, actualKatex.end);
  const source = fixtureDoc.elements.find(node => node.name === 'g').attrs.get('data-diagram-source');
  const inline = `<div class="dg-view dg-view--fixture" data-view-id="fixture-math"><span class="rm-law-math" data-math-source="${escapeHtml(source)}" aria-label="${escapeHtml(source)}">${katexMarkup}</span></div>`;
  const fallback = `<div class="dg-view dg-view--fixture" data-view-id="fixture-math"><span class="rm-law-math" data-math-source="opaque source" data-math-fallback="source">opaque source</span></div>`;
  test('inline law actual strict KaTeX needs no foreignObject', () => assert.deepEqual(validateFragment(inline, options).errors, []));
  test('inline source fallback remains exact ordinary text', () => assert.deepEqual(validateFragment(fallback, options).errors, []));
  test('inline law refuses absent approved font contract', () => assert.ok(validateFragment(inline, {...options, mathAssetsVerified:false}).errors.some(e=>/verified math assets/.test(e))));
  for (const [name, changed, reason] of [
    ['inline source mismatch', inline.replace('aria-label="', 'aria-label="wrong '), /accessible label/],
    ['inline unexpected host attribute', inline.replace('class="rm-law-math"', 'class="rm-law-math" data-other="yes"'), /unexpected attribute/],
    ['inline lost MathML', inline.replace('class="katex-mathml"', 'class="other"'), /MathML/],
    ['inline nested markup fallback', fallback.replace('>opaque source</span>', '><span>opaque source</span></span>'), /exact plain source/],
    ['inline changed fallback text', fallback.replace('>opaque source</span>', '>changed</span>'), /exact plain source/],
    ['inline external source URL', inline.replace('data-math-source="', 'data-math-source="https://example.test/'), /URL/],
    ['inline directive annotation', inline.replace('</annotation>', '{{view:other}}</annotation>'), /directive syntax/],
  ]) test(name, () => rejected(changed, reason));
  const mutations = [
    ['arbitrary foreignObject', s => s.replace('<foreignObject ', '<foreignObject data-other="true" '), /unexpected attribute/],
    ['unrecognized group', s => s.replace('class="diagram-math-label"', 'class="other"'), /requires the Product/],
    ['source disagreement', s => s.replace('<title>', '<title>different '), /must agree/],
    ['measurement key is not a native id', s => s.replace('data-math-label="', 'data-math-label="wrong '), /measurement key/],
    ['lost MathML', s => s.replace('class="katex-mathml"', 'class="other"'), /MathML and visual/],
    ['hidden MathML', s => s.replace('class="katex-mathml"', 'class="katex-mathml" aria-hidden="true"'), /must remain accessible/],
    ['visual tree exposed twice', s => s.replace('class="katex-html" aria-hidden="true"', 'class="katex-html"'), /aria-hidden/],
    ['namespace switching', s => s.replace('xmlns="http://www.w3.org/1999/xhtml"', 'xmlns="http://www.w3.org/2000/svg"'), /XHTML/],
    ['MathML namespace confusion', s => s.replace('xmlns="http://www.w3.org/1998/Math/MathML"', 'xmlns="http://www.w3.org/1999/xhtml"'), /MathML root/],
    ['active MathML annotation', s => s.replace('<annotation ', '<annotation-xml ').replace('</annotation>', '</annotation-xml>'), /annotation|approved MathML/],
    ['event handler', s => s.replace('<math ', '<math onload="go()" '), /event handler/],
    ['external hyperlink', s => s.replace('<math ', '<math href="https://example.com/" '), /unexpected attribute|href/],
    ['embedded image', s => s.replace('</foreignObject>', '<img src="/bad.png" alt=""></foreignObject>'), /<img>|one XHTML/],
    ['nested foreignObject', s => s.replace('</foreignObject>', '<foreignObject></foreignObject></foreignObject>'), /foreignObject|foreignobject/],
    ['style attribute', s => s.replace('class="diagram-math-content"', 'class="diagram-math-content" style="position:fixed"'), /style attribute/],
    ['HTML self-closing namespace ambiguity', s => s.replace('<span data-math-baseline="" class="diagram-math-baseline"></span>', '<span data-math-baseline="" class="diagram-math-baseline"/>'), /explicit end tags/],
    ['unsupported HTML element', s => s.replace('class="katex-html" aria-hidden="true">', 'class="katex-html" aria-hidden="true"><object></object>'), /approved KaTeX|<object>/],
    ['unsafe namespace in visual span', s => s.replace('class="katex-html" aria-hidden="true">', 'class="katex-html" aria-hidden="true"><span xmlns="http://www.w3.org/2000/svg">x</span>'), /unexpected attribute/],
    ['invalid measured viewport', s => s.replace('width="1000" height="100" overflow', 'width="0" height="100" overflow'), /invalid width/],
    ['site directive in annotation', s => s.replace('</annotation>', '{{view:other}}</annotation>'), /directive syntax|reserves/],
    ['site directive in measurement key', s => s.replace('data-math-label="', 'data-math-label="{{view:other}}'), /measurement key|reserves/],
    ['nested braces outside math', s => s.replace('</svg>', '</svg><span>}}</span>'), /reserves/],
    ['private metadata still prohibited', s => s.replace('data-diagram-label="fixture-label"', 'data-diagram-label="/private/tmp/secret"'), /private system path|temporary/],
  ];
  for (const [name, change, reason] of mutations) test(`reject ${name}`, () => { const changed = change(fragment); assert.notEqual(changed, fragment); rejected(changed, reason); });
  test('complete package and canonical CSS verified', () => assert.equal(verifyMathAssets(MATH_ASSETS, read).size, 22));
  test('legacy absence introduces no resources', () => { assert.equal(verifyMathAssets(undefined, read).size, 0); assert.equal(publishedMathCss([{}]), ''); assert.deepEqual(mathAssetOutputs([{}]), []); });
  const contractCases = [
    ['different version', c => { c.version = '0.18.6'; }],
    ['different engine', c => { c.engine = 'other'; }],
    ['missing font', c => { c.fonts.pop(); }],
    ['duplicate font', c => { c.fonts[1] = c.fonts[0]; }],
    ['extra public field', c => { c.path = '/private/input'; }],
    ['extra font field', c => { c.fonts[0].url = 'https://example.com/font'; }],
    ['path traversal', c => { c.fonts[0].file = '../font.woff2'; }],
    ['alternate format', c => { c.fonts[0].mime = 'font/ttf'; }],
    ['self-authorized font hash', c => { c.fonts[0].sha256 = 'a'.repeat(64); }],
    ['font size', c => { c.fonts[0].bytes += 1; }],
    ['missing license', c => { delete c.license; }],
    ['changed license pin', c => { c.license.sha256 = 'b'.repeat(64); }],
    ['arbitrary stylesheet pin', c => { c.stylesheet.sha256 = 'c'.repeat(64); }],
    ['extra stylesheet field', c => { c.stylesheet.private = 'note'; }],
  ];
  for (const [name, change] of contractCases) test(`reject ${name}`, () => { const contract = structuredClone(MATH_ASSETS); change(contract); assert.throws(() => validateMathAssetContract(contract)); });
  for (const entry of [MATH_ASSETS.fonts[0], MATH_ASSETS.license, MATH_ASSETS.stylesheet]) test(`reject changed bytes ${entry.file}`, () => assert.throws(() => verifyMathAssets(MATH_ASSETS, file => file === entry.file ? Buffer.from('changed') : read(file)), /approved bytes/));
  for (const bad of ['@font-face{font-family:x;src:url("/bad.woff2")}', '.dg-view{background:url("https://example.com/x")}', '@import "/x.css";']) test('ordinary CSS keeps resource ban', () => assert.ok(validateViewCss(bad).errors.length));
  test('published font block has only generated same-origin paths and deduplicates', () => {
    const batch = { mathAssets: MATH_ASSETS, mathFiles: verifyMathAssets(MATH_ASSETS, read) };
    assert.equal(publishedMathFiles([batch, batch]).length, 21);
    const generated = publishedMathCss([batch, batch]);
    assert.equal((generated.match(/@font-face/g) ?? []).length, 20);
    assert.ok(generated.includes('url("/assets/math/katex-0.18.7/KaTeX_Main-Regular.woff2")'));
    assert.deepEqual(validatePublishedMathCss(generated + '.dg-view{color:black}', [batch]), []);
    assert.ok(validatePublishedMathCss(generated + generated, [batch]).length);
    assert.ok(validatePublishedMathCss(generated + '.x{background:url("/unapproved")}', [batch]).length);
    assert.ok(validatePublishedMathCss(generated.replace('font-display:block', 'font-display:swap'), [batch]).length);
    assert.throws(() => publishedMathFiles([batch, { ...batch, mathFiles: new Map() }]), /conflicting/);
  });
  const scratch = mkdtempSync(path.join(os.tmpdir(), 'dg-math-test-'));
  try {
    test('symlink input rejected', () => {
      const relative = MATH_ASSETS.fonts[0].file;
      mkdirSync(path.join(scratch, 'links/assets/fonts'), { recursive: true });
      symlinkSync(path.join(fixture, relative), path.join(scratch, 'links', relative));
      assert.throws(() => readMathAsset(path.join(scratch, 'links'), relative), /symlink/);
    });
    test('import and public load verify all assets; byte drift fails after import', () => {
      const batchDir = path.join(scratch, 'batch');
      const site = path.join(scratch, 'site');
      cpSync(fixture, batchDir, { recursive: true });
      mkdirSync(path.join(batchDir, 'fixture-math'));
      const fragmentBytes = Buffer.from(fragment);
      const source = readFileSync(path.join(fixture, 'epsilon.lean'));
      writeFileSync(path.join(batchDir, 'fixture-math/fragment.html'), fragmentBytes);
      writeFileSync(path.join(batchDir, 'fixture-math/source.lean'), source);
      const css = readFileSync(path.join(fixture, 'epsilon.css'));
      writeFileSync(path.join(batchDir, 'views.css'), css);
      const manifest = { batch:'fixture-math', createdAt:'2026-10-02T12:00:00Z', lean:'4.28.0', product:{commit:'0'.repeat(40)}, mathAssets:MATH_ASSETS, css:{file:'views.css',sha256:hash(css)}, views:[{id:'fixture-math',kind:'fixture',title:'Math validator fixture',minWidthPx:1000,files:{fragment:'fixture-math/fragment.html',source:'fixture-math/source.lean'},sha256:{fragment:hash(fragmentBytes),source:hash(source)}}] };
      const manifestBytes = Buffer.from(JSON.stringify(manifest));
      writeFileSync(path.join(batchDir, 'manifest.json'), manifestBytes);
      // A throwaway declaration solely for this synthetic import fixture.
      writeFileSync(path.join(scratch, 'READY-math-fixture.json'), JSON.stringify({status:'ready',createdAt:manifest.createdAt,manifest:'batch/manifest.json',manifestSha256:hash(manifestBytes)}));
      mkdirSync(path.dirname(path.join(site,VIEWS_MANIFEST)), {recursive:true});
      writeFileSync(path.join(site,VIEWS_MANIFEST), JSON.stringify({version:2,batches:[]}));
      const result = importBatch(batchDir, site);
      assert.ok(result.written.some(file => file.endsWith('math-fonts.css')));
      const loaded = loadViews(site);
      assert.deepEqual(loaded.errors, []);
      assert.deepEqual(loaded.batches[0].mathAssets, MATH_ASSETS);
      assert.equal(loaded.batches[0].mathFiles.size, 22);
      assert.equal(publishedMathFiles(loaded.batches).length, 21);
      const publicManifest = JSON.parse(readFileSync(path.join(site,VIEWS_MANIFEST)));
      assert.equal(publicManifest.batches[0].product, undefined);
      writeFileSync(path.join(site,loaded.batches[0].dir,MATH_ASSETS.fonts[0].file), 'corrupt');
      assert.ok(loadViews(site).errors.some(error => /approved bytes/.test(error)));
    });
  } finally { rmSync(scratch, {recursive:true,force:true}); }
  return { failures, cases };
}
if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const result = runMathSelfTest(path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..'));
  result.failures.forEach(failure => console.error(failure));
  console.log(`${result.cases} static math checks; ${result.failures.length} failures.`);
  process.exitCode = result.failures.length ? 1 : 0;
}
