// Focused metadata tests using the existing hand-written fixture, never product captures.
// Temporary hand-written fixture files are removed after testing; no product capture or readiness declaration is produced.
import assert from 'node:assert/strict';
import { createHash } from 'node:crypto';
import { cpSync, mkdirSync, mkdtempSync, readFileSync, rmSync, symlinkSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { importBatch, importedViewProvenance } from './import-views.mjs';
import { keyframePlan, loadViews, provenanceLine, renderCaptureFigure, renderViewFigure, validateBatchProvenance, validateFragment, validateNativeCapture, VIEWS_MANIFEST } from './views.mjs';

export function runProvenanceSelfTest(root) {
  const failures = [];
  let cases = 0;
  const test = (name, run) => {
    cases += 1;
    try { run(); } catch (error) { failures.push(`${name}: ${error.message}`); }
  };
  const batch = { createdAt: '2026-10-02T12:00:00Z', renderedFromSavedData: true, recordedTheme: 'light' };
  const capture = { startedAt: '2026-09-28T08:00:00Z', completedAt: '2026-09-28T08:00:00Z' };
  const validate = (value, owner = batch) => validateNativeCapture(value, owner).join('\n');
  test('valid capture, unknown capture and legacy absence', () => {
    assert.equal(validate(capture), '');
    assert.equal(validate(null), '');
    assert.equal(validate(undefined, {}), '');
    assert.deepEqual(validateBatchProvenance(batch), []);
  });
  for (const [name, value] of [['missing', undefined], ['array', []], ['empty object', {}], ['string', '/private/native.json'], ['extra private field', { ...capture, path: '/private/native.json' }], ['extra hash field', { ...capture, sha256: 'a'.repeat(64) }]]) {
    test(`reject ${name} native capture`, () => assert.notEqual(validate(value), ''));
  }
  for (const stamp of ['2026-02-29T08:00:00Z', '2026-04-31T08:00:00Z', '2026-13-01T08:00:00Z', '2026-09-28T24:00:00Z', '2026-09-28T08:60:00Z', '2026-09-28T08:00:60Z', '2026-09-28T08:00:00+24:00', '2026-09-28', 'not-a-date']) {
    test(`reject invalid calendar timestamp ${stamp}`, () => assert.match(validate({ ...capture, startedAt: stamp }), /valid ISO/));
  }
  test('accept leap day and minute precision', () => assert.equal(validate({ startedAt: '2024-02-29T08:00Z', completedAt: '2024-02-29T08:00Z' }), ''));
  test('reject reversed range', () => assert.match(validate({ startedAt: '2026-09-29T08:00:00Z', completedAt: capture.completedAt }), /not be later/));
  test('reject capture after rendering, including submillisecond fraction', () => {
    assert.match(validate({ startedAt: batch.createdAt, completedAt: '2026-10-02T12:00:00.0001Z' }), /later than the rendering/);
    assert.match(validate({ startedAt: '2026-09-28T08:00:00.0002Z', completedAt: '2026-09-28T08:00:00.0001Z' }), /startedAt must not/);
  });
  test('compare offset instants rather than written local clocks', () => assert.equal(validate({ startedAt: '2026-09-29T00:00:00+02:00', completedAt: '2026-09-28T23:00:00Z' }), ''));
  for (const [name, mutation] of [
    ['false saved marker', { renderedFromSavedData: false }],
    ['string saved marker', { renderedFromSavedData: 'true' }],
    ['missing theme', { recordedTheme: undefined }],
    ['invalid theme', { recordedTheme: 'system' }],
    ['false adaptive marker', { adaptiveTheme: false }],
    ['string adaptive marker', { adaptiveTheme: 'true' }],
    ['invalid rendering date', { createdAt: '2026-02-30T00:00:00Z' }],
  ]) test(`reject ${name}`, () => assert.ok(validateBatchProvenance({ ...batch, ...mutation }).length));
  test('adaptive theme requires a recorded theme even without a saved-data marker', () => assert.match(validateBatchProvenance({ adaptiveTheme: true }).join('\n'), /requires recordedTheme/));
  test('reject native range without explicit saved-data marker', () => assert.match(validate(null, {}), /requires renderedFromSavedData/));
  test('extract only approved public provenance from pipeline metadata', () => {
    const result = importedViewProvenance(batch, { private: { path: '/private/native.json' }, recordedState: { nativeCapture: capture, savedRecord: false, privateInputHash: 'not-public' } });
    assert.deepEqual(result, { nativeCapture: capture });
    assert.deepEqual(importedViewProvenance(batch, { recordedState: { nativeCapture: null, savedRecord: true } }), { savedRecord: true, nativeCapture: null });
    assert.deepEqual(importedViewProvenance({ createdAt: '2026-09-28T00:00:00Z' }, {}), {});
  });
  test('missing date is not inferred from batch export date', () => assert.throws(() => importedViewProvenance(batch, { recordedState: {} }), /nativeCapture must/));
  test('unsafe capture fields are rejected before copying', () => assert.throws(() => importedViewProvenance(batch, { recordedState: { nativeCapture: { ...capture, privateHash: 'not-public' } } }), /unexpected nativeCapture field/));
  test('malformed history flag cannot silently become ordinary results', () => assert.throws(() => importedViewProvenance(batch, { recordedState: { nativeCapture: null, savedRecord: 'true' } }), /must be a boolean/));

  const legacy = '<p class="dg-provenance"><a class="dg-recorded" href="/reference/#recorded-views">Recorded Definograph output</a> · Lean 4.28.0 · <time datetime="2026-09-28">28 September 2026</time></p>';
  test('legacy provenance is byte-for-byte unchanged', () => {
    assert.equal(provenanceLine('Recorded Definograph output', '2026-09-28', '4.28.0'), legacy);
    assert.equal(provenanceLine('Recorded Definograph output', '2026-09-28', '4.28.0', { savedRecord: true }), legacy.replace(' · Lean', ' · from a saved history · Lean'));
  });
  test('unknown date and saved-input wording', () => {
    const label = provenanceLine('Recorded Definograph output', '2026-10-02', '4.28.0', { renderedFromSavedData: true, nativeCapture: null });
    for (const text of ['Rendered <time', 'from saved results', 'Native capture date unavailable', 'Saved input: Lean 4.28.0', 'Lean was not rerun.']) assert.ok(label.includes(text), text);
    assert.ok(!label.includes('from a saved history'));
  });
  test('native range is distinct from rendering date and normalized to UTC', () => {
    const label = provenanceLine('Recorded Definograph excerpt', '2026-10-02', '4.28.0', { renderedFromSavedData: true, savedRecord: true, nativeCapture: { startedAt: '2026-09-28T00:00:00+02:00', completedAt: '2026-09-28T08:00:00Z' } });
    assert.ok(label.includes('from a saved history'));
    assert.ok(label.includes('>27 September 2026</time>–<time'));
    assert.ok(label.includes('>28 September 2026</time>'));
    assert.ok(label.includes('Dates in UTC'));
  });

  const fixture = path.join(root, 'scripts/fixtures/views/fixture-1');
  const nativeManifest = JSON.parse(readFileSync(path.join(fixture, 'manifest.json'), 'utf8'));
  const nativeView = nativeManifest.views[0];
  const fragment = readFileSync(path.join(fixture, nativeView.files.fragment), 'utf8');
  const css = readFileSync(path.join(fixture, 'views.css'), 'utf8');
  const classes = validateFragment(fragment, { id: nativeView.id, kind: nativeView.kind }).classes;
  const publicBatch = {
    batch: nativeManifest.batch, createdAt: nativeManifest.createdAt, lean: nativeManifest.lean,
    stylesheet: { path: 'views.css', sha256: nativeManifest.css.sha256 },
    keyframes: keyframePlan(css, nativeManifest.batch, [classes]),
    views: [{ id: nativeView.id, kind: nativeView.kind, title: nativeView.title, label: 'Hand-written fixture', caption: 'Hand-written test fixture, not reader output.', fragment: { path: nativeView.files.fragment, sha256: nativeView.sha256.fragment }, source: { path: nativeView.files.source, sha256: nativeView.sha256.source, form: 'term' } }],
  };
  const scratch = mkdtempSync(path.join(root, '.provenance-selftest-'));
  try {
    const parent = path.join(scratch, 'source-assets/views');
    mkdirSync(parent, { recursive: true });
    symlinkSync(fixture, path.join(parent, 'fixture-1'), 'dir');
    const load = (record) => {
      writeFileSync(path.join(scratch, VIEWS_MANIFEST), JSON.stringify({ version: 2, batches: [record] }));
      return loadViews(scratch);
    };
    const replay = { ...structuredClone(publicBatch), ...batch };
    replay.views[0].nativeCapture = null;
    test('legacy loader and canvas remain unchanged', () => {
      const loaded = load(publicBatch);
      assert.deepEqual(loaded.errors, []);
      const view = loaded.views.get('fixture-card');
      assert.ok(renderViewFigure(view).includes(fragment.trimEnd()));
      assert.ok(!renderViewFigure(view).includes('data-dg-theme'));
      assert.ok(renderViewFigure(view).includes('27 September 2026'));
    });
    test('saved-result loader carries theme, native data and exact source', () => {
      const loaded = load(replay);
      assert.deepEqual(loaded.errors, []);
      const view = loaded.views.get('fixture-card');
      assert.equal(view.batch.recordedTheme, 'light');
      assert.equal(view.nativeCapture, null);
      assert.equal(view.sourceText, readFileSync(path.join(fixture, nativeView.files.source), 'utf8'));
      assert.ok(renderViewFigure(view).includes('data-dg-theme="light"'));
      const captureView = { ...view, context: { width: 640, height: 480, alt: 'Test fixture', caption: 'Test only.' }, contextOutput: 'fixture.png' };
      const screenshot = renderCaptureFigure(captureView);
      assert.ok(screenshot.includes('Recorded Definograph screenshot'));
      assert.ok(screenshot.includes('from saved results'));
      assert.ok(screenshot.includes('Lean was not rerun.'));
    });
    test('adaptive HTML keeps same-batch screenshots fixed and saved-data provenance explicit', () => {
      const loaded = load({ ...replay, adaptiveTheme: true });
      assert.deepEqual(loaded.errors, []);
      const view = loaded.views.get('fixture-card');
      assert.equal(view.batch.adaptiveTheme, true);
      const html = renderViewFigure(view);
      assert.ok(html.includes('data-dg-theme="adaptive"'));
      assert.ok(html.includes('Adapts to page theme'));
      assert.ok(html.includes('Lean was not rerun.'));
      assert.ok(!html.includes('Light theme'));
      const screenshot = renderCaptureFigure({ ...view, context: { width: 640, height: 480, alt: 'Test fixture', caption: 'Test only.' }, contextOutput: 'fixture.png' });
      assert.ok(screenshot.includes('Light theme'));
      assert.ok(screenshot.includes('Lean was not rerun.'));
      assert.ok(!screenshot.includes('Adapts to page theme'));
      assert.ok(!screenshot.includes('data-dg-theme'));
    });
    test('fixed saved-data HTML and screenshots name their recorded dark theme', () => {
      const loaded = load({ ...replay, recordedTheme: 'dark' });
      assert.deepEqual(loaded.errors, []);
      const view = loaded.views.get('fixture-card');
      const html = renderViewFigure(view);
      assert.ok(html.includes('data-dg-theme="dark"'));
      assert.ok(html.includes('Dark theme'));
      const screenshot = renderCaptureFigure({ ...view, context: { width: 640, height: 480, alt: 'Test fixture', caption: 'Test only.' }, contextOutput: 'fixture.png' });
      assert.ok(screenshot.includes('Dark theme'));
      assert.ok(!screenshot.includes('Adapts to page theme'));
    });
    test('an adaptive marker alone makes no fresh native-run or saved-result claim', () => {
      const loaded = load({ ...publicBatch, recordedTheme: 'light', adaptiveTheme: true });
      assert.deepEqual(loaded.errors, []);
      const html = renderViewFigure(loaded.views.get('fixture-card'));
      assert.ok(html.includes('data-dg-theme="adaptive"'));
      assert.ok(!html.includes('Rendered <time'));
      assert.ok(!html.includes('from saved results'));
      assert.ok(!html.includes('Native capture'));
      assert.ok(!html.includes('Lean was not rerun.'));
    });
    test('explicit legacy theme adds only the canvas marker', () => {
      const loaded = load({ ...publicBatch, recordedTheme: 'dark' });
      assert.deepEqual(loaded.errors, []);
      const figure = renderViewFigure(loaded.views.get('fixture-card'));
      assert.ok(figure.includes('data-dg-theme="dark"'));
      assert.ok(!figure.includes('Rendered <time'));
    });
    // Exercise actual import decisions with unchanged fixture fragment and PNG bytes.
    // This one-pixel image is test data, not a screenshot or claimed product output.
    const pixel = Buffer.from('iVBORw0KGgoAAAANSUhEUgAAAAEAAAABCAQAAAC1HAwCAAAAC0lEQVR42mP8/x8AAwMCAO+aX1sAAAAASUVORK5CYII=', 'base64');
    const digest = (bytes) => createHash('sha256').update(bytes).digest('hex');
    const importFixture = path.join(scratch, 'fixture-input', 'fixture-1');
    cpSync(fixture, importFixture, { recursive: true });
    const importManifest = { ...structuredClone(nativeManifest), ...batch };
    const importView = importManifest.views[0];
    const meta = JSON.parse(readFileSync(path.join(importFixture, importView.files.meta), 'utf8'));
    meta.recordedState = { nativeCapture: null };
    const metaBytes = Buffer.from(JSON.stringify(meta));
    writeFileSync(path.join(importFixture, importView.files.meta), metaBytes);
    importView.sha256.meta = digest(metaBytes);
    importView.files.context = 'fixture-card/context@2x.png';
    importView.sha256.context = digest(pixel);
    writeFileSync(path.join(importFixture, importView.files.context), pixel);
    const reviewed = structuredClone(replay);
    reviewed.views[0].context = { path: importView.files.context, sha256: digest(pixel), width: 1, height: 1, alt: 'One-pixel test fixture.', caption: 'Reviewed test capture caption.' };
    const dryImport = (changes = {}) => {
      writeFileSync(path.join(scratch, VIEWS_MANIFEST), JSON.stringify({ version: 2, batches: [reviewed] }));
      const manifestBytes = Buffer.from(JSON.stringify({ ...importManifest, ...changes }));
      writeFileSync(path.join(importFixture, 'manifest.json'), manifestBytes);
      const declaration = JSON.parse(readFileSync(path.join(root, 'scripts/fixtures/views/READY-fixture.json'), 'utf8'));
      declaration.batch.manifestSha256 = digest(manifestBytes);
      writeFileSync(path.join(scratch, 'fixture-input/READY-fixture.json'), JSON.stringify(declaration));
      const imported = importBatch(importFixture, scratch, { dryRun: true });
      assert.equal(imported.batch.adaptiveTheme, changes.adaptiveTheme);
      assert.equal(imported.batch.recordedTheme, changes.recordedTheme ?? 'light');
      return imported.batch.views[0];
    };
    test('identical theme and provenance retain reviewed fragment and capture text', () => {
      const imported = dryImport();
      assert.equal(imported.captionDraft, undefined);
      assert.equal(imported.context.textDraft, undefined);
      assert.equal(imported.caption, reviewed.views[0].caption);
      assert.equal(imported.context.caption, reviewed.views[0].context.caption);
    });
    test('rendering date alone retains reviewed fragment and capture text', () => {
      const imported = dryImport({ createdAt: '2026-10-03T12:00:00Z' });
      assert.equal(imported.captionDraft, undefined);
      assert.equal(imported.context.textDraft, undefined);
    });
    test('changed theme requires review even with identical fragment and capture bytes', () => {
      const imported = dryImport({ recordedTheme: 'dark' });
      assert.equal(imported.fragment.sha256, reviewed.views[0].fragment.sha256);
      assert.equal(imported.context.sha256, reviewed.views[0].context.sha256);
      assert.equal(imported.captionDraft, true);
      assert.equal(imported.context.textDraft, true);
      assert.equal(imported.caption, reviewed.views[0].caption);
      assert.equal(imported.context.alt, reviewed.views[0].context.alt);
      assert.equal(imported.context.caption, reviewed.views[0].context.caption);
    });
    test('changed adaptive behavior requires review of unchanged fragment and capture text', () => {
      const imported = dryImport({ adaptiveTheme: true });
      assert.equal(imported.fragment.sha256, reviewed.views[0].fragment.sha256);
      assert.equal(imported.context.sha256, reviewed.views[0].context.sha256);
      assert.equal(imported.captionDraft, true);
      assert.equal(imported.context.textDraft, true);
    });
    for (const [name, mutate, reason] of [
      ['missing native metadata', (b) => { delete b.views[0].nativeCapture; }, /nativeCapture must/],
      ['unsafe view field', (b) => { b.views[0].privatePath = '/private/input.json'; }, /unexpected public saved-data view field/],
      ['unsafe batch field', (b) => { b.privateHash = 'not-public'; }, /unexpected public batch field/],
      ['unsafe nested capture field', (b) => { b.views[0].nativeCapture = { ...capture, sha256: 'not-public' }; }, /unexpected nativeCapture field/],
      ['invalid adaptive marker', (b) => { b.adaptiveTheme = false; }, /adaptiveTheme is either true or absent/],
      ['missing adaptive theme', (b) => { b.adaptiveTheme = true; delete b.recordedTheme; }, /adaptiveTheme requires recordedTheme/],
      ['missing actual theme', (b) => { delete b.recordedTheme; }, /requires recordedTheme/],
    ]) test(`loader rejects ${name}`, () => {
      const broken = structuredClone(replay);
      mutate(broken);
      assert.ok(load(broken).errors.some((error) => reason.test(error)));
    });
  } finally {
    rmSync(scratch, { recursive: true, force: true });
  }
  return { failures, cases };
}

if (process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href) {
  const { failures, cases } = runProvenanceSelfTest(path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..'));
  failures.forEach((failure) => console.error(failure));
  console.log(`${cases} saved-data provenance checks; ${failures.length} failure(s).`);
  process.exitCode = failures.length ? 1 : 0;
}
