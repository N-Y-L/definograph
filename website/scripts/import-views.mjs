// Imports a recorded-view batch produced by the views pipeline into source-assets/views/.
//
//   node scripts/import-views.mjs <batch directory> [--replaces <batch>] [--replaces-view <id>] [--dry-run]
//
// --replaces removes an earlier batch from the allowlist and from source-assets/views (git
// history keeps it); the new batch may reuse its view ids.
// --replaces-view takes one screenshot (a view with no recorded fragment) from the earlier batch
// that holds it, so that a new batch can bring a retaken screenshot without replacing the rest
// of that batch; the earlier batch keeps its other views (or leaves the allowlist if it has none).
// The batch directory holds manifest.json, views.css and one directory per view with
// fragment.html, source.lean, meta.json and optionally context@2x.png. The import:
// - accepts the batch only when a READY-*.json beside it declares its manifest.json with the
//   same SHA-256 (readyDeclaration below), so a draft cannot be pinned;
// - verifies every file against the SHA-256 in the batch manifest and refuses on a mismatch;
// - validates the fragments and stylesheet with the same rules as the build;
// - copies only the publishable files (never meta.json) into source-assets/views/<batch>/,
//   replacing that directory;
// - decides what publishing does with the stylesheet's @keyframes (keyframePlan in views.mjs:
//   rename to dg-<batch>-<name> when a rule that could apply to one of the batch's fragments
//   uses it, drop otherwise) and records that plan as the batch's "keyframes";
// - writes the batch into source-assets/views/views.json with pinned hashes. Fields the
//   site writes (label, caption, source form, capture text) are kept from an earlier import
//   of the same view; a new view gets a draft caption from the public part of its meta.json,
//   marked captionDraft, which the build refuses to publish until someone reviews it. Text
//   kept for a changed recording or screenshot is marked the same way (captionDraft, or
//   textDraft on the screenshot), so it is reviewed against the new image before it is used.
// - records two facts the batch states in a view's public metadata: savedRecord, when the
//   recording was drawn from a saved record (recordedState.savedRecord), which the figure's
//   provenance line reports as "from a saved history"; and excerpt, when it shows only part of
//   a panel (excerpt.isExcerpt, or excerpt: true in the manifest), which the figure discloses
//   and whose reviewed caption begins with "Excerpt" or "Part of".
// Private metadata (the "private" object of meta.json) is never read into the site.
import { createHash } from 'node:crypto';
import { existsSync, mkdirSync, readdirSync, readFileSync, realpathSync, rmSync, statSync, writeFileSync } from 'node:fs';
import path from 'node:path';
import { fileURLToPath, pathToFileURL } from 'node:url';
import { escapeHtml } from './format.mjs';
import { readMathAsset, verifyMathAssets } from './math-assets.mjs';
import { stripCssComments, keyframePlan, validateBatchProvenance, validateNativeCapture, validateFragment, validateViewCss, VIEWS_DIR, VIEWS_MANIFEST } from './views.mjs';

const NAME = /^[a-z0-9][a-z0-9-]{0,63}$/;
const sha256 = (data) => createHash('sha256').update(data).digest('hex');

// Copy only the public provenance contract. Native dates never come from an older export's
// createdAt, and saved native results are not automatically an editor inspection history.
export function importedViewProvenance(manifest, meta, label = 'view') {
  const state = meta.recordedState;
  const errors = [...validateBatchProvenance(manifest, 'manifest.json'), ...validateNativeCapture(state?.nativeCapture, manifest, label)];
  if (manifest.renderedFromSavedData === true && state?.savedRecord !== undefined && typeof state.savedRecord !== 'boolean') errors.push(`${label}: recordedState.savedRecord must be a boolean when supplied`);
  if (errors.length) throw new Error(errors.join('\n'));
  const provenance = state?.savedRecord === true ? { savedRecord: true } : {};
  if (manifest.renderedFromSavedData === true) provenance.nativeCapture = state.nativeCapture === null ? null : {
    startedAt: state.nativeCapture.startedAt, completedAt: state.nativeCapture.completedAt,
  };
  return provenance;
}

// Statement terms are what the Lean expression field of the reader's Lean source panel accepts;
// a file has commands.
function sourceForm(text) {
  return /^\s*(?:example|theorem|lemma|def|abbrev|structure|class|instance|inductive|namespace|section|open|import|variable|#check|#print|#eval)\b/m.test(text) ? 'file' : 'term';
}

// A view's minimum width, so its diagram scrolls inside its frame instead of shrinking its
// labels. The width applies to the view root (the reader's own figures can clip an SVG that is
// wider than they are). In order: a width the site recorded itself (from "site: …"), which
// stays across recordings because the batch cannot see what the static page needs (a
// recording freezes a scroll box that the live reader makes scrollable when it overflows);
// none when the batch manifest says the view reflows; the batch manifest's minWidthPx; a width
// recorded by an earlier import of the same recording, or by measurement. A view with an SVG
// and none of these is reported, so someone measures it.
export function sizing(view, fragmentText, before, { siteWidth = null, honorMeasuredMinimum = false } = {}) {
  const layout = { ...view, ...(view.layout ?? {}) };
  // A measured mathematical figure may reflow above a finite safe minimum.
  // Reflow alone must not discard the font/geometry floor established by capture.
  if (honorMeasuredMinimum) {
    if (!Number.isInteger(layout.minWidthPx) || layout.minWidthPx <= 0) throw new Error('Measured math figure requires a positive integer minWidthPx');
    if (typeof siteWidth?.from === 'string' && siteWidth.from.startsWith('site:') && siteWidth.minWidthPx >= layout.minWidthPx) return { size: siteWidth, kept: true };
    return { size: { minWidthPx: layout.minWidthPx, target: 'root', from: 'batch manifest minWidthPx' } };
  }
  if (typeof siteWidth?.from === 'string' && siteWidth.from.startsWith('site:')) return { size: siteWidth, kept: true };
  if (layout.reflows === true) return { size: null };
  if (Number.isInteger(layout.minWidthPx) && layout.minWidthPx > 0) return { size: { minWidthPx: layout.minWidthPx, target: 'root', from: 'batch manifest minWidthPx' } };
  if (before?.sizing) return { size: before.sizing };
  return { size: null, unmeasured: /<svg\b/.test(fragmentText) };
}

function draftCaption(meta, title) {
  const shows = Array.isArray(meta.showsFacts) ? meta.showsFacts.filter((fact) => typeof fact === 'string') : [];
  const omits = Array.isArray(meta.omits) ? meta.omits.filter((fact) => typeof fact === 'string') : [];
  const parts = [`${title}.`];
  if (shows.length) parts.push(`Shows: ${shows.join('; ')}.`);
  if (omits.length) parts.push(`Leaves out: ${omits.join('; ')}.`);
  return escapeHtml(parts.join(' '));
}

// A pipeline keeps its batches in <pipeline>/public-candidates/<batch> and, once a batch is
// finished, declares it in a READY-*.json file in <pipeline>. A declaration is any object in
// such a file with the batch's manifest path as "manifest" and its SHA-256 as "manifestSha256"
// (the views pipeline writes it as "batch" or "partA", the editor-views pipeline as
// "batches.<name>"); a relative path is read from the READY file's directory. Declarations are
// matched to this batch by that path. The READY files looked at are those in the batch
// directory's parent and grandparent. The most recent READY file that declares this manifest
// (its "createdAt" or "completedAt", else its modification time) decides: its "status" must be
// "ready" or "complete" and its SHA-256 must be the manifest's. Returns { file, at, path } of
// that READY file; throws otherwise.
const READY_FILE = /^READY-[\w.-]+\.json$/;
const READY_STATUS = new Set(['ready', 'complete']);

function realOrResolved(file) {
  try {
    return realpathSync(file);
  } catch {
    return path.resolve(file);
  }
}

function declarationsIn(value, found = []) {
  if (Array.isArray(value)) value.forEach((item) => declarationsIn(item, found));
  else if (value && typeof value === 'object') {
    if (typeof value.manifest === 'string' && typeof value.manifestSha256 === 'string') found.push(value);
    Object.values(value).forEach((item) => declarationsIn(item, found));
  }
  return found;
}

export function readyDeclaration(batchDir, manifestSha) {
  const manifestFile = path.join(path.resolve(batchDir), 'manifest.json');
  const target = realOrResolved(manifestFile);
  const dirs = [...new Set([path.dirname(path.resolve(batchDir)), path.dirname(path.dirname(path.resolve(batchDir)))])];
  const found = [];
  for (const dir of dirs) {
    const names = existsSync(dir) ? readdirSync(dir).filter((name) => READY_FILE.test(name)).sort() : [];
    for (const name of names) {
      const file = path.join(dir, name);
      let ready;
      try {
        ready = JSON.parse(readFileSync(file, 'utf8'));
      } catch (error) {
        throw new Error(`${file} cannot be read (${error.message}); the import will not guess whether it declares this batch`);
      }
      const stated = typeof ready.createdAt === 'string' ? ready.createdAt : ready.completedAt;
      const time = Number.isNaN(Date.parse(stated)) ? statSync(file).mtimeMs : Date.parse(stated);
      for (const declaration of declarationsIn(ready)) {
        if (realOrResolved(path.resolve(dir, declaration.manifest)) !== target) continue;
        found.push({ file, name, status: ready.status, at: typeof stated === 'string' ? stated : new Date(time).toISOString(), time, sha256: declaration.manifestSha256 });
      }
    }
  }
  if (!found.length) throw new Error(`no READY-*.json in ${dirs.join(' or ')} declares ${manifestFile}; the import accepts only a batch its pipeline has declared finished`);
  found.sort((a, b) => b.time - a.time);
  const [latest] = found;
  const rival = found.find((other) => other.time === latest.time && other.sha256 !== latest.sha256);
  if (rival) throw new Error(`${latest.name} and ${rival.name} declare different manifests for this batch with the same time; which one is final?`);
  if (!READY_STATUS.has(latest.status)) throw new Error(`${latest.file} declares this batch but its status is ${JSON.stringify(latest.status)}, not "ready" or "complete"`);
  if (latest.sha256 !== manifestSha) throw new Error(`${latest.file} (${latest.at}) declares this batch's manifest with SHA-256 ${latest.sha256}, but ${manifestFile} has ${manifestSha}: a draft, or a batch changed after it was declared. Import the declared batch.`);
  return { file: latest.name, at: latest.at, path: latest.file };
}

// Returns { batch, written, notes, drafts, ready }. Throws when the batch cannot be imported.
export function importBatch(batchDir, siteRoot, { dryRun = false, replaces = [], replacesViews = [] } = {}) {
  const problems = [];
  const readBatch = (rel) => readFileSync(path.join(batchDir, rel));
  const manifestBytes = readBatch('manifest.json');
  const manifestSha = sha256(manifestBytes);
  // Refused first, before anything is read into the site: a batch no READY file declares.
  const ready = readyDeclaration(batchDir, manifestSha);
  const manifest = JSON.parse(manifestBytes.toString('utf8'));
  const name = manifest.batch;
  if (!NAME.test(name ?? '')) throw new Error(`manifest.json: batch name ${JSON.stringify(name)} is not lowercase letters, digits and hyphens`);
  // The stylesheet is pinned either as css: { file, sha256 } or as files: { "views.css": sha256 }.
  const cssPin = manifest.css ?? (manifest.files?.['views.css'] ? { file: 'views.css', sha256: manifest.files['views.css'] } : {});
  for (const [field, ok] of [
    ['createdAt', typeof manifest.createdAt === 'string'],
    ['lean', typeof manifest.lean === 'string'],
    ['product.commit', /^[0-9a-f]{40}$/.test(manifest.product?.commit ?? '')],
    ['the views.css pin', cssPin.file === 'views.css' && /^[0-9a-f]{64}$/.test(cssPin.sha256 ?? '')],
    ['views', Array.isArray(manifest.views) && manifest.views.length > 0],
  ]) if (!ok) problems.push(`manifest.json: ${field} is missing or malformed`);
  problems.push(...validateBatchProvenance(manifest, 'manifest.json'));
  if (problems.length) throw new Error(problems.join('\n'));

  const verified = (rel, expected, label) => {
    if (!/^[\w@.-]+(?:\/[\w@.-]+)?$/.test(rel ?? '') || rel.includes('..')) {
      problems.push(`${label}: unexpected path ${JSON.stringify(rel)}`);
      return null;
    }
    if (!existsSync(path.join(batchDir, rel))) {
      problems.push(`${label}: ${rel} is missing`);
      return null;
    }
    const bytes = readBatch(rel);
    if (sha256(bytes) !== expected) problems.push(`${label}: ${rel} does not match the batch manifest's SHA-256`);
    return bytes;
  };

  const css = verified('views.css', cssPin.sha256, 'stylesheet');
  const publicIds = [manifest.product.commit, manifest.product.tree];
  if (css) problems.push(...validateViewCss(css.toString('utf8'), `${name}/views.css`, { allow: publicIds }).errors);

  const manifestPath = path.join(siteRoot, VIEWS_MANIFEST);
  const allowlist = existsSync(manifestPath) ? JSON.parse(readFileSync(manifestPath, 'utf8')) : { version: 1, batches: [] };
  if (![1, 2].includes(allowlist.version)) throw new Error('Unsupported recorded-view manifest version');
  for (const old of replaces) if (!allowlist.batches.some((batch) => batch.batch === old)) problems.push(`--replaces ${old}: no such batch in the allowlist`);
  const earlier = new Map(allowlist.batches.flatMap((batch) => (batch.views ?? []).map((view) => [view.id, { ...view, fromBatch: batch.batch, fromSavedData: batch.renderedFromSavedData === true, fromRecordedTheme: batch.recordedTheme, fromAdaptiveTheme: batch.adaptiveTheme === true, fromMathAssets: batch.mathAssets }])));
  // Screenshots taken from the batches that hold them (--replaces-view). A recorded view is
  // replaced only with its whole batch: that batch's @keyframes plan depends on its fragments.
  const taken = new Map();
  for (const id of replacesViews) {
    const holder = allowlist.batches.find((batch) => batch.batch !== name && !replaces.includes(batch.batch) && (batch.views ?? []).some((view) => view.id === id));
    if (!holder) problems.push(`--replaces-view ${id}: no other batch in the allowlist has this id`);
    else if (holder.views.find((view) => view.id === id).fragment !== undefined) problems.push(`--replaces-view ${id}: only a screenshot can be replaced on its own; ${id} is a recorded view, so replace its whole batch ${holder.batch}`);
    else taken.set(id, holder.batch);
  }
  const otherIds = new Set(allowlist.batches.filter((batch) => batch.batch !== name && !replaces.includes(batch.batch)).flatMap((batch) => (batch.views ?? []).map((view) => view.id)).filter((id) => !taken.has(id)));

  const files = new Map([['views.css', css]]);
  let mathAssetsVerified = false;
  if (manifest.mathAssets !== undefined) {
    try {
      for (const [file, bytes] of verifyMathAssets(manifest.mathAssets, rel => readMathAsset(batchDir, rel))) files.set(file, bytes);
      mathAssetsVerified = true;
    } catch (error) { problems.push(error.message); }
  }
  const entries = [];
  const notes = [];
  const fragmentClasses = [];
  for (const view of manifest.views) {
    const label = `view ${JSON.stringify(view.id)}`;
    if (!NAME.test(view.id ?? '') || /^view(?:-|$)/.test(view.id)) {
      problems.push(`${label}: ids are lowercase letters, digits and hyphens, and do not start with "view"`);
      continue;
    }
    if (otherIds.has(view.id)) problems.push(`${label}: another batch in the allowlist already uses this id`);
    // A capture-only entry is a screenshot of the whole application with no recorded view.
    const captureOnly = !view.files?.fragment && Boolean(view.files?.context);
    const fragment = captureOnly ? null : verified(view.files?.fragment, view.sha256?.fragment, `${label} fragment`);
    const source = captureOnly && !view.files?.source ? null : verified(view.files?.source, view.sha256?.source, `${label} source`);
    const metaBytes = view.files?.meta ? verified(view.files.meta, view.sha256?.meta, `${label} meta`) : null;
    const context = view.files?.context ? verified(view.files.context, view.sha256?.context, `${label} context`) : null;
    if (captureOnly ? !context : !fragment || !source) continue;
    const displayed = Array.isArray(view.displayedIdentifiers) ? view.displayedIdentifiers : [];
    if (view.displayedIdentifiers !== undefined && !Array.isArray(view.displayedIdentifiers)) problems.push(`${label}: displayedIdentifiers must be a list`);
    if (fragment) {
      const checked = validateFragment(fragment.toString('utf8'), { id: view.id, kind: view.kind, label: `${name}/${view.id}/fragment.html`, displayed, mathAssetsVerified });
      problems.push(...checked.errors);
      fragmentClasses.push(checked.classes);
    }
    // Only public metadata is read; the "private" object is dropped unread.
    const { private: _private, ...meta } = metaBytes ? JSON.parse(metaBytes.toString('utf8')) : {};
    let provenance;
    try {
      provenance = importedViewProvenance(manifest, meta, label);
    } catch (error) {
      problems.push(error.message);
      continue;
    }
    // Text the site wrote for an earlier recording of the same id is kept. It stays reviewed
    // only if the recording itself is unchanged; otherwise it is marked for review again.
    const before = earlier.get(view.id);
    if (manifest.renderedFromSavedData === true && before?.source && (!source || before.source.sha256 !== sha256(source))) problems.push(`${label}: a saved-data rendering must preserve the original source bytes`);
    const sameProvenance = before && before.fromSavedData === (manifest.renderedFromSavedData === true)
      && before.fromRecordedTheme === manifest.recordedTheme
      && before.fromAdaptiveTheme === (manifest.adaptiveTheme === true)
      && JSON.stringify(before.fromMathAssets) === JSON.stringify(manifest.mathAssets)
      && (before.savedRecord === true) === (provenance.savedRecord === true)
      && JSON.stringify(before.nativeCapture) === JSON.stringify(provenance.nativeCapture);
    const sameRecording = before && sameProvenance && (captureOnly ? before.context?.sha256 === sha256(context) : before.fragment?.sha256 === sha256(fragment));
    if (before && !sameRecording && !before.captionDraft) notes.push(`${view.id}: the recording differs from ${before.fromBatch}; its caption and label were carried over for review`);
    const entry = { id: view.id, kind: view.kind, title: view.title, ...provenance };
    if (!captureOnly && (meta.excerpt?.isExcerpt === true || view.excerpt === true)) entry.excerpt = true;
    if (!captureOnly) {
      entry.label = before?.label ?? `Recorded view: ${view.title}`;
      entry.caption = before?.caption ?? draftCaption(meta, view.title);
      if (!(before && !before.captionDraft && sameRecording)) entry.captionDraft = true;
      entry.fragment = { path: `${view.id}/fragment.html`, sha256: sha256(fragment) };
      if (displayed.length) entry.displayedIdentifiers = displayed;
      files.set(entry.fragment.path, fragment);
    }
    if (source) {
      entry.source = { path: `${view.id}/source.lean`, sha256: sha256(source), form: before?.source?.form ?? sourceForm(source.toString('utf8')) };
      files.set(entry.source.path, source);
    }
    if (!captureOnly) {
      const { size, unmeasured, kept } = sizing(view, fragment.toString('utf8'), sameRecording ? before : null, { siteWidth: before?.sizing, honorMeasuredMinimum: mathAssetsVerified });
      if (size) entry.sizing = size;
      if (kept && !sameRecording) notes.push(`${view.id}: keeps the width the site recorded (${size.minWidthPx} px, ${size.from}); check that the new recording still needs it`);
      if (unmeasured) notes.push(`${view.id} draws a diagram but has no minimum width; measure it and record sizing in views.json`);
    }
    if (context) {
      const width = context.readUInt32BE(16);
      const height = context.readUInt32BE(20);
      // Alt text and caption written for an earlier screenshot of the same id are kept. They
      // stay reviewed only if the image is unchanged; for a new image they are kept as text but
      // marked textDraft, and the build will not publish the screenshot until someone reviews
      // them and removes the mark. A new screenshot takes the alt text and caption its batch
      // proposes (manifest entry or public metadata, as plain text), also as a draft.
      const sameShot = sameProvenance && before?.context?.sha256 === sha256(context);
      const proposed = (...fields) => fields.flatMap((field) => [view[field], meta[field]]).find((value) => typeof value === 'string' && value.trim()) ?? '';
      const alt = before?.context ? before.context.alt ?? '' : proposed('alt', 'altText');
      const caption = before?.context ? before.context.caption ?? '' : escapeHtml(proposed('caption'));
      entry.context = {
        path: `${view.id}/context@2x.png`,
        sha256: sha256(context),
        width,
        height,
        alt,
        caption,
      };
      if ((alt || caption) && (!sameShot || before?.context?.textDraft)) entry.context.textDraft = true;
      if ((alt || caption) && before?.context && !sameShot && !before.context.textDraft) notes.push(`${view.id}: the screenshot differs from ${before.fromBatch}; its alt text and caption were carried over for review`);
      if ((alt || caption) && !before?.context) notes.push(`${view.id}: the batch proposes alt text and a caption for this new screenshot; review them`);
      files.set(entry.context.path, context);
    }
    entries.push(entry);
  }
  for (const id of taken.keys()) if (!entries.some((entry) => entry.id === id)) problems.push(`--replaces-view ${id}: this batch has no view with that id`);
  if (problems.length) throw new Error(`batch ${name} was not imported:\n  ${problems.join('\n  ')}`);

  // What publishing does with the batch's @keyframes, recorded so the build and the checks
  // apply and verify the same plan.
  const keyframes = keyframePlan(css.toString('utf8'), name, fragmentClasses);
  for (const [animation, scoped] of Object.entries(keyframes.renamed)) notes.push(`${name}/views.css: @keyframes ${animation} is published as ${scoped}, with every animation that names it`);
  for (const animation of keyframes.dropped) notes.push(`${name}/views.css: @keyframes ${animation} is dropped; no rule that could apply to a fragment of this batch uses it`);

  const record = {
    batch: name,
    manifest: { sha256: manifestSha },
    // The READY declaration the batch was accepted under (file name and its time).
    ready: { file: ready.file, at: ready.at },
    createdAt: manifest.createdAt,
    ...(manifest.renderedFromSavedData === true ? { renderedFromSavedData: true } : {}),
    ...(manifest.recordedTheme !== undefined ? { recordedTheme: manifest.recordedTheme } : {}),
    ...(manifest.adaptiveTheme === true ? { adaptiveTheme: true } : {}),
    ...(manifest.mathAssets !== undefined ? { mathAssets: manifest.mathAssets } : {}),
    lean: manifest.lean,
    product: { commit: manifest.product.commit, ...(manifest.product.tree ? { tree: manifest.product.tree } : {}) },
    stylesheet: { path: 'views.css', sha256: sha256(css) },
    keyframes,
    views: entries,
  };
  const givers = new Set(taken.values());
  const emptied = [];
  const batches = allowlist.batches
    .filter((batch) => batch.batch !== name && !replaces.includes(batch.batch))
    .map((batch) => (givers.has(batch.batch) ? { ...batch, views: batch.views.filter((view) => !taken.has(view.id)) } : batch))
    .filter((batch) => {
      if (!givers.has(batch.batch) || batch.views.length) return true;
      emptied.push(batch.batch);
      return false;
    });
  for (const [id, holder] of taken) notes.push(`${id} moves from ${holder} to ${name}${emptied.includes(holder) ? `; ${holder} has no views left and leaves the allowlist` : ''}`);
  const at = allowlist.batches.findIndex((batch) => batch.batch === name || replaces.includes(batch.batch));
  batches.splice(at === -1 ? batches.length : Math.min(at, batches.length), 0, record);
  if (allowlist.version === 2) {
    const cleaned = stripCssComments(css.toString('utf8'));
    if (cleaned.error) throw new Error(cleaned.error);
    const publicCss = Buffer.from(cleaned.text);
    const publicRecord = { ...record, stylesheet: { path: 'views.css', sha256: sha256(publicCss) } };
    delete publicRecord.product;
    delete publicRecord.manifest;
    delete publicRecord.ready;
    batches[batches.indexOf(record)] = publicRecord;
    files.set('views.css', publicCss);
  }
  const written = [...files.keys()].map((rel) => `${VIEWS_DIR}/${name}/${rel}`);
  if (!dryRun) {
    for (const old of [...replaces, ...emptied]) rmSync(path.join(siteRoot, VIEWS_DIR, old), { recursive: true, force: true });
    for (const [id, holder] of taken) rmSync(path.join(siteRoot, VIEWS_DIR, holder, id), { recursive: true, force: true });
    const dir = path.join(siteRoot, VIEWS_DIR, name);
    rmSync(dir, { recursive: true, force: true });
    for (const [rel, bytes] of files) {
      mkdirSync(path.dirname(path.join(dir, rel)), { recursive: true });
      writeFileSync(path.join(dir, rel), bytes);
    }
    mkdirSync(path.dirname(manifestPath), { recursive: true });
    writeFileSync(manifestPath, `${JSON.stringify({ version: allowlist.version, batches }, null, 2)}\n`);
  }
  return { batch: record, written, notes, drafts: entries.filter((entry) => entry.captionDraft || entry.context?.textDraft).map((entry) => entry.id), ready };
}

const invokedDirectly = process.argv[1] && import.meta.url === pathToFileURL(path.resolve(process.argv[1])).href;
if (invokedDirectly) {
  const args = process.argv.slice(2);
  const dir = args.find((arg, i) => !arg.startsWith('--') && args[i - 1] !== '--replaces' && args[i - 1] !== '--replaces-view');
  if (!dir) {
    console.error('Usage: node scripts/import-views.mjs <batch directory> [--replaces <batch>] [--replaces-view <id>] [--dry-run]');
    process.exit(2);
  }
  try {
    const root = path.resolve(path.dirname(fileURLToPath(import.meta.url)), '..');
    const replaces = args.flatMap((arg, i) => (arg === '--replaces' && args[i + 1] ? [args[i + 1]] : []));
    const replacesViews = args.flatMap((arg, i) => (arg === '--replaces-view' && args[i + 1] ? [args[i + 1]] : []));
    const { batch, written, drafts, notes, ready } = importBatch(path.resolve(dir), root, { dryRun: args.includes('--dry-run'), replaces, replacesViews });
    console.log(`Declared ready by ${ready.path} (${ready.at}): manifest.json SHA-256 ${batch.manifest.sha256}.`);
    console.log(`${args.includes('--dry-run') ? 'Would import' : 'Imported'} batch ${batch.batch}: ${batch.views.length} views, ${written.length} files.`);
    for (const file of written) console.log(`  ${file}`);
    if (drafts.length) console.log(`Draft captions to review before a page uses them: ${drafts.join(', ')}`);
    for (const note of notes) console.log(`Note: ${note}`);
  } catch (error) {
    console.error(error.message);
    process.exitCode = 1;
  }
}
