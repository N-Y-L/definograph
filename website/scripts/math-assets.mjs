// The only fetchable resources a recorded math fragment may add: the reviewed KaTeX
// package's complete WOFF2 set. No stylesheet supplied by a recording is trusted to
// choose URLs, faces, or destinations. This module emits no client-side renderer.
import { createHash } from 'node:crypto';
import { lstatSync, readFileSync, realpathSync } from 'node:fs';
import path from 'node:path';

export const APPROVED_MATH = JSON.parse(readFileSync(new URL('./katex-fonts-approved.json', import.meta.url), 'utf8'));
const hash = bytes => createHash('sha256').update(bytes).digest('hex');
export const MATH_OUTPUT = `assets/math/${APPROVED_MATH.engine}-${APPROVED_MATH.version}`;
export function canonicalFontCss(urlFor = file => `./assets/fonts/${file}`) {
  return APPROVED_MATH.faces.map(face => `@font-face{font-family:"${face.family}";src:url("${urlFor(face.file)}") format("woff2");font-weight:${face.weight};font-style:${face.style};font-display:${face.display};}\n`).join('');
}
const pin = (file, bytes, sha256, mime) => ({ file, sha256, bytes, mime });
const css = Buffer.from(canonicalFontCss());
export const MATH_ASSETS = {
  engine: APPROVED_MATH.engine, version: APPROVED_MATH.version,
  fonts: APPROVED_MATH.faces.map(face => pin(`assets/fonts/${face.file}`, face.bytes, face.sha256, 'font/woff2')),
  license: pin(`assets/licenses/${APPROVED_MATH.license.file}`, APPROVED_MATH.license.bytes, APPROVED_MATH.license.sha256, 'text/plain'),
  stylesheet: pin('math-fonts.css', css.length, hash(css), 'text/css'),
};

function exactRecord(actual, expected, label) {
  if (!actual || Array.isArray(actual) || typeof actual !== 'object') throw new Error(`${label}: expected an object`);
  if (Object.keys(actual).sort().join('|') !== Object.keys(expected).sort().join('|')) throw new Error(`${label}: unexpected or missing fields`);
  for (const [key, value] of Object.entries(expected)) if (actual[key] !== value) throw new Error(`${label}: ${key} does not match approved KaTeX ${APPROVED_MATH.version}`);
}
export function validateMathAssetContract(contract) {
  if (contract === undefined) return;
  if (!contract || Array.isArray(contract) || typeof contract !== 'object') throw new Error('mathAssets: expected an object');
  exactRecord({ ...contract, fonts: null, license: null, stylesheet: null }, { ...MATH_ASSETS, fonts: null, license: null, stylesheet: null }, 'mathAssets');
  if (!Array.isArray(contract.fonts) || contract.fonts.length !== MATH_ASSETS.fonts.length) throw new Error('mathAssets.fonts: the complete approved set is required');
  contract.fonts.forEach((font, index) => exactRecord(font, MATH_ASSETS.fonts[index], `mathAssets.fonts[${index}]`));
  exactRecord(contract.license, MATH_ASSETS.license, 'mathAssets.license');
  exactRecord(contract.stylesheet, MATH_ASSETS.stylesheet, 'mathAssets.stylesheet');
}
// Reject symlinked assets, including intermediate path components; every input must
// reside in this actual batch directory. Paths have already matched the fixed set.
export function readMathAsset(base, relative) {
  const root = realpathSync(base);
  let current = root;
  for (const part of relative.split('/')) {
    current = path.join(current, part);
    if (lstatSync(current).isSymbolicLink()) throw new Error(`mathAssets: symlink is not allowed: ${relative}`);
  }
  if (!lstatSync(current).isFile() || !current.startsWith(`${root}${path.sep}`)) throw new Error(`mathAssets: not a batch file: ${relative}`);
  return readFileSync(current);
}
export function verifyMathAssets(contract, read) {
  validateMathAssetContract(contract);
  const files = new Map();
  if (contract === undefined) return files;
  for (const entry of [...contract.fonts, contract.license, contract.stylesheet]) {
    const bytes = read(entry.file);
    if (!Buffer.isBuffer(bytes) || bytes.length !== entry.bytes || hash(bytes) !== entry.sha256) throw new Error(`mathAssets: ${entry.file} does not match its approved bytes/hash`);
    if (entry.mime === 'font/woff2' && bytes.subarray(0, 4).toString('ascii') !== 'wOF2') throw new Error(`mathAssets: ${entry.file} is not WOFF2`);
    files.set(entry.file, bytes);
  }
  // The pin is to these exact bytes, not merely to CSS that parses similarly.
  if (!files.get('math-fonts.css').equals(css)) throw new Error('mathAssets: stylesheet is not canonical');
  return files;
}
export function mathAssetOutputs(batches) {
  if (!batches.some(batch => batch.mathAssets !== undefined)) return [];
  for (const batch of batches) validateMathAssetContract(batch.mathAssets);
  return [...MATH_ASSETS.fonts, MATH_ASSETS.license].map(entry => ({ ...entry, output: `${MATH_OUTPUT}/${path.posix.basename(entry.file)}` }));
}
export function publishedMathCss(batches) {
  return mathAssetOutputs(batches).length ? canonicalFontCss(file => `/${MATH_OUTPUT}/${file}`) : '';
}
export function publishedMathFiles(batches) {
  const outputs = mathAssetOutputs(batches);
  if (!outputs.length) return [];
  const withMath = batches.filter(batch => batch.mathAssets !== undefined);
  return outputs.map(entry => {
    const candidates = withMath.map(batch => batch.mathFiles?.get(entry.file));
    if (candidates.some(bytes => !bytes || bytes.length !== entry.bytes || hash(bytes) !== entry.sha256)) throw new Error(`mathAssets: missing or conflicting verified bytes for ${entry.file}`);
    return { ...entry, bytes: candidates[0] };
  });
}
// Allow exactly the generated face block in the combined stylesheet, nothing else
// that fetches. This also refuses a duplicate copy of an approved block.
export function validatePublishedMathCss(text, batches) {
  const allowed = publishedMathCss(batches);
  if (allowed && !text.startsWith(allowed)) return ['published stylesheet: canonical math faces must occur exactly once at the start'];
  const rest = allowed ? text.slice(allowed.length) : text;
  return /url\(|@import|@font-face/i.test(rest.replace(/\/\*[\s\S]*?\*\//g, '')) ? ['published stylesheet: resource rule outside the approved math faces'] : [];
}
