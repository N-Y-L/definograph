import assert from 'node:assert/strict';
import { readFileSync } from 'node:fs';
import path from 'node:path';
import { escapeHtml } from './format.mjs';
import { parseHtml } from './html.mjs';
import { checkPageDirectives } from './page-directives.mjs';

export function runPageDirectiveSelfTest(root) {
  const failures = []; let cases = 0;
  const test = (name, run) => { cases++; try { run(); } catch (error) { failures.push(`${name}: ${error.message}`); } };
  const original = readFileSync(path.join(root, 'scripts/fixtures/math/epsilon.html'), 'utf8');
  const doc = parseHtml(original), group = doc.elements.find(n => n.attrs.has('data-math-label'));
  const annotation = doc.elements.find(n => n.name === 'annotation' && n.ancestors.includes(group));
  const tex = doc.text(annotation), nested = `{{${tex}}}`;
  // Extra grouping leaves this fixture's mathematical expression unchanged.
  const fragment = (original.slice(0, annotation.innerStart) + escapeHtml(nested) + original.slice(annotation.innerEnd)).replace(`data-math-label="${escapeHtml(group.attrs.get('data-math-label'))}"`, `data-math-label="${escapeHtml(group.attrs.get('data-math-label').slice(0, -tex.length) + nested)}"`).trimEnd();
  const registry = text => new Map([['fixture-math', { fragmentText: text, batch: { mathAssets: {}, mathFiles: new Map() } }]]);
  const page = text => `<main>${text}</main>`;
  test('nested TeX in exact validated annotation and key passes', () => assert.deepEqual(checkPageDirectives(page(fragment), registry(fragment)), []));
  test('unknown recording gets no exemption', () => assert.ok(checkPageDirectives(page(fragment), new Map()).length));
  test('missing approved font assets gets no exemption', () => assert.ok(checkPageDirectives(page(fragment), new Map([['fixture-math', { fragmentText: fragment, batch: {} }]])).length));
  test('altered recording gets no exemption', () => assert.ok(checkPageDirectives(page(fragment.replace('data-diagram-label="', 'data-diagram-label="changed-')), registry(fragment)).length));
  for (const text of ['{{view:missing}}', '{{title}}', '}}']) test(`outside math rejects ${text}`, () => assert.ok(checkPageDirectives(page(fragment)+text, registry(fragment)).length));
  test('ordinary attribute retains brace check', () => assert.ok(checkPageDirectives(page(fragment)+'<p title="{{title}}">text</p>', registry(fragment)).length));
  test('fake annotation outside a recording is refused', () => assert.ok(checkPageDirectives('<annotation encoding="application/x-tex">{{x}}</annotation>', new Map()).length));
  test('directive inside recorded TeX remains fatal', () => { const changed = fragment.replace('</annotation>', '{{view:missing}}</annotation>'); assert.ok(checkPageDirectives(page(changed), registry(changed)).length); });
  test('malformed MathML receives no exemption', () => { const changed = fragment.replace('application/x-tex', 'text/html'); assert.ok(checkPageDirectives(page(changed), registry(changed)).length); });
  test('existing source-listing exemption remains', () => assert.deepEqual(checkPageDirectives('<pre>{{x}}</pre>', new Map()), []));
  return { failures, cases };
}
