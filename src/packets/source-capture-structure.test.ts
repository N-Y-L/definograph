import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import type { JsonValue } from './packet';
import { buildStructuralDrawing, readStructuralDrawing, type ExternalDeclarationInput } from './structure';

// Generate this external corpus with scripts/structure-capture.lean and the
// configured SourceCapture imports. No producer trust is inferred by these tests.
const file = process.env.DEFINOGRAPH_SOURCE_CAPTURES;
interface CapturedCase {
  label: string;
  binding: { schema: 1 | 2; sourceTerm: JsonValue; sourceType: JsonValue; context: { originalDeclarations: ExternalDeclarationInput[] } };
  checks: { outcome: { tag: string } }[];
}
describe.skipIf(!file)('structural reading of actual Lean source captures', () => {
  const cases = file ? JSON.parse(readFileSync(file, 'utf8')) as CapturedCase[] : [];
  it('contains successful actual captures covering the intended independent controls', () => {
    expect(cases.map(item => item.label)).toEqual(['dependent external home', 'opaque stored metadata',
      'nested definition and projection', 'owned have', 'dependent function type', 'structured universes', 'string literal', 'natural zero', 'natural one', 'natural safe maximum',
      'natural first unsafe', 'natural adjacent unsafe', 'natural two to sixty four', 'natural long decimal',
      'numeric binder names', 'numeric external user name', 'numeric universe name']);
    for (const item of cases) {
      expect(item.binding.schema).toBe(2);
      expect(item.checks).toHaveLength(2);
      expect(item.checks.every(check => check.outcome.tag === 'accepted')).toBe(true);
    }
  });
  it('preserves independent decimal oracles from actual Lean literal captures', () => {
    const expected: Record<string, string> = {
      'natural zero': '0', 'natural one': '1', 'natural safe maximum': '9007199254740991',
      'natural first unsafe': '9007199254740992', 'natural adjacent unsafe': '9007199254740993',
      'natural two to sixty four': '18446744073709551616', 'natural long decimal': '1' + '0'.repeat(126) + '7',
    };
    for (const [label, digits] of Object.entries(expected)) {
      const raw = cases.find(item => item.label === label)?.binding.sourceTerm;
      expect(raw, label).toEqual(['lit', ['natVal', ['nat', digits]]]);
    }
  });
  it('independently reconstructs exact named terms, supplied types and all local metadata', () => {
    for (const item of cases) for (const field of ['sourceTerm', 'sourceType'] as const) {
      const externalContext = item.binding.context.originalDeclarations;
      const result = buildStructuralDrawing(item.binding[field], {
        sourceIdentity: `capture:${item.label}:${field}`, sourcePath: ['binding', field], externalContext, profile: item.binding.schema,
      });
      expect(result.ok, `${item.label}/${field}: ${JSON.stringify(result)}`).toBe(true);
      if (!result.ok) continue;
      const readback = readStructuralDrawing(result.value);
      expect(readback).toEqual({ ok: true, value: { expression: item.binding[field], externalContext } });
      if (item.label === 'opaque stored metadata') {
        const declaration = result.value.declarations.find(d => d.kind === 'external');
        expect(declaration?.kind).toBe('external');
        if (declaration?.kind === 'external') expect(declaration.children.map(edge => edge.role)).toEqual(['type', 'storedValue']);
      }
    }
  });
});
