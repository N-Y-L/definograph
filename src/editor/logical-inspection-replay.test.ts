import { readFileSync } from 'node:fs';
import { describe, expect, it } from 'vitest';
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { PositionalStructuralInput } from '../packets/structure';
import { sourceSnapshotValidation as shared, type ClosureItem } from './source-snapshot';
import { logicalDeclarations, validateLogicalCandidate } from './logical-inspection-replay';

const location = process.env.DEFINOGRAPH_SOURCE_LOGICAL_BACKEND_FIXTURES;
const rows: JsonObject[] = location ? JSON.parse(readFileSync(location, 'utf8')) : [];
const object = (value: unknown) => value as JsonObject;
const array = (value: unknown) => value as JsonValue[];
const canonical = (value: unknown) => createExactJsonTools().canonical(value as JsonValue);
const logical = rows.flatMap(row => {
  const checking = object(row.checking);
  return array(checking.steps).filter(step => object(object(step).operation).kind === 'logical' && object(object(step).output).status === 'candidate')
    .map(step => ({ row, checking, step: object(step) }));
});
function items(input: PositionalStructuralInput): ClosureItem[] {
  const reversed: ClosureItem[] = []; let tel = array(input.home.telescope);
  while (tel[0] !== 'nil') {
    if (tel[0] === 'port') { const attrs = object(tel[2]); reversed.push({ name: attrs.name, info: attrs.info, type: tel[3] }); }
    else reversed.push({ name: tel[2], nondep: tel[3] as boolean, type: tel[4], value: tel[5] });
    tel = array(tel[1]);
  }
  return reversed.reverse();
}

describe.skipIf(!location)('actual native logical formation associations', () => {
  it('reconstructs every actual root/domain declaration and every coherent prefix', () => {
    expect(rows).toHaveLength(28); expect(logical.length).toBeGreaterThan(25);
    for (const { checking, step } of logical) {
      const input = step.input as unknown as PositionalStructuralInput, binding = object(checking.binding);
      const candidate = validateLogicalCandidate(step.output, input, array(binding.universeParams), ['output']);
      const prefix = shared.strName(binding.declarationPrefix, `step${step.index}`);
      const count = Number(step.receiptCount), offset = Number(step.receiptStart);
      for (let length = 0; length <= count; length++) {
        const declarations = logicalDeclarations(candidate, input, items(input), prefix, array(binding.universeParams), length);
        expect(canonical(declarations)).toBe(canonical(array(checking.checks).slice(offset, offset + length).map(check => object(check).declaration)));
      }
    }
  });
  it('refuses wrong standard module/category/universe metadata and operand paths', () => {
    const found = logical.find(({ step }) => object(object(step.output).shape).form === 'eq')!;
    const input = found.step.input as unknown as PositionalStructuralInput, params = array(object(found.checking.binding).universeParams);
    const mutations = [
      (out: JsonObject) => { object(object(out.shape).descriptor).declaringModule = shared.named('Pretend'); },
      (out: JsonObject) => { object(object(out.shape).descriptor).kind = 'thmDecl'; },
      (out: JsonObject) => { object(object(out.shape).descriptor).safety = 'unsafe'; },
      (out: JsonObject) => { object(object(out.shape).descriptor).levelParams = []; },
      (out: JsonObject) => { object(object(out.shape).descriptor).name = shared.named('Imitation'); },
      (out: JsonObject) => { object(array(object(out.shape).operands)[0]).path = ['appArg']; },
      (out: JsonObject) => { object(out.shape).form = '__proto__'; },
      (out: JsonObject) => { object(out.result).term = ['const', shared.named('False'), []]; },
      (out: JsonObject) => { out.domain = { term: ['sort', ['zero']], inferredType: ['sort', ['zero']] }; },
    ];
    for (const mutate of mutations) {
      const output = structuredClone(found.step.output) as JsonObject; mutate(output);
      expect(() => validateLogicalCandidate(output, input, params, ['output'])).toThrow();
    }
  });
  it('refuses erased proof dependence or a domain attached to the wrong occurrence', () => {
    const found = logical.find(({ row }) => row.label === 'dependent-proof')!;
    const input = found.step.input as unknown as PositionalStructuralInput, params = array(object(found.checking.binding).universeParams);
    const erased = structuredClone(found.step.output) as JsonObject;
    object(erased.shape).bodyUsesBinder = false;
    expect(() => validateLogicalCandidate(erased, input, params, ['output'])).toThrow();
    const wrongDomain = structuredClone(found.step.output) as JsonObject;
    object(wrongDomain.domain).term = ['const', shared.named('False'), []];
    expect(() => validateLogicalCandidate(wrongDomain, input, params, ['output'])).toThrow();
  });
});
