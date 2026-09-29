/** Exact direct-field syntax and declaration associations. Saved metadata does
 * not authenticate a Lean environment or replace the displayed check outcomes. */
import { createExactJsonTools, type JsonObject, type JsonValue } from '../packets/packet';
import type { RawPath } from '../packets/raw';
import type { PositionalStructuralInput } from '../packets/structure';
import { encodeNatural } from '../packets/natural';
import { sourceSnapshotValidation as shared, type ClosureItem } from './source-snapshot';
import { validateHeadExpression } from './head-exposure-replay';

export type DirectFieldEntry = JsonObject & {
  index: number; name: JsonValue; projector: JsonValue; binderInfo: string; parent: JsonValue;
  projectionInfo: JsonObject; declaration: JsonObject;
};
export type DirectFieldCatalogue = JsonObject & {
  structure: JsonObject; constructor: JsonObject; actualLevels: JsonValue[];
  parameters: JsonValue[]; fields: DirectFieldEntry[]; omittedFields: number;
};
const { object, array, exact, operational, preflight, close, named, strName, constant } = shared;
const requireThat: (condition: unknown, message: string, path: RawPath) => asserts condition = shared.requireThat;
const key = (value: JsonValue) => createExactJsonTools().canonical(value);
const info = new Set(['default', 'implicit', 'strictImplicit', 'instImplicit']);

function checkedName(value: JsonValue, path: RawPath): void {
  validateHeadExpression(['const', value, []], 0, path);
  requireThat(key(value) !== '["anonymous"]', 'metadata declaration names must be nonempty', path);
}
function formalLevels(value: JsonValue, path: RawPath): JsonValue[] {
  const levels = array(value, path);
  requireThat(levels.length <= 128, 'too many formal universe parameters', path);
  const seen = new Set<string>();
  levels.forEach((name, i) => {
    checkedName(name, [...path, i]); const identity = key(name);
    requireThat(!seen.has(identity), 'duplicate formal universe parameter', [...path, i]); seen.add(identity);
  });
  return levels;
}
function bounded(value: JsonValue, maximum: number, path: RawPath): number {
  const count = operational(value, path);
  requireThat(count <= maximum, 'field metadata count exceeds its bound', path); return count;
}
function signature(value: JsonObject, path: RawPath): JsonValue[] {
  checkedName(value.name, [...path, 'name']);
  const levels = formalLevels(value.levelParams, [...path, 'levelParams']);
  validateHeadExpression(value.type, 0, [...path, 'type'], levels); return levels;
}

export function validateDirectFieldCatalogue(value: JsonValue, input: PositionalStructuralInput,
  universeParams: JsonValue[], path: RawPath): DirectFieldCatalogue {
  preflight({ value, input, universeParams }, 2 * 1024 * 1024, path, false, 120);
  const c = object(value, ['structure', 'constructor', 'actualLevels', 'parameters', 'fields', 'omittedFields'], path);
  const s = object(c.structure, ['name', 'levelParams', 'type', 'numParams', 'numIndices', 'isRec', 'isUnsafe', 'constructor'], [...path, 'structure']);
  const ctor = object(c.constructor, ['name', 'levelParams', 'type', 'induct', 'cidx', 'numParams', 'numFields', 'isUnsafe'], [...path, 'constructor']);
  const formal = signature(s, [...path, 'structure']); signature(ctor, [...path, 'constructor']);
  requireThat(s.numIndices === 0 && s.isRec === false && s.isUnsafe === false && ctor.cidx === 0 && ctor.isUnsafe === false,
    'unsupported structure or constructor profile', path);
  exact(ctor.induct, s.name, [...path, 'constructor', 'induct']); exact(s.constructor, ctor.name, [...path, 'structure', 'constructor']);
  exact(ctor.levelParams, formal, [...path, 'constructor', 'levelParams']); exact(ctor.numParams, s.numParams, [...path, 'constructor', 'numParams']);
  const parameterCount = bounded(s.numParams, 128, [...path, 'structure', 'numParams']);
  const fieldCount = bounded(ctor.numFields, 65536, [...path, 'constructor', 'numFields']);
  const levels = array(c.actualLevels, [...path, 'actualLevels']), parameters = array(c.parameters, [...path, 'parameters']);
  requireThat(levels.length === formal.length && parameters.length === parameterCount, 'actual structure arity differs', path);
  levels.forEach((level, i) => validateHeadExpression(['sort', level], 0, [...path, 'actualLevels', i], universeParams));
  parameters.forEach((parameter, i) => validateHeadExpression(parameter, input.home.arity, [...path, 'parameters', i], universeParams));
  let ownerType: JsonValue = ['const', s.name, levels];
  for (const parameter of parameters) ownerType = ['app', ownerType, parameter];
  exact(input.type, ownerType, [...path, 'structure']);
  const fields = array(c.fields, [...path, 'fields']);
  requireThat(fields.length === Math.min(fieldCount, 16), 'catalogue is not the complete supported direct-field prefix', [...path, 'fields']);
  exact(c.omittedFields, fieldCount - fields.length, [...path, 'omittedFields']);
  const names = new Set<string>(), projectors = new Set<string>();
  fields.forEach((value, index) => {
    const p = [...path, 'fields', index], f = object(value, ['index', 'name', 'projector', 'binderInfo', 'parent', 'projectionInfo', 'declaration'], p);
    exact(f.index, index, [...p, 'index']); checkedName(f.name, [...p, 'name']); checkedName(f.projector, [...p, 'projector']);
    const name = array(f.name, [...p, 'name']);
    requireThat(name.length === 3 && name[0] === 'str' && key(name[1]) === '["anonymous"]' && typeof name[2] === 'string' && name[2].length > 0,
      'direct field name must be a nonempty single component', [...p, 'name']);
    requireThat(!names.has(key(f.name)) && !projectors.has(key(f.projector)), 'duplicate direct field or projector identity', p);
    names.add(key(f.name)); projectors.add(key(f.projector));
    requireThat(typeof f.binderInfo === 'string' && info.has(f.binderInfo), 'invalid field binder info', [...p, 'binderInfo']);
    if (f.parent !== null) checkedName(f.parent, [...p, 'parent']);
    const projection = object(f.projectionInfo, ['ctorName', 'numParams', 'index', 'fromClass'], [...p, 'projectionInfo']);
    exact(projection.ctorName, ctor.name, [...p, 'projectionInfo', 'ctorName']); exact(projection.numParams, parameterCount, [...p, 'projectionInfo', 'numParams']);
    exact(projection.index, index, [...p, 'projectionInfo', 'index']);
    requireThat(typeof projection.fromClass === 'boolean', 'invalid projector class flag', [...p, 'projectionInfo', 'fromClass']);
    const declaration = object(f.declaration, ['kind', 'name', 'levelParams', 'type', 'safety'], [...p, 'declaration']);
    requireThat((declaration.kind === 'defnDecl' || declaration.kind === 'thmDecl') && declaration.safety === 'safe',
      'unsupported projector declaration category', [...p, 'declaration']);
    exact(declaration.name, f.projector, [...p, 'declaration', 'name']);
    exact(declaration.levelParams, formal, [...p, 'declaration', 'levelParams']); signature(declaration, [...p, 'declaration']);
  });
  return c as DirectFieldCatalogue;
}

/** Rebuild both field terms from the checked predecessor catalogue, never from
 * a newly supplied executable term or a pretty field label. */
export function validateDirectFieldCandidate(value: JsonValue, input: PositionalStructuralInput,
  catalogue: DirectFieldCatalogue, index: number, universeParams: JsonValue[], path: RawPath): JsonObject {
  preflight({ value, input, catalogue, universeParams }, 4 * 1024 * 1024, path, false, 120);
  requireThat(Number.isSafeInteger(index) && index >= 0 && index < catalogue.fields.length,
    'projection does not select an available catalogue entry', path);
  const candidate = object(value, ['status', 'field', 'primitive', 'result', 'carrierSort', 'checking'], path);
  requireThat(candidate.status === 'candidate', 'invalid projected candidate status', path);
  exact(candidate.field, catalogue.fields[index], [...path, 'field']);
  const result = object(candidate.result, ['home', 'term', 'type'], [...path, 'result']);
  exact(result.home, input.home, [...path, 'result', 'home']);
  let projected: JsonValue = ['const', catalogue.fields[index].projector, catalogue.actualLevels];
  for (const parameter of catalogue.parameters) projected = ['app', projected, parameter];
  projected = ['app', projected, input.term];
  const primitive: JsonValue = ['proj', catalogue.structure.name, encodeNatural(index, 2), input.term];
  validateHeadExpression(projected, input.home.arity, [...path, 'result', 'term'], universeParams);
  validateHeadExpression(primitive, input.home.arity, [...path, 'primitive'], universeParams);
  exact(result.term, projected, [...path, 'result', 'term']); exact(candidate.primitive, primitive, [...path, 'primitive']);
  validateHeadExpression(result.type, input.home.arity, [...path, 'result', 'type'], universeParams);
  validateHeadExpression(['sort', candidate.carrierSort], 0, [...path, 'carrierSort'], universeParams);
  return candidate;
}

export function directFieldDeclarations(candidate: JsonObject, items: ClosureItem[], prefix: JsonValue,
  universeParams: JsonValue[], count: number): JsonObject[] {
  const result = candidate.result as JsonObject;
  return Array.from({ length: count }, (_, i): JsonObject => {
    const component = i === 1, conversion = i === 2;
    const name = strName(strName(prefix, 'project'), conversion ? 'conversion' : component ? 'component' : 'context');
    const eq: JsonValue = ['const', named('Eq'), [candidate.carrierSort]], refl: JsonValue = ['const', strName(named('Eq'), 'refl'), [candidate.carrierSort]];
    const type: JsonValue = conversion ? ['app', ['app', ['app', eq, result.type], result.term], candidate.primitive] : component ? result.type : constant('True');
    const value: JsonValue = conversion ? ['app', ['app', refl, result.type], result.term] : component ? result.term : ['const', strName(named('True'), 'intro'), []];
    return { kind: component ? 'defnDecl' : 'thmDecl', name, levelParams: universeParams,
      type: close(items, type, 'forallE'), value: close(items, value, 'lam'), all: [name], ...(component ? { hints: ['abbrev'], safety: 'safe' } : {}) };
  });
}
