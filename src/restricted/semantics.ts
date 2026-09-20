import type { Expr } from '../core/types';
import type { SemanticPlugin, SemanticRuleMatch } from '../semantic/types';

type Application = Extract<Expr, { kind: 'app' }>;
type ArgumentKind = NonNullable<Application['argumentKinds']>[number];
export type RestrictedMapKind = 'partial-equivalence' | 'open-partial-homeomorphism';
export type RestrictedDirection = 'forward' | 'inverse';
export interface RestrictedMapParts {
  readonly kind: RestrictedMapKind;
  /** Orientation of this operation, relative to the original map object. */
  readonly direction: RestrictedDirection;
  readonly map: Expr;
  readonly sourceCarrier: Expr;
  readonly targetCarrier: Expr;
  /** The side of the original map; symm.source is therefore target. */
  readonly region?: 'source' | 'target';
  readonly regionExpression?: Expr;
  readonly input?: Expr;
  readonly output?: Expr;
}
const partialType = ['type', 'type'] as const;
const openType = ['type', 'type', 'instance', 'instance'] as const;
const partialValue = [...partialType, 'value'] as const;
const openValue = [...openType, 'value'] as const;
const port = (role: string, expression: Expr) => ({ role, expression });
function application(expression: Expr, name: string, kinds: readonly ArgumentKind[], result?: 'type' | 'set'): boolean {
  return expression.kind === 'app' && expression.fn.kind === 'const' && expression.fn.name === name && expression.fn.canonical === true
    && expression.args.length === kinds.length && expression.argumentKinds?.length === kinds.length
    && expression.argumentKinds.every((kind, index) => kind === kinds[index])
    && (!result || expression.typeDescriptor?.kind === result);
}
const flip = (direction: RestrictedDirection): RestrictedDirection => direction === 'forward' ? 'inverse' : 'forward';

/** Only these audited constructors change object identity or orientation. An
 * unfamiliar map-producing expression is retained as its own complete object. */
function bundle(value: Expr, kind: RestrictedMapKind, sourceCarrier: Expr, targetCarrier: Expr, depth = 0): RestrictedMapParts | undefined {
  if (depth > 32) return;
  const symmName = kind === 'partial-equivalence' ? 'PartialEquiv.symm' : 'OpenPartialHomeomorph.symm';
  const valueKinds = kind === 'partial-equivalence' ? partialValue : openValue;
  if (value.kind === 'app' && application(value, symmName, valueKinds)) {
    const original = bundle(value.args.at(-1)!, kind, value.args[0]!, value.args[1]!, depth + 1);
    return original && { ...original, direction: flip(original.direction) };
  }
  if (kind === 'partial-equivalence' && value.kind === 'app' && application(value, 'OpenPartialHomeomorph.toPartialEquiv', openValue)) {
    return bundle(value.args[4]!, 'open-partial-homeomorphism', value.args[0]!, value.args[1]!, depth + 1);
  }
  return { kind, direction: 'forward', map: value, sourceCarrier, targetCarrier };
}

/** Decode actual exported projections; no printed type or theorem-name guesses.
 * A stored function is total. Its inverse laws are restricted to source/target. */
export function restrictedMapParts(expression: Expr): RestrictedMapParts | undefined {
  if (expression.kind !== 'app') return;
  for (const region of ['source', 'target'] as const) {
    if (application(expression, `PartialEquiv.${region}`, partialValue, 'set')) {
      const base = bundle(expression.args[2]!, 'partial-equivalence', expression.args[0]!, expression.args[1]!);
      return base && { ...base, region: base.direction === 'forward' ? region : region === 'source' ? 'target' : 'source', regionExpression: expression };
    }
  }
  for (const inverse of [false, true]) {
    if (application(expression, inverse ? 'PartialEquiv.invFun' : 'PartialEquiv.toFun', [...partialValue, 'value'])) {
      const base = bundle(expression.args[2]!, 'partial-equivalence', expression.args[0]!, expression.args[1]!);
      return base && { ...base, direction: inverse ? flip(base.direction) : base.direction, input: expression.args[3]!, output: expression };
    }
  }
  if (application(expression, "OpenPartialHomeomorph.toFun'", [...openValue, 'value'])) {
    const base = bundle(expression.args[4]!, 'open-partial-homeomorphism', expression.args[0]!, expression.args[1]!);
    return base && { ...base, input: expression.args[5]!, output: expression };
  }
}

const basePorts = (parts: RestrictedMapParts) => [port('map', parts.map), port('source carrier', parts.sourceCarrier), port('target carrier', parts.targetCarrier)];
function conditions(kind: RestrictedMapKind): readonly string[] {
  return [
    'The forward map sends source to target; the inverse map sends target to source. The two compositions return the input on those respective sets.',
    'The stored functions are defined on the entire carriers. Outside source and target, their values need not satisfy either inverse law.',
    'Neither region is assumed nonempty or the whole carrier; no coordinates, dimension, or particular points are supplied.',
    ...(kind === 'open-partial-homeomorphism' ? ['Source and target are open in the supplied topologies. The forward and inverse maps are continuous on these respective regions.'] : []),
  ];
}
function common(parts: RestrictedMapParts) {
  return { fidelity: 'symbolic' as const, restrictedMapKind: parts.kind, restrictedDirection: parts.direction, conditions: conditions(parts.kind) };
}
export function restrictedBinderSemantics(value: Expr, typeExpression: Expr): SemanticRuleMatch | undefined {
  const kind = application(typeExpression, 'PartialEquiv', partialType, 'type') ? 'partial-equivalence'
    : application(typeExpression, 'OpenPartialHomeomorph', openType, 'type') ? 'open-partial-homeomorphism' : undefined;
  if (!kind || typeExpression.kind !== 'app') return;
  const parts = bundle(value, kind, typeExpression.args[0]!, typeExpression.args[1]!);
  if (!parts) return;
  return { ...common(parts), kind: 'restricted-equivalence', label: kind === 'partial-equivalence' ? 'equivalence between designated subsets' : 'homeomorphism between open subsets', arguments: basePorts(parts) };
}
export const restrictedSemanticPlugin: SemanticPlugin = {
  id: 'restricted-maps', version: '1.0.0', title: 'Maps inverse on designated regions',
  capabilities: ['restricted-equivalence', 'restricted-region', 'restricted-application'],
  limitations: [
    'Inverse and image laws apply on the designated source/target only; no global inverse is inferred.',
    'Openness and continuity are properties in the supplied topologies, not coordinate geometry or differentiability.',
    'Only canonical fully applied Mathlib projections and exact symm/forgetful constructions are interpreted.',
  ],
  matchBinder: restrictedBinderSemantics,
  match(expression) {
    const parts = restrictedMapParts(expression);
    if (!parts) return;
    if (parts.region && parts.regionExpression) return { ...common(parts), kind: 'restricted-region', label: `${parts.region} of the restricted equivalence`, restrictedRegion: parts.region, arguments: [...basePorts(parts), port('region', parts.regionExpression)] };
    if (parts.input && parts.output) return { ...common(parts), kind: 'restricted-application', label: `${parts.direction} map value`, arguments: [...basePorts(parts), port('input', parts.input), port('output', parts.output)] };
  },
};
