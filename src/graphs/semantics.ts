import type { Expr } from '../core/types';
import { headName } from '../core/expression';
import type { SemanticPlugin, SemanticRuleMatch } from '../semantic/types';

type Application = Extract<Expr, { kind: 'app' }>;
type ArgumentKind = NonNullable<Application['argumentKinds']>[number];
const port = (role: string, expression: Expr) => ({ role, expression });
/** This family requires native v2 provenance and exact saturation. No pretty-text guesses. */
function application(expression: Expr, name: string, arguments_: readonly ArgumentKind[], result?: 'type' | 'proposition'): boolean {
  return expression.kind === 'app' && expression.fn.kind === 'const' && expression.fn.canonical === true && headName(expression) === name
    && expression.args.length === arguments_.length && expression.argumentKinds?.length === arguments_.length
    && expression.argumentKinds.every((kind, index) => kind === arguments_[index])
    && (!result || expression.typeDescriptor?.kind === result);
}
const coloringArguments = ['type', 'value', 'type'] as const;
const mapArguments = ['type', 'type', 'value', 'value'] as const;

/** The bound value is supplied by the compiler at its actual lexical introduction. */
export function graphBinderSemantics(value: Expr, typeExpression: Expr): SemanticRuleMatch | undefined {
  if (typeExpression.kind !== 'app') return;
  if (application(typeExpression, 'SimpleGraph.Coloring', coloringArguments, 'type')) {
    return {
      kind: 'graph-coloring', label: 'proper coloring', fidelity: 'symbolic',
      arguments: [port('graph', typeExpression.args[1]!), port('coloring', value), port('colors', typeExpression.args[2]!)],
      conditions: [
        'This bundled coloring sends adjacent vertices to different colors.',
        'No vertex positions, complete graph instance, particular color assignment, or use of every available color is asserted.',
      ],
    };
  }
  const hom = application(typeExpression, 'SimpleGraph.Hom', mapArguments, 'type');
  const embedding = application(typeExpression, 'SimpleGraph.Embedding', mapArguments, 'type');
  if (hom || embedding) {
    const type = typeExpression as Application;
    return {
      kind: 'graph-map', label: embedding ? 'graph embedding' : 'graph homomorphism',
      fidelity: 'symbolic', graphMapKind: embedding ? 'embedding' : 'homomorphism',
      arguments: [port('source graph', type.args[2]!), port('target graph', type.args[3]!), port('map', value)],
      conditions: embedding ? [
        'The map is injective and adjacency holds exactly when the image vertices are adjacent.',
        'The image is an induced subgraph; no target-wide surjectivity or coordinates are asserted.',
      ] : [
        'Adjacency in the source implies adjacency between image vertices in the target.',
        'Injectivity, surjectivity, and the converse implication are not asserted.',
      ],
    };
  }
}

/** Reads the canonical bundled-function coercion, including its native instance audit. */
function graphApplication(expression: Expr): SemanticRuleMatch | undefined {
  if (expression.kind !== 'app') return;
  if (!application(expression, 'DFunLike.coe', ['type', 'type', 'value', 'instance', 'value', 'value']) || expression.standard !== true) return;
  const bundle = graphBinderSemantics(expression.args[4]!, expression.args[0]!);
  if (!bundle) return;
  return { ...bundle,
    label: bundle.kind === 'graph-coloring' ? 'color of a vertex' : 'image of a vertex',
    arguments: [...bundle.arguments,
      port(bundle.kind === 'graph-coloring' ? 'vertex' : 'source vertex', expression.args[5]!),
      port(bundle.kind === 'graph-coloring' ? 'color' : 'target vertex', expression)],
  };
}

export const graphSemanticPlugin: SemanticPlugin = {
  id: 'graphs', version: '1.0.0', title: 'Simple graphs and proper colorings',
  capabilities: ['graph-adjacency', 'graph-coloring', 'graph-colorable', 'graph-map'],
  limitations: [
    'A symbolic adjacency slot is a constraint in the surrounding logical context, not an enumerated graph.',
    'A coloring bound is an upper bound on available colors; no witness or exact number of used colors is inferred.',
    'Only canonical fully applied Mathlib simple-graph constructors and audited bundled coercions are interpreted.',
  ],
  match(expression) {
    if (expression.kind !== 'app') return;
    if (application(expression, 'SimpleGraph.Adj', ['type', 'value', 'value', 'value'], 'proposition')) {
      return { kind: 'graph-adjacency', label: 'adjacent in the graph', fidelity: 'symbolic',
        arguments: [port('graph', expression.args[1]!), port('left vertex', expression.args[2]!), port('right vertex', expression.args[3]!)],
        conditions: ['A simple graph has symmetric, irreflexive adjacency.', 'This adjacency clause keeps its quantifier, premise, negation, or alternative context. No other edges are inferred.'],
      };
    }
    if (application(expression, 'SimpleGraph.Colorable', ['type', 'value', 'value'], 'proposition')) {
      return { kind: 'graph-colorable', label: 'colorable with at most this many colors', fidelity: 'symbolic',
        arguments: [port('graph', expression.args[1]!), port('color bound', expression.args[2]!)],
        conditions: ['There exists a proper coloring into Fin n. This does not exhibit a coloring or assert that every available color is used.', 'A zero color bound permits only an empty vertex type; nonempty vertices are not assumed.'],
      };
    }
    return graphApplication(expression);
  },
};
