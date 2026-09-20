import { discoverScenes } from '../core/scenes';
import { headName, numericOperator } from '../core/expression';
import type { Binder, Expr, StatementNode, TypeDescriptor } from '../core/types';
import { binderTypeExpression, expressionKey, formatExpression, setConstructionParts, stableHash, visibleApplicationArguments } from './expression';
import { createSemanticRegistry } from './registry';
import { graphBinderSemantics } from '../graphs/semantics';
import { SEMANTIC_DOCUMENT_VERSION } from './types';
import type { AnalysisInput, FragmentCoverage, OpaqueRegion, Provenance, QuantifierChoice, SemanticDocument, SemanticObject, SemanticObjectKind, SemanticPlugin, SemanticRelation, SemanticScope } from './types';

function objectKind(expression: Expr, binder?: Binder): SemanticObjectKind {
  if (setConstructionParts(expression)) return 'set';
  const descriptor: TypeDescriptor | undefined = binder?.typeDescriptor ?? ('typeDescriptor' in expression ? expression.typeDescriptor : undefined);
  if (descriptor?.kind === 'set') return 'set';
  if (descriptor?.kind === 'map' || descriptor?.kind === 'relation') return 'function';
  if (descriptor?.kind === 'type' || expression.kind === 'sort') return 'type';
  if (descriptor && ['real', 'natural', 'integer', 'rational', 'finite'].includes(descriptor.kind)) return 'scalar';
  if (binder?.domain === 'real') return 'scalar';
  if (binder?.domain === 'realFunction' || expression.kind === 'lambda') return 'function';
  if (binder?.domain && ['sup2', 'euclidean2', 'supN', 'euclideanN'].includes(binder.domain)) return 'point';
  if (expression.kind === 'literal') return 'literal';
  if (expression.kind === 'var') return 'variable';
  if (expression.kind === 'const') return 'symbol';
  if (expression.kind === 'app' && ['Metric.ball', 'Metric.closedBall', 'Metric.sphere', 'Set.image', 'Set.preimage'].includes(headName(expression) ?? '')) return 'set';
  return 'expression';
}

/** Adapt elaborated Lean expressions into a renderer-independent semantic document. */
export function compileSemanticDocument(analysis: AnalysisInput, plugins?: readonly SemanticPlugin[]): SemanticDocument {
  const registry = createSemanticRegistry(plugins);
  const identities = new Map<string, string>();
  const binders = new Map<string, Binder>();
  const registerBinder = (binder: Binder): string => {
    if (!identities.has(binder.id)) identities.set(binder.id, `object:b${identities.size}`);
    binders.set(binder.id, binder);
    return identities.get(binder.id)!;
  };
  const index = (node: StatementNode, depth = 0): void => {
    if (depth > 128) return;
    if (node.binder) registerBinder(node.binder);
    node.children.forEach(child => index(child, depth + 1));
  };
  index(analysis.tree);
  const objects = new Map<string, SemanticObject & { provenance: Provenance[] }>();
  const objectKeys = new Map<string, string>();
  const relations: SemanticRelation[] = [];
  const scopes: SemanticScope[] = [];
  const choices: QuantifierChoice[] = [];
  const opaqueRegions: OpaqueRegion[] = [];
  const coverage: FragmentCoverage[] = [];
  const diagnostics: string[] = [];
  const scenes = discoverScenes(analysis.tree);
  let visits = 0;
  const provenance = (nodeId: string, expressionPath: string): Provenance => ({ nodeId, expressionPath, origin: 'elaborated-expression' });
  const object = (expression: Expr, scopeId: string, source: Provenance): string => {
    const binder = expression.kind === 'var' ? binders.get(expression.id) : undefined;
    const key = expressionKey(expression, identities);
    const baseId = expression.kind === 'var' && identities.has(expression.id) ? identities.get(expression.id)! : `object:e${stableHash(key)}`;
    let id = baseId, suffix = 0;
    while (objectKeys.has(id) && objectKeys.get(id) !== key) id = `${baseId}:${++suffix}`;
    const existing = objects.get(id);
    if (existing) {
      if (!existing.provenance.some(p => p.nodeId === source.nodeId && p.expressionPath === source.expressionPath)) existing.provenance.push(source);
      return id;
    }
    objectKeys.set(id, key);
    const label = binder?.role === 'assumption' && binder.name.includes('_@') ? 'Hypothesis' : formatExpression(expression);
    objects.set(id, { id, kind: objectKind(expression, binder), label, type: binder?.type ?? ('type' in expression ? expression.type ?? '' : ''), expression, binder, scopeId, provenance: [source] });
    return id;
  };
  const visitNode = (node: StatementNode, parent: SemanticScope | undefined, activeObjects: readonly string[], assumptions: readonly string[], context: readonly string[], depth: number): void => {
    if (depth > 128 || ++visits > 20_000) { if (!diagnostics.length) diagnostics.push('The semantic traversal limit was reached; the remaining source remains available in the statement tree.'); return; }
    const scopeId = `scope:${node.id}`;
    const localObjects = [...activeObjects];
    let implicationBinderId: string | undefined;
    if (node.binder) {
      const b = node.binder;
      const isImplicationHypothesis = node.kind === 'implies' && b.role === 'assumption' && node.children.length > 1;
      const binderScopeId = isImplicationHypothesis ? `scope:${node.children[1]!.id}` : scopeId;
      const id = object({ kind: 'var', id: b.id, name: b.name, type: b.type, typeDescriptor: b.typeDescriptor }, binderScopeId, provenance(node.id, 'binder'));
      const dependsOn = b.dependsOn.map(dep => identities.get(dep)).filter((dep): dep is string => dep !== undefined && activeObjects.includes(dep));
      choices.push({ id: `choice:${id}`, objectId: id, binderId: b.id, nodeId: node.id, role: b.role, dependsOn, availableObjectIds: [...activeObjects], scopeId: binderScopeId,
        explanation: b.role === 'existential' ? 'Choose a witness using only earlier choices available in this scope. Its existence remains an obligation.'
          : b.role === 'universal' ? 'An arbitrary element of this type. A displayed sample represents one choice, never every element.'
            : b.role === 'assumption' ? 'A local hypothesis; it is available only within this scope.' : b.role === 'parameter' ? 'A parameter of this definition. This function signature is not a universally quantified proposition.' : 'A function input, local to its body.' });
      if (isImplicationHypothesis) implicationBinderId = id;
      else localObjects.push(id);
      // A bundled coloring/map carries constraints as part of its declared type.
      // Attach them to the actual introduced object, never to a fabricated witness.
      const value: Expr = { kind: 'var', id: b.id, name: b.name, type: b.type, typeDescriptor: b.typeDescriptor };
      const typeExpression = binderTypeExpression(node, b);
      const bundled = typeExpression && b.role !== 'assumption' ? graphBinderSemantics(value, typeExpression) : undefined;
      if (bundled && (!plugins || plugins.some(plugin => plugin.id === 'graphs'))) {
        const source = provenance(node.id, 'binder.type');
        relations.push({ id: `relation:${node.id}:binder:graphs`, kind: bundled.kind, label: bundled.label,
          ports: bundled.arguments.map(argument => ({ role: argument.role, objectId: object(argument.expression, binderScopeId, provenance(node.id, `binder.type.${argument.role}`)) })),
          expression: typeExpression!, scopeId: binderScopeId, nodeId: node.id, pluginId: 'graphs', fidelity: bundled.fidelity,
          provenance: source, conditions: bundled.conditions ?? [], ...(bundled.graphMapKind ? { graphMapKind: bundled.graphMapKind } : {}) });
      }
    }
    const scope: SemanticScope = { id: scopeId, parentId: parent?.id, nodeId: node.id, kind: node.kind, label: node.label, objectIds: localObjects, assumptionNodeIds: assumptions, context };
    scopes.push(scope);
    if (node.children.length) {
      node.children.forEach((child, i) => {
        const branchAssumptions = node.kind === 'implies' && i === 1 && node.children[0] ? [...assumptions, node.children[0].id] : assumptions;
        const branchContext = node.kind === 'implies' && i === 0 ? [...context, 'Premise of an implication']
          : node.kind === 'implies' && i === 1 ? [...context, 'Conditional on the premise']
            : node.kind === 'not' ? [...context, 'Inside a negation']
              : node.kind === 'or' ? [...context, `Alternative ${i + 1} of a disjunction`]
                : node.kind === 'iff' ? [...context, `Side ${i + 1} of an equivalence`] : context;
        const branchObjects = node.kind === 'implies' && i === 1 && implicationBinderId ? [...localObjects, implicationBinderId] : localObjects;
        visitNode(child, scope, branchObjects, branchAssumptions, branchContext, depth + 1);
      });
      return;
    }
    const relationStart = relations.length, opaqueStart = opaqueRegions.length;
    const fragmentObjects = new Set(localObjects);
    const seen = new Set<string>();
    const walk = (expression: Expr, path: string, exprDepth: number, expressionScope = scope, expressionObjects: readonly string[] = localObjects): void => {
      if (exprDepth > 128 || ++visits > 20_000) { if (!diagnostics.length) diagnostics.push('The semantic traversal limit was reached.'); return; }
      const key = expressionKey(expression, identities);
      if (seen.has(key)) return;
      seen.add(key);
      const source = provenance(node.id, path);
      const currentScopeId = expressionScope.id;
      fragmentObjects.add(object(expression, currentScopeId, source));
      if (expression.kind === 'lambda' || expression.kind === 'forall') {
        const b = expression.binder;
        registerBinder(b);
        const innerScopeId = `${currentScopeId}:${path}:body`;
        const id = object({ kind: 'var', id: b.id, name: b.name, type: b.type, typeDescriptor: b.typeDescriptor }, innerScopeId, provenance(node.id, `${path}.binder`));
        fragmentObjects.add(id);
        const innerScope: SemanticScope = { id: innerScopeId, parentId: currentScopeId, nodeId: node.id, kind: expression.kind === 'lambda' ? 'parameter' : 'forall', label: `${expression.kind === 'lambda' ? 'Function input' : 'Quantified input'} ${b.name}`, objectIds: [...expressionObjects, id], assumptionNodeIds: expressionScope.assumptionNodeIds, context: [...expressionScope.context, expression.kind === 'lambda' ? 'Within a function body' : 'Within a quantified expression'] };
        scopes.push(innerScope);
        choices.push({ id: `choice:${id}`, objectId: id, binderId: b.id, nodeId: node.id, role: expression.kind === 'lambda' ? 'lambda' : b.role, dependsOn: b.dependsOn.map(dep => identities.get(dep)).filter((dep): dep is string => dep !== undefined && expressionObjects.includes(dep)), availableObjectIds: expressionObjects, scopeId: innerScopeId, explanation: expression.kind === 'lambda' ? 'A function input, bound only within this function body.' : 'An arbitrary element local to this quantified expression.' });
        walk(expression.body, `${path}.body`, exprDepth + 1, innerScope, innerScope.objectIds);
        return;
      }
      const rule = registry.map(plugin => ({ plugin, match: plugin.match(expression) })).find(result => result.match);
      if (rule?.match) {
        const matched = rule.match;
        if (!rule.plugin.capabilities.includes(matched.kind)) throw new Error(`Plugin ${rule.plugin.id} emitted an undeclared capability: ${matched.kind}`);
        const ports = matched.arguments.map(argument => {
          const id = object(argument.expression, currentScopeId, provenance(node.id, `${path}.${argument.role}`));
          fragmentObjects.add(id);
          return { role: argument.role, objectId: id };
        });
        relations.push({ id: `relation:${node.id}:${stableHash(key)}:${rule.plugin.id}`, kind: matched.kind, label: matched.label, ports, expression, scopeId: currentScopeId, nodeId: node.id, pluginId: rule.plugin.id, fidelity: matched.fidelity, provenance: source, conditions: matched.conditions ?? [], ...(matched.setOperation ? { setOperation: matched.setOperation } : {}), ...(matched.graphMapKind ? { graphMapKind: matched.graphMapKind } : {}) });
        matched.arguments.forEach(argument => { if (expressionKey(argument.expression, identities) !== key) walk(argument.expression, `${path}.${argument.role}`, exprDepth + 1, expressionScope, expressionObjects); });
        return;
      }
      if (expression.kind === 'app') {
        if (expression.fn.kind === 'const' && expression.fn.canonical === true && headName(expression) === 'Fin' && expression.args.length === 1 && expression.typeDescriptor?.kind === 'type') {
          walk(expression.args[0]!, `${path}.cardinality`, exprDepth + 1, expressionScope, expressionObjects);
          return;
        }
        const op = numericOperator(expression);
        const valueCount = expression.argumentKinds?.filter(kind => kind === 'value').length;
        const fullNumericExpression = expression.typeDescriptor?.kind !== 'map' && expression.typeDescriptor?.kind !== 'relation';
        if (op && fullNumericExpression && (valueCount === undefined || valueCount >= (['neg', 'abs', 'proj1', 'proj2', 'ofNat'].includes(op) ? 1 : 2))) {
          const count = ['neg', 'abs', 'proj1', 'proj2'].includes(op) ? 1 : 2;
          const args = op === 'ofNat' ? expression.args.slice(1, 2) : expression.args.slice(-count);
          args.forEach((arg, i) => walk(arg, `${path}.value${i}`, exprDepth + 1, expressionScope, expressionObjects));
          return;
        }
        const relationBefore = relations.length;
        const args = visibleApplicationArguments(expression);
        const symbolId = object(expression.fn, currentScopeId, provenance(node.id, `${path}.function`));
        fragmentObjects.add(symbolId);
        const ports = [{ role: 'symbol', objectId: symbolId }, ...args.map((arg, i) => {
          const id = object(arg, currentScopeId, provenance(node.id, `${path}.argument${i}`));
          fragmentObjects.add(id);
          return { role: `argument ${i + 1}`, objectId: id };
        })];
        relations.push({ id: `relation:${node.id}:${stableHash(key)}:structural`, kind: 'predicate', label: formatExpression(expression.fn), ports, expression, scopeId: currentScopeId, nodeId: node.id, pluginId: 'structural', fidelity: 'structural', provenance: source, conditions: ['Application structure is preserved; the meaning of this definition has not been interpreted.'] });
        args.forEach((arg, i) => walk(arg, `${path}.argument${i}`, exprDepth + 1, expressionScope, expressionObjects));
        opaqueRegions.push({ id: `opaque:${node.id}:${stableHash(key)}`, nodeId: node.id, scopeId: currentScopeId, expression, label: formatExpression(expression), reason: 'No semantic rule interprets this application. Its typed objects, arguments, and recognized children remain available.', supportedRelationIds: relations.slice(relationBefore + 1).filter(r => r.fidelity !== 'structural').map(r => r.id), provenance: source });
      } else if (expression.kind === 'opaque' || expression.kind === 'const' && path === 'expression' && !['True', 'False'].includes(headName(expression) ?? '')) {
        opaqueRegions.push({ id: `opaque:${node.id}:${stableHash(key)}`, nodeId: node.id, scopeId: currentScopeId, expression, label: formatExpression(expression), reason: expression.kind === 'opaque' ? 'The prover exported this subexpression without an inspectable internal structure.' : 'This proposition is retained symbolically; no semantic rule interprets its definition.', supportedRelationIds: [], provenance: source });
      }
    };
    walk(node.expression, 'expression', 0);
    const fragmentRelations = relations.slice(relationStart);
    const fragmentOpaque = opaqueRegions.slice(opaqueStart);
    const meaningful = fragmentRelations.some(r => r.fidelity !== 'structural');
    coverage.push({ nodeId: node.id, status: fragmentOpaque.length ? meaningful ? 'partial' : 'structural' : meaningful || node.expression.kind === 'const' && ['True', 'False'].includes(headName(node.expression) ?? '') ? 'interpreted' : 'structural', relationIds: fragmentRelations.map(r => r.id), sceneIds: scenes.filter(s => s.nodeId === node.id).map(s => s.id), opaqueRegionIds: fragmentOpaque.map(r => r.id), objectIds: [...fragmentObjects] });
  };
  visitNode(analysis.tree, undefined, [], [], [], 0);
  return { schemaVersion: SEMANTIC_DOCUMENT_VERSION, prover: 'lean', source: analysis.source, tree: analysis.tree, objects: [...objects.values()], relations, scopes, choices, opaqueRegions, coverage, scenes, diagnostics };
}
