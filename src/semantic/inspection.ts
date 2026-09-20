import type { Analysis, Expr, StatementNode } from '../core/types';
import { compileSemanticDocument } from './compiler';
import { compileInterpretationReport } from './coverage';

function treeSize(node: StatementNode, depth = 0): number {
  if (depth > 64) return 1001;
  return 1 + node.children.reduce((sum, child) => sum + treeSize(child, depth + 1), 0);
}
function hasOpaque(expression: Expr, depth = 0): boolean {
  if (depth > 80 || expression.kind === 'opaque') return true;
  if (expression.kind === 'app') return hasOpaque(expression.fn, depth + 1) || expression.args.some(arg => hasOpaque(arg, depth + 1));
  if (expression.kind === 'forall' || expression.kind === 'lambda') return hasOpaque(expression.body, depth + 1);
  return false;
}
function checkedExpansions(node: StatementNode, constant: string): number {
  if (node.expansion && (node.expansion.constant !== constant || node.expansion.definitionalEquality !== true)) return -1000;
  return (node.expansion ? 1 : 0) + node.children.reduce((sum, child) => sum + checkedExpansions(child, constant), 0);
}

/** Select only a small, kernel-checked preview of an initially unknown definition.
 * Previews are produced in the original elaboration context, never by replaying
 * editor commands. No additional fetch or host request is performed here. */
export function inspectSmallDefinitions(analysis: Analysis): Analysis {
  if (!analysis.definitionPreviews?.length || analysis.definitionTree) return analysis;
  const original = compileSemanticDocument(analysis);
  const report = compileInterpretationReport(original, analysis.definitions);
  const eligible = new Set(report.gaps.filter(gap => gap.canExpand && gap.constant).map(gap => gap.constant));
  if (!eligible.size) return analysis;
  const beforeSize = treeSize(analysis.tree);
  let best: Analysis | undefined, bestGain = 0;
  for (const preview of analysis.definitionPreviews.slice(0, 3)) {
    if (!eligible.has(preview.constant) || preview.expansionPolicy?.constants.length !== 1 || preview.expansionPolicy.constants[0] !== preview.constant || preview.expansionPolicy.maxDepth !== 1) continue;
    const size = treeSize(preview.tree);
    if (size > 80 || size > beforeSize + 24 || preview.tree.id !== analysis.tree.id || checkedExpansions(preview.tree, preview.constant) <= 0) continue;
    if (JSON.stringify(preview).length > 262_144) continue;
    const candidate: Analysis = { ...analysis, tree: preview.tree, expression: preview.expression, pretty: preview.pretty, originalExpression: analysis.expression, expansionPolicy: preview.expansionPolicy };
    const doc = compileSemanticDocument(candidate);
    if (doc.diagnostics.length || doc.opaqueRegions.some(region => hasOpaque(region.expression))) continue;
    const next = compileInterpretationReport(doc, analysis.definitions);
    // Favor an actual reduction in unknown meaning. New logical clauses alone
    // cannot hide a multiplication of uninterpreted predicates.
    const beforeUnknown = original.opaqueRegions.length, afterUnknown = doc.opaqueRegions.length;
    if (afterUnknown >= beforeUnknown || next.gaps.some(gap => gap.constant === preview.constant)) continue;
    const gain = (beforeUnknown - afterUnknown) * 4 + Math.min(8, next.clauses.interpreted - report.clauses.interpreted) - (size - beforeSize) / 12;
    if (gain > bestGain) {
      bestGain = gain;
      best = { ...candidate, automaticInspection: { constant: preview.constant, originalPretty: analysis.pretty,
        reason: 'Opening this small definition exposes more of the statement using the installed visual vocabulary. Lean checked the expansion for definitional equality.' } };
    }
  }
  return best ?? analysis;
}
