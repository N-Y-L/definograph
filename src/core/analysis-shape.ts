/** The structure the browser reader reads from a Lean analysis reply (`Analysis`), checked before anything is drawn.
 * It checks shape only (strings, lists, and the statement tree and expressions all the way down); it
 * says nothing about the mathematics, which the Lean worker checked. Optional fields are checked only
 * where present. Returns the first problem found, or undefined when the reply has the expected shape. */
export function analysisShapeIssue(value: unknown): string | undefined {
  if (!record(value)) return 'the reply is not an object';
  if (value.ok !== true) return 'ok is not true';
  for (const field of ['source', 'pretty'] as const) if (typeof value[field] !== 'string') return `${field} is not text`;
  if (!Array.isArray(value.diagnostics)) return 'diagnostics is not a list';
  if (value.validation !== undefined && typeof value.validation !== 'string') return 'validation is not text';
  for (const field of ['provenance', 'readableMath', 'definitionReadableMath'] as const) {
    if (value[field] !== undefined && !record(value[field])) return `${field} is not an object`;
  }
  const pending: Pending[] = [[{ segment: 'tree' }, 'node', value.tree], [{ segment: 'expression' }, 'expression', value.expression]];
  if (value.definitionTree != null) pending.push([{ segment: 'definitionTree' }, 'node', value.definitionTree]);
  if (value.definitionExpression != null) pending.push([{ segment: 'definitionExpression' }, 'expression', value.definitionExpression]);
  const listIssue = eachRecord(value, 'sourceTerms', (term, path) =>
    !Number.isSafeInteger(term.startByte) || !Number.isSafeInteger(term.endByte) ? `${path} has no byte range`
      : typeof term.lean !== 'string' || typeof term.type !== 'string' ? `${path} has no text` : undefined)
    ?? eachRecord(value, 'definitions', (definition, path) =>
      typeof definition.name !== 'string' || typeof definition.canExpand !== 'boolean' ? `${path} has no name or expansion flag` : undefined)
    ?? eachRecord(value, 'definitionPreviews', (preview, path) => {
      if (typeof preview.constant !== 'string' || typeof preview.pretty !== 'string') return `${path} has no constant or text`;
      pending.push([{ segment: `${path}.tree` }, 'node', preview.tree], [{ segment: `${path}.expression` }, 'expression', preview.expression]);
      return undefined;
    });
  if (listIssue) return listIssue;
  // An explicit stack, so a deep statement cannot exhaust the call stack.
  while (pending.length) {
    const [path, kind, item] = pending.pop()!;
    const issue = kind === 'node' ? nodeIssue(path, item, pending) : expressionIssue(path, item, pending);
    if (issue) return issue;
  }
  return undefined;
}

/** A field's path, kept as a chain and spelled out only when a problem is reported. */
interface Path { parent?: Path; segment: string }
type Pending = [path: Path, kind: 'node' | 'expression', value: unknown];
const at = (parent: Path, segment: string): Path => ({ parent, segment });
function spell(path: Path, field = ''): string {
  const segments = [field];
  for (let step: Path | undefined = path; step; step = step.parent) segments.push(step.segment);
  return segments.reverse().join('');
}
const record = (value: unknown): value is Record<string, unknown> => !!value && typeof value === 'object' && !Array.isArray(value);

function eachRecord(owner: Record<string, unknown>, field: string, check: (item: Record<string, unknown>, path: string) => string | undefined): string | undefined {
  const list = owner[field];
  if (list === undefined) return undefined;
  if (!Array.isArray(list)) return `${field} is not a list`;
  for (const [index, item] of list.entries()) {
    const path = `${field}[${index}]`;
    const issue = record(item) ? check(item, path) : `${path} is not an object`;
    if (issue) return issue;
  }
  return undefined;
}

function nodeIssue(path: Path, node: unknown, pending: Pending[]): string | undefined {
  if (!record(node)) return `${spell(path)} is not a statement node`;
  for (const field of ['id', 'kind', 'label', 'lean'] as const) if (typeof node[field] !== 'string') return `${spell(path, `.${field}`)} is not text`;
  if (!Array.isArray(node.children)) return `${spell(path, '.children')} is not a list`;
  if (node.binder !== undefined) {
    const binder = node.binder;
    if (!record(binder) || typeof binder.id !== 'string' || typeof binder.name !== 'string' || typeof binder.type !== 'string' || typeof binder.role !== 'string')
      return `${spell(path, '.binder')} has no id, name, type or role`;
    if (!Array.isArray(binder.dependsOn) || !binder.dependsOn.every(id => typeof id === 'string')) return `${spell(path, '.binder.dependsOn')} is not a list of names`;
    binderExpressions(at(path, '.binder'), binder, pending);
  }
  pending.push([at(path, '.expression'), 'expression', node.expression]);
  node.children.forEach((child, index) => pending.push([at(path, `.children[${index}]`), 'node', child]));
  return undefined;
}

function binderExpressions(path: Path, binder: Record<string, unknown>, pending: Pending[]): void {
  if (binder.typeExpression !== undefined) pending.push([at(path, '.typeExpression'), 'expression', binder.typeExpression]);
  if (record(binder.definition)) pending.push([at(path, '.definition.value'), 'expression', binder.definition.value]);
}

function expressionIssue(path: Path, expression: unknown, pending: Pending[]): string | undefined {
  if (!record(expression)) return `${spell(path)} is not an expression`;
  const text = (...fields: string[]) => fields.find(field => typeof expression[field] !== 'string');
  let missing: string | undefined;
  switch (expression.kind) {
    case 'const': case 'sort': missing = text('name'); break;
    case 'var': missing = text('id', 'name', 'type'); break;
    case 'opaque': missing = text('text'); break;
    // Lean writes a natural-number literal as a JSON number, which may be too large to be finite here.
    case 'literal': if (typeof expression.value !== 'string' && typeof expression.value !== 'number') missing = 'value'; break;
    case 'app':
      if (!Array.isArray(expression.args)) return `${spell(path, '.args')} is not a list`;
      pending.push([at(path, '.fn'), 'expression', expression.fn]);
      expression.args.forEach((argument, index) => pending.push([at(path, `.args[${index}]`), 'expression', argument]));
      break;
    case 'forall': case 'lambda': {
      const binder = expression.binder;
      if (!record(binder) || typeof binder.id !== 'string' || typeof binder.name !== 'string' || typeof binder.type !== 'string') return `${spell(path, '.binder')} has no id, name or type`;
      binderExpressions(at(path, '.binder'), binder, pending);
      if (expression.binderType !== undefined) pending.push([at(path, '.binderType'), 'expression', expression.binderType]);
      pending.push([at(path, '.body'), 'expression', expression.body]);
      break;
    }
    default: return `${spell(path, '.kind')} is not a known expression kind`;
  }
  return missing ? `${spell(path, `.${missing}`)} is missing` : undefined;
}
