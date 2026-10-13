/** The way back from the drawn skeleton to the tree it was drawn from. A row is an element carrying
 * data-skeleton-row; its kind and source nodes are attributes; a row is a child of the nearest enclosing row, through
 * the nearest data-skeleton-edge in between; a folded row carries the number of rows it stands for. The role mark and
 * the binder names a row prints are read as its labels. Classes, order of attributes, other text and styling carry
 * no structure. */
export interface SkeletonRow {
  readonly id: string;
  readonly kind: string;
  readonly nodeIds: readonly string[];
  /** Present on a binder row: forall, exists, parameter, definition or auxiliary. */
  readonly binder?: string;
  /** The role mark drawn on a binder or connective row, as printed. */
  readonly mark?: string;
  /** The drawn binder names, in order. */
  readonly names: readonly string[];
  /** Present on a stub: how many rows it stands for, itself included. */
  readonly folded?: number;
  readonly children: readonly { readonly edge: string; readonly row: SkeletonRow }[];
}
interface DraftRow extends SkeletonRow { mark?: string; readonly names: string[]; readonly children: { edge: string; row: SkeletonRow }[] }

const entities: Record<string, string> = { '&amp;': '&', '&lt;': '<', '&gt;': '>', '&quot;': '"', '&#x27;': "'" };
const decode = (text: string): string => text.replace(/&(?:amp|lt|gt|quot|#x27);/g, entity => entities[entity]!);
function attributes(source: string): Map<string, string> {
  const result = new Map<string, string>();
  for (const match of source.matchAll(/([^\s=]+)(?:="([^"]*)")?/g)) result.set(match[1]!, decode(match[2] ?? ''));
  return result;
}

/** Read the first skeleton in server-rendered markup. Throws when the markup holds none or is not well nested. */
export function readSkeleton(html: string): SkeletonRow {
  const start = html.indexOf('<section class="statement-skeleton"');
  if (start < 0) throw new Error('The markup holds no statement skeleton.');
  const open: { tag: string; edge?: string; row?: DraftRow }[] = [];
  const tags = /<(\/?)([a-zA-Z][\w-]*)((?:\s[^<>]*?)?)(\/?)>/g;
  tags.lastIndex = start;
  let root: DraftRow | undefined, label: ((text: string) => void) | undefined, textFrom = start, tag: RegExpExecArray | null;
  while ((tag = tags.exec(html))) {
    const [, closing, name, source, selfClosing] = tag;
    if (label) { label(decode(html.slice(textFrom, tag.index))); label = undefined; }
    textFrom = tags.lastIndex;
    if (closing) {
      if (open.pop()?.tag !== name) throw new Error(`Skeleton markup is not well nested at </${name}>.`);
      if (!open.length) return root ?? fail('The skeleton holds no row.');
      continue;
    }
    const attrs = attributes(source!);
    let parent: DraftRow | undefined, edge: string | undefined;
    for (let index = open.length - 1; index >= 0 && !parent; index--) { parent = open[index]!.row; if (!parent) edge ??= open[index]!.edge; }
    let row: DraftRow | undefined;
    if (attrs.has('data-skeleton-row')) {
      row = { id: attrs.get('data-skeleton-row')!, kind: attrs.get('data-skeleton-kind') ?? '', nodeIds: (attrs.get('data-skeleton-nodes') ?? '').split(' ').filter(Boolean), names: [], children: [],
        ...(attrs.has('data-skeleton-binder') ? { binder: attrs.get('data-skeleton-binder') } : {}), ...(attrs.has('data-skeleton-folded') ? { folded: Number(attrs.get('data-skeleton-folded')) } : {}) };
      if (parent) parent.children.push({ edge: edge ?? attrs.get('data-skeleton-edge') ?? fail(`Row ${row.id} is drawn inside ${parent.id} without an edge.`), row });
      else if (root) fail('The skeleton has more than one outermost row.');
      else root = row;
    }
    if (attrs.has('data-skeleton-name')) { const named = parent ?? fail('A binder name is drawn outside every row.'); label = text => named.names.push(text); }
    if (attrs.has('data-skeleton-mark')) { const marked = parent ?? fail('A role mark is drawn outside every row.'); label = text => { marked.mark = text; }; }
    if (!selfClosing) open.push({ tag: name!, edge: attrs.get('data-skeleton-edge'), row });
  }
  return fail('The skeleton markup is incomplete.');
}
function fail(message: string): never { throw new Error(message); }
