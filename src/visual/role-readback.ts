/** The way back from framed figures to the role chains they were drawn under. A reading's root carries
 * data-role-root with its standing; a role frame carries data-role-frame, its role and its index, and prints its label
 * in a data-role-label element; a leaf carries data-role-leaf, its kind and its node, and prints at most one mark in a
 * data-role-mark element. A leaf's chain is the frames that enclose it inside its nearest root, outermost first, so a
 * reading nested in a figure starts a fresh chain. Every frame holds a leaf, and nothing of the same reading is framed
 * inside a leaf. Inside a data-role-surface, every figure must lie in a leaf.
 * Classes, attribute order, other text and styling carry no structure. skeleton-readback.ts is the pattern. */
export interface FigureRole {
  readonly nodeId: string;
  readonly leaf: string;
  /** A ⊢ mark was printed on the leaf. */
  readonly required: boolean;
  /** The leaf's mark as printed. */
  readonly mark?: string;
  readonly chain: readonly { readonly role: string; readonly index: number; readonly label: string }[];
  /** The standing of the reading the leaf belongs to, and how many readings enclose that one. */
  readonly standing: string;
  readonly depth: number;
}

interface Frame { role: string; index: number; label?: string; holdsLeaf?: true }
interface Leaf { nodeId: string; leaf: string; mark?: string; chain: Frame[]; standing: string; depth: number }
type Open = { tag: string; root?: { standing: string; depth: number }; surface?: true; frame?: Frame; leaf?: Leaf; capture?: (text: string) => void };

const entities: Record<string, string> = { '&amp;': '&', '&lt;': '<', '&gt;': '>', '&quot;': '"', '&#x27;': "'", '&#39;': "'", '&nbsp;': ' ' };
const decode = (text: string): string => text.replace(/&(?:amp|lt|gt|quot|#x27|#39|nbsp);/g, entity => entities[entity]!);
function attributes(source: string): Map<string, string> {
  const result = new Map<string, string>();
  for (const match of source.matchAll(/([^\s=/]+)(?:="([^"]*)")?/g)) result.set(match[1]!, decode(match[2] ?? ''));
  return result;
}
const voidElements = new Set(['area', 'base', 'br', 'col', 'embed', 'hr', 'img', 'input', 'link', 'meta', 'source', 'track', 'wbr']);
/** Elements that draw a figure, or a clause in place of one. */
const figureClasses = ['sr-inline-constraint', 'sr-symbolic-clause', 'structural-object', 'sr-binder-strip', 'ssg-clause'];
const isFigure = (tag: string, attrs: Map<string, string>): boolean => tag === 'figure' || (attrs.get('class') ?? '').split(/\s+/).some(name => figureClasses.includes(name));
const STANDINGS = new Set(['statement', 'expression', 'law', 'premise']);
function fail(message: string): never { throw new Error(message); }

/** Read every leaf in server-rendered markup, in document order. Throws when the markup is not well nested, when a
 * frame or leaf lies outside every root or inside a leaf of the same reading, when a frame holds no leaf, when a frame
 * prints no label or two, when a leaf prints two marks, or when a figure inside a surface lies outside every leaf. */
export function readFigureRoles(html: string): FigureRole[] {
  const open: Open[] = [], leaves: Leaf[] = [];
  const tags = /<(\/?)([a-zA-Z][\w-]*)((?:\s[^<>]*?)?)(\/?)>/g;
  let textFrom = 0, tag: RegExpExecArray | null;
  const nearest = <K extends keyof Open>(key: K, until?: keyof Open): Open | undefined => {
    for (let index = open.length - 1; index >= 0; index--) { if (open[index]![key]) return open[index]; if (until && open[index]![until]) return undefined; }
  };
  while ((tag = tags.exec(html))) {
    const [, closing, name, source, selfClosing] = tag;
    const text = decode(html.slice(textFrom, tag.index));
    if (text) open.forEach(entry => entry.capture?.(text));
    textFrom = tags.lastIndex;
    if (closing) {
      const closed = open.pop();
      if (closed?.tag !== name) fail(`Role markup is not well nested at </${name}>.`);
      if (closed.frame && !closed.frame.holdsLeaf) fail(`The ${closed.frame.role} frame holds no figure.`);
      continue;
    }
    const attrs = attributes(source!), entry: Open = { tag: name! };
    if (attrs.has('data-role-root')) {
      const standing = attrs.get('data-role-root')!;
      if (!STANDINGS.has(standing)) fail(`A reading root has no standing: "${standing}".`);
      entry.root = { standing, depth: open.filter(item => item.root).length };
    }
    if (attrs.has('data-role-surface')) entry.surface = true;
    if (attrs.has('data-role-frame') || attrs.has('data-role-leaf')) {
      const root = nearest('root')?.root ?? fail('A role frame or leaf is drawn outside every reading.');
      // A frame or leaf inside a leaf would put a figure under a role its own chain does not name.
      if (nearest('leaf', 'root')) fail('A role frame or leaf is drawn inside a leaf of the same reading.');
      if (attrs.has('data-role-frame')) entry.frame = { role: attrs.get('data-role') ?? fail('A role frame has no role.'), index: Number(attrs.get('data-role-index') ?? fail('A role frame has no index.')) };
      else {
        const chain: Frame[] = [];
        for (let index = open.length - 1; index >= 0 && !open[index]!.root; index--) {
          const frame = open[index]!.frame;
          if (frame) { frame.holdsLeaf = true; chain.unshift(frame); }
        }
        entry.leaf = { nodeId: attrs.get('data-role-node') ?? fail('A role leaf names no node.'), leaf: attrs.get('data-role-leaf')!, chain, ...root };
        leaves.push(entry.leaf);
      }
    }
    if (attrs.has('data-role-label')) {
      const frame = nearest('frame', 'leaf')?.frame ?? fail('A role label is printed outside every frame, or inside a leaf.');
      if (frame.label !== undefined) fail(`The ${frame.role} frame prints two labels.`);
      frame.label = '';
      entry.capture = text => { frame.label += text; };
    }
    if (attrs.has('data-role-mark')) {
      const leaf = nearest('leaf')?.leaf ?? fail('A role mark is printed outside every leaf.');
      if (leaf.mark !== undefined) fail(`The leaf of ${leaf.nodeId} prints two marks.`);
      leaf.mark = '';
      entry.capture = text => { leaf.mark += text; };
    }
    if (isFigure(name!, attrs) && nearest('surface', 'leaf')) fail(`A figure (${name}${attrs.get('class') ? ` ${attrs.get('class')}` : ''}) is drawn outside every role leaf.`);
    if (!selfClosing && !voidElements.has(name!)) open.push(entry);
    else if (entry.frame) fail(`The ${entry.frame.role} frame holds no figure.`);
  }
  if (open.length) fail('The role markup is incomplete.');
  return leaves.map(({ chain, mark, ...leaf }) => ({ ...leaf, ...(mark === undefined ? {} : { mark }), required: mark === '⊢',
    chain: chain.map(frame => ({ role: frame.role, index: frame.index, label: frame.label ?? fail(`The ${frame.role} frame prints no label.`) })) }));
}
