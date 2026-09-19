import { useEffect, useRef } from 'react';
import { basicSetup } from 'codemirror';
import { EditorState } from '@codemirror/state';
import { EditorView, keymap } from '@codemirror/view';
import { StreamLanguage, syntaxHighlighting, HighlightStyle } from '@codemirror/language';
import { tags } from '@lezer/highlight';

// Highlighting is deliberately lexical. The native Lean worker is the parser/type checker.
const lean = StreamLanguage.define<{comment: number}>({
  startState: () => ({ comment: 0 }),
  token(stream, state) {
    if (state.comment) {
      while (!stream.eol()) {
        if (stream.match('/-')) state.comment++;
        else if (stream.match('-/')) { if (--state.comment === 0) break; }
        else stream.next();
      }
      return 'comment';
    }
    if (stream.eatSpace()) return null;
    if (stream.match('--')) { stream.skipToEnd(); return 'comment'; }
    if (stream.match('/-')) { state.comment = 1; return 'comment'; }
    if (stream.match(/^(∀|∃|→|↔|∧|∨|¬|fun\b|forall\b|exists\b|let\b|in\b|if\b|then\b|else\b)/)) return 'keyword';
    if (stream.match(/^(ℝ|ℕ|ℤ|ℚ|Prop\b|Type\b|Sort\b)/)) return 'typeName';
    if (stream.match(/^\d+(\.\d+)?/)) return 'number';
    if (stream.match(/^[A-Z][\w.']*/)) return 'typeName';
    if (stream.match(/^[\p{L}_][\p{L}\p{N}_'.]*/u)) return 'variableName';
    if (stream.match(/^[∈∉⊆⊂≤≥≠=<>+*/^∘∩∪-]/)) return 'operator';
    stream.next(); return null;
  },
});
const style = HighlightStyle.define([
  { tag: tags.keyword, color: '#8463aa' },
  { tag: tags.typeName, color: '#247d84' },
  { tag: tags.variableName, color: '#324967' },
  { tag: tags.operator, color: '#5378a6' },
  { tag: tags.number, color: '#a46e35' },
  { tag: tags.comment, color: '#8490a0', fontStyle: 'italic' },
]);
const abbreviations: Record<string, string> = {
  forall:'∀', exists:'∃', R:'ℝ', N:'ℕ', Z:'ℤ', Q:'ℚ', in:'∈', notin:'∉',
  to:'→', iff:'↔', and:'∧', or:'∨', not:'¬', le:'≤', ge:'≥', ne:'≠',
  epsilon:'ε', eps:'ε', delta:'δ', alpha:'α', beta:'β', gamma:'γ',
  subset:'⊆', inter:'∩', union:'∪', circ:'∘', times:'×',
};
export function LeanEditor({value, onChange, onAnalyze, onSelection, editorRef}: {
  value: string; onChange: (value: string) => void; onAnalyze: () => void;
  onSelection?: (from:number,to:number)=>void;
  editorRef: { current: EditorView | null };
}) {
  const host = useRef<HTMLDivElement>(null);
  const callbacks = useRef({onChange,onAnalyze,onSelection}); callbacks.current = {onChange,onAnalyze,onSelection};
  useEffect(() => {
    const view = new EditorView({parent:host.current!, state:EditorState.create({doc:value, extensions:[
      basicSetup, lean, syntaxHighlighting(style), EditorView.lineWrapping,
      EditorView.contentAttributes.of({'aria-label':'Lean statement editor', spellcheck:'false'}),
      keymap.of([
        {key:'Mod-Enter', run:() => { callbacks.current.onAnalyze(); return true; }},
        {key:'Tab', run:view => {
          const cursor = view.state.selection.main;
          if (!cursor.empty) return false;
          const prefix = view.state.doc.sliceString(Math.max(0,cursor.head-24),cursor.head);
          const match = /\\([A-Za-z]+)$/.exec(prefix);
          if (!match || !abbreviations[match[1]]) return false;
          const insert = abbreviations[match[1]];
          view.dispatch({changes:{from:cursor.head-match[0].length,to:cursor.head,insert},selection:{anchor:cursor.head-match[0].length+insert.length}});
          return true;
        }},
      ]),
      EditorView.updateListener.of(update => {if (update.docChanged) callbacks.current.onChange(update.state.doc.toString()); if(update.selectionSet){const s=update.state.selection.main;callbacks.current.onSelection?.(s.from,s.to);}}),
      EditorView.theme({
        '&':{fontSize:'12px',background:'#fbfcfe',color:'#324967'},
        '.cm-content':{fontFamily:'"SFMono-Regular",Consolas,monospace',padding:'16px 0',minHeight:'200px',lineHeight:'1.85'},
        '.cm-scroller':{overflow:'auto',maxHeight:'390px'},
        '.cm-gutters':{background:'#f5f7fa',color:'#a4afbc',border:'none',fontSize:'10px'},
        '.cm-lineNumbers .cm-gutterElement':{padding:'0 7px'},
        '.cm-activeLine,.cm-activeLineGutter':{background:'#eaf1f966'},
        '&.cm-focused':{outline:'none'},
        '.cm-cursor':{borderLeftColor:'#366fac'},
      }),
    ]})});
    editorRef.current=view;
    return () => {view.destroy();editorRef.current=null;};
  }, []);
  useEffect(() => { const view=editorRef.current; if(view && view.state.doc.toString()!==value) view.dispatch({changes:{from:0,to:view.state.doc.length,insert:value}}); },[value]);
  return <div className="lean-editor" ref={host}/>;
}
