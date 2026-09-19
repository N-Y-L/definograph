import type { Analysis } from '../core/types';
type SourceTerm = NonNullable<Analysis['sourceTerms']>[number];
export interface TypedSourceSelection extends SourceTerm { from: number; to: number; sourceText: string }
/** Lean byte ranges must align to Unicode scalar boundaries, never split a UTF-8 sequence. */
export function sourceTermAtRange(source: string, terms: readonly SourceTerm[], from: number, to=from): TypedSourceSelection | undefined {
  if(!Number.isInteger(from)||!Number.isInteger(to)||from<0||to<from||to>source.length)return;
  const boundaries=new Map<number,number>([[0,0]]);let bytes=0,chars=0;
  const encoder=new TextEncoder();
  for(const character of source){bytes+=encoder.encode(character).length;chars+=character.length;boundaries.set(bytes,chars);}
  const candidates=terms.flatMap(term=>{
    const start=boundaries.get(term.startByte),end=boundaries.get(term.endByte);
    if(start===undefined||end===undefined||end<=start||start>from||end<to||(from===to&&from===end&&from!==source.length))return [];
    return [{...term,from:start,to:end,sourceText:source.slice(start,end)}];
  });
  return candidates.sort((a,b)=>(a.to-a.from)-(b.to-b.from)||Number(a.isBinder)-Number(b.isBinder))[0];
}
