import { describe,it,expect } from 'vitest';
import { sourceTermAtRange } from './sourceTerms';
const term=(startByte:number,endByte:number,lean='ε')=>({startByte,endByte,lean,type:'ℝ',isBinder:false,origin:'lean-infotree' as const});
describe('Lean source selection coordinates',()=>{
  it('converts UTF8 offsets without confusing a Greek letter or astral character with UTF16 positions',()=>{
    const source='/- 🧭 -/ ε < 1';
    const start=new TextEncoder().encode('/- 🧭 -/ ').length;
    expect(sourceTermAtRange(source,[term(start,start+2)],9)?.sourceText).toBe('ε');
    expect(sourceTermAtRange(source,[term(start,start+2)],9)?.from).toBe(9);
  });
  it('selects the smallest typed occurrence covering the selection',()=>{
    expect(sourceTermAtRange('ε < 1',[term(0,6,'ε < 1'),term(0,2),term(5,6,'1')],4)?.lean).toBe('1');
    expect(sourceTermAtRange('ε < 1',[term(0,6,'ε < 1'),term(0,2)],0,4)?.lean).toBe('ε < 1');
  });
  it('rejects malformed byte boundaries and stale out-of-range selections',()=>{
    expect(sourceTermAtRange('ε',[term(1,2)],0)).toBeUndefined();
    expect(sourceTermAtRange('ε',[term(0,20)],0)).toBeUndefined();
    expect(sourceTermAtRange('ε',[term(0,2)],3)).toBeUndefined();
  });
});
