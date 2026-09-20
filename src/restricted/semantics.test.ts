import { describe, expect, it } from 'vitest';
import type { Expr } from '../core/types';
import { restrictedBinderSemantics, restrictedMapParts, restrictedSemanticPlugin } from './semantics';
const variable = (name: string): Expr => ({kind:'var',id:name,name,type:'abstract'});
const constant = (name: string, canonical = true): Expr => ({kind:'const',name,canonical});
const app = (name:string,args:Expr[],argumentKinds:Extract<Expr,{kind:'app'}>['argumentKinds'],result='unknown'):Extract<Expr,{kind:'app'}> => ({kind:'app',fn:constant(name),args,argumentKinds,typeDescriptor:{kind:result as 'unknown',lean:'typed fixture'},standard:false});
const X=variable('X'),Y=variable('Y'),e=variable('e'),x=variable('x'),y=variable('y'),tx=variable('topologyX'),ty=variable('topologyY');
const partial = () => app('PartialEquiv',[X,Y],['type','type'],'type');
const open = () => app('OpenPartialHomeomorph',[X,Y,tx,ty],['type','type','instance','instance'],'type');
const project = (side='source',value=e,A=X,B=Y) => app(`PartialEquiv.${side}`,[A,B,value],['type','type','value'],'set');
const apply = (value=e,input=x,A=X,B=Y) => app('PartialEquiv.toFun',[A,B,value,input],['type','type','value','value']);
const symm = (value=e,A=X,B=Y) => app('PartialEquiv.symm',[A,B,value],['type','type','value']);
const forget = (value=e) => app('OpenPartialHomeomorph.toPartialEquiv',[X,Y,tx,ty,value],['type','type','instance','instance','value']);
const openSymm = () => app('OpenPartialHomeomorph.symm',[X,Y,tx,ty,e],['type','type','instance','instance','value']);
describe('audited maps inverse on designated regions',()=>{
  it('introduces a bound partial equivalence without invented point or nonempty region',()=>{
    const result=restrictedBinderSemantics(e,partial());
    expect(result?.kind).toBe('restricted-equivalence');
    expect(result?.arguments).toEqual([{role:'map',expression:e},{role:'source carrier',expression:X},{role:'target carrier',expression:Y}]);
    expect(result?.conditions?.join(' ')).toContain('Neither region is assumed nonempty');
    expect(restrictedSemanticPlugin.match(partial())).toBeUndefined();
  });
  it('accepts arbitrary supplied topology instances while retaining openness and continuity limits',()=>{
    const result=restrictedBinderSemantics(e,open());
    expect(result?.restrictedMapKind).toBe('open-partial-homeomorphism');
    expect(result?.conditions?.join(' ')).toContain('supplied topologies');
    expect(result?.conditions?.join(' ')).toContain('Outside source and target');
  });
  it('preserves the exact source and target projection expressions',()=>{
    for(const side of ['source','target'] as const){const expression=project(side), result=restrictedSemanticPlugin.match(expression);expect(result?.restrictedRegion).toBe(side);expect(result?.arguments.at(-1)).toEqual({role:'region',expression});}
  });
  it('retains unrestricted actual application and does not infer its membership',()=>{
    const expression=apply(),result=restrictedSemanticPlugin.match(expression);
    expect(result?.restrictedDirection).toBe('forward');
    expect(result?.arguments.slice(-2)).toEqual([{role:'input',expression:x},{role:'output',expression}]);
    expect(result?.arguments.some(port=>port.role==='source member')).toBe(false);
  });
  it('normalizes inverse application to original map identity and original carrier order',()=>{
    const result=restrictedMapParts(apply(symm(),y,Y,X));
    expect(result).toMatchObject({map:e,sourceCarrier:X,targetCarrier:Y,direction:'inverse',input:y});
    expect(restrictedMapParts(project('source',symm(),Y,X))).toMatchObject({map:e,region:'target'});
    expect(restrictedMapParts(project('target',symm(),Y,X))).toMatchObject({map:e,region:'source'});
  });
  it('handles double symmetry and direct invFun without conflating application expressions',()=>{
    const double=symm(symm(),Y,X);
    expect(restrictedMapParts(apply(double))).toMatchObject({map:e,direction:'forward'});
    const inverse=app('PartialEquiv.invFun',[X,Y,e,y],['type','type','value','value']);
    expect(restrictedMapParts(inverse)).toMatchObject({map:e,direction:'inverse',input:y,output:inverse});
    expect(restrictedMapParts(app('PartialEquiv.invFun',[Y,X,symm(),x],['type','type','value','value']))?.direction).toBe('forward');
  });
  it('normalizes the exact forgetful projection and open-map symmetry',()=>{
    expect(restrictedMapParts(project('source',forget()))).toMatchObject({map:e,kind:'open-partial-homeomorphism',region:'source'});
    const inverse=app("OpenPartialHomeomorph.toFun'",[Y,X,ty,tx,openSymm(),y],['type','type','instance','instance','value','value']);
    expect(restrictedMapParts(inverse)).toMatchObject({map:e,sourceCarrier:X,targetCarrier:Y,kind:'open-partial-homeomorphism',direction:'inverse',input:y});
  });
  it('keeps unfamiliar map constructors intact rather than identifying their arguments',()=>{
    const unknown=app('User.wrap',[e],['value']);unknown.fn=constant('User.wrap',false);
    expect(restrictedMapParts(project('source',unknown))?.map).toBe(unknown);
    expect(restrictedMapParts(project('source',{...symm(),fn:constant('PartialEquiv.symm',false)}))?.direction).toBe('forward');
  });
  it('rejects missing canonical provenance, partial applications, extra arguments and wrong argument kinds',()=>{
    const valid=project();
    const invalid:Expr[]=[{...valid,fn:constant('PartialEquiv.source',false)},{...valid,fn:{kind:'const',name:'PartialEquiv.source'}},{...valid,args:valid.args.slice(0,2),argumentKinds:['type','type']},{...valid,args:[...valid.args,x],argumentKinds:['type','type','value','value']},{...valid,argumentKinds:['type','instance','value']},{...valid,argumentKinds:undefined},{...valid,typeDescriptor:{kind:'map',lean:'Set X → Set X'}}];
    for(const expression of invalid)expect(restrictedMapParts(expression)).toBeUndefined();
  });
  it('requires a fully applied canonical bundle type at binder introduction',()=>{
    for(const expression of [{...partial(),fn:constant('PartialEquiv',false)},{...partial(),args:[X],argumentKinds:['type']},{...open(),argumentKinds:['type','type','value','instance']},{...open(),typeDescriptor:{kind:'unknown',lean:'unknown'}}] as Expr[])expect(restrictedBinderSemantics(e,expression)).toBeUndefined();
  });
  it('never interprets a generic or custom CoeFun application as a stored map projection',()=>{
    expect(restrictedMapParts(app('CoeFun.coe',[partial(),constant('family'),variable('custom'),e,x],['type','value','instance','value','value']))).toBeUndefined();
    expect(restrictedMapParts(app('User.toFun',[X,Y,e,x],['type','type','value','value']))).toBeUndefined();
  });
  it('bounds symm normalization depth and refuses truncated projection chains',()=>{
    let value=e;for(let i=0;i<35;i++)value=symm(value,i%2?Y:X,i%2?X:Y);
    expect(restrictedMapParts(project('source',value))).toBeUndefined();
  });
});
