import { describe, expect, it } from 'vitest';
import type { Expr } from '../core/types';
import { graphBinderSemantics, graphSemanticPlugin } from './semantics';
const constant = (name: string, canonical = true): Expr => ({ kind: 'const', name, canonical });
const variable = (name: string): Expr => ({ kind: 'var', name, id: name, type: 'abstract' });
const app = (name: string, args: Expr[], argumentKinds: Extract<Expr,{kind:'app'}>['argumentKinds'], result: 'type'|'proposition'|'unknown' = 'proposition'): Extract<Expr,{kind:'app'}> => ({ kind:'app',fn:constant(name),args,argumentKinds,standard:true,typeDescriptor:{kind:result,lean:'typed fixture'} });
const V=variable('V'), W=variable('W'), G=variable('G'), H=variable('H'), C=variable('C'), c=variable('c'), u=variable('u'), v=variable('v');
const coloring = () => app('SimpleGraph.Coloring',[V,G,C],['type','value','type'],'type');
const hom = (name='SimpleGraph.Hom') => app(name,[V,W,G,H],['type','type','value','value'],'type');
function coerce(type: Expr, value=c): Extract<Expr,{kind:'app'}> { return app('DFunLike.coe',[type,V,constant('codomain family'),{kind:'opaque',text:'instance'},value,u],['type','type','value','instance','value','value'],'unknown'); }
describe('canonical graph grammar',()=>{
  it('preserves graph and endpoint identity, including repeated endpoints',()=>{
    const result=graphSemanticPlugin.match(app('SimpleGraph.Adj',[V,G,u,u],['type','value','value','value']));
    expect(result?.kind).toBe('graph-adjacency');
    expect(result?.arguments).toEqual([{role:'graph',expression:G},{role:'left vertex',expression:u},{role:'right vertex',expression:u}]);
  });
  it('colorability has a bound but never an invented coloring witness',()=>{
    const result=graphSemanticPlugin.match(app('SimpleGraph.Colorable',[V,G,{kind:'literal',value:0}],['type','value','value']));
    expect(result?.arguments.map(port=>port.role)).toEqual(['graph','color bound']);
    expect(result?.label).toContain('at most');
    expect(result?.conditions?.join(' ')).toContain('empty vertex type');
  });
  it('coloring type is interpreted only with an actual scoped value',()=>{
    expect(graphSemanticPlugin.match(coloring())).toBeUndefined();
    expect(graphBinderSemantics(c,coloring())?.arguments.map(port=>port.role)).toEqual(['graph','coloring','colors']);
    const result=graphSemanticPlugin.match(coerce(coloring()));
    expect(result?.arguments.map(port=>port.role)).toEqual(['graph','coloring','colors','vertex','color']);
    expect(result?.arguments.at(-1)?.expression).toEqual(coerce(coloring()));
  });
  it('distinguishes adjacency-preserving homomorphisms from induced embeddings',()=>{
    expect(graphBinderSemantics(c,hom())?.graphMapKind).toBe('homomorphism');
    const embedding=graphBinderSemantics(c,hom('SimpleGraph.Embedding'));
    expect(embedding?.graphMapKind).toBe('embedding');
    expect(embedding?.conditions?.join(' ')).toContain('exactly when');
    expect(graphSemanticPlugin.match(coerce(hom()))?.arguments.map(port=>port.role)).toEqual(['source graph','target graph','map','source vertex','target vertex']);
  });
  it('refuses partial, overapplied, wrongly classified, and unaudited constructors',()=>{
    const valid=app('SimpleGraph.Adj',[V,G,u,v],['type','value','value','value']);
    for(const invalid of [
      {...valid,args:valid.args.slice(0,3),argumentKinds:valid.argumentKinds?.slice(0,3)},
      {...valid,args:[...valid.args,v],argumentKinds:[...valid.argumentKinds!,'value']},
      {...valid,argumentKinds:['type','value','proof','value']},
      {...valid,typeDescriptor:{kind:'relation',lean:'V → Prop'}},
      {...valid,fn:constant('SimpleGraph.Adj',false)},
      {...valid,fn:{kind:'const',name:'SimpleGraph.Adj'}},
      {...valid,argumentKinds:undefined},
    ] as Expr[]) expect(graphSemanticPlugin.match(invalid)).toBeUndefined();
  });
  it('refuses custom coercions and partial color application while retaining bundle typing',()=>{
    const valid=coerce(coloring());
    for(const invalid of [{...valid,standard:false},{...valid,standard:undefined},{...valid,args:valid.args.slice(0,5),argumentKinds:valid.argumentKinds?.slice(0,5)},{...valid,fn:constant('DFunLike.coe',false)},{...valid,args:[{...coloring(),fn:constant('SimpleGraph.Coloring',false)},...valid.args.slice(1)]}] as Expr[]) expect(graphSemanticPlugin.match(invalid)).toBeUndefined();
    expect(graphBinderSemantics(c,coloring())?.kind).toBe('graph-coloring');
  });
  it('does not grant graph meaning to a generic relation hom or unsupported isomorphism',()=>{
    expect(graphBinderSemantics(c,hom('RelHom'))).toBeUndefined();
    expect(graphBinderSemantics(c,hom('SimpleGraph.Iso'))).toBeUndefined();
    expect(graphSemanticPlugin.match(coerce(hom('RelHom')))).toBeUndefined();
  });
  it('requires exact fully applied canonical type provenance for binder constraints',()=>{
    const type=coloring();
    for(const invalid of [{...type,fn:constant('SimpleGraph.Coloring',false)},{...type,args:type.args.slice(0,2),argumentKinds:type.argumentKinds?.slice(0,2)},{...type,typeDescriptor:{kind:'map',lean:'Type → Type'}}] as Expr[]) expect(graphBinderSemantics(c,invalid)).toBeUndefined();
  });
});
