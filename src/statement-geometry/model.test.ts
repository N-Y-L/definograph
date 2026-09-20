import { describe, expect, it } from 'vitest';
import type { BallScene, Expr } from '../core';
import { literalSign, metricReading } from './model';
const radius: Expr = {kind:'var', id:'r', name:'ε', type:'ℝ'};
const zero: Expr = {kind:'literal', value:0};
const c: Expr = {kind:'var', id:'c', name:'c', type:'EuclideanSpace ℝ (Fin 2)'};
const base: BallScene = {id:'ball',nodeId:'clause',title:'Ball',kind:'ball',expression:radius,metric:'euclidean2',dimension:2,center:c,radius,boundary:'open',scope:[],guards:[],context:[]};
const positive: Expr = {kind:'app',fn:{kind:'const',name:'LT.lt'},args:[{kind:'const',name:'Real'},{kind:'const',name:'instLTReal'},zero,radius],standard:true,typeDescriptor:{kind:'proposition',lean:'Prop'}};
describe('symbolic metric reading',()=>{
  it('does not silently assume that a symbolic radius is positive',()=>{
    expect(metricReading(base)).toMatchObject({sign:undefined,zero:'empty'});
    expect(metricReading({...base,boundary:'closed'}).zero).toBe('singleton');
  });
  it('uses only a local positive-radius assumption',()=>{
    expect(metricReading({...base,guards:[positive]})).toMatchObject({sign:1,signFromAssumption:true});
    const or: Expr={kind:'app',fn:{kind:'const',name:'Or'},args:[positive,{kind:'const',name:'True'}]};
    expect(metricReading({...base,guards:[or]}).sign).toBeUndefined();
    expect(metricReading({...base,guards:[{...positive,standard:false}]}).sign).toBeUndefined();
  });
  it('does not reuse a similarly named radius or a partially applied comparison',()=>{
    expect(metricReading({...base,radius:{...radius,id:'different'},guards:[positive]}).sign).toBeUndefined();
    expect(metricReading({...base,guards:[{...positive,args:[zero,radius]}]}).sign).toBeUndefined();
  });
  it('handles zero and negative radius without numerical scenarios',()=>{
    expect(metricReading({...base,radius:zero})).toMatchObject({sign:0,zero:'empty'});
    expect(metricReading({...base,radius:{kind:'literal',value:-1}}).sign).toBe(-1);
    expect(metricReading({...base,boundary:'sphere',radius:zero})).toMatchObject({sign:0,zero:'singleton'});
    expect(literalSign({kind:'literal',value:'999999999999999999999999999999999999'})).toBe(1);
    expect(literalSign({kind:'literal',value:'0.00001'})).toBeUndefined();
  });
  it('preserves the actual metric and high dimensional distance condition',()=>{
    expect(metricReading(base).presentation).toBe('circle');
    expect(metricReading({...base,metric:'sup2'}).presentation).toBe('square');
    expect(metricReading({...base,metric:'euclideanN',dimension:21})).toMatchObject({presentation:'distance',dimension:21,relation:'<'});
    expect(metricReading({...base,metric:'real',dimension:1}).presentation).toBe('interval');
  });
});
