import { describe, expect, it } from 'vitest';
import { applicationFlow } from './application-flow';
import { expressionMapPath } from '../visual/StatementReadingView';
import type { SemanticRelation } from './types';
const relation = (kind: SemanticRelation['kind'], ports: Record<string,string>, extra: Partial<SemanticRelation> = {}): SemanticRelation => ({
  id: 'r', kind, label: kind, ports: Object.entries(ports).map(([role,objectId]) => ({role,objectId})),
  expression: {kind:'const',name:'fixture'}, scopeId:'scope:clause',nodeId:'clause',pluginId:'fixture',fidelity:'symbolic',
  provenance:{nodeId:'clause',expressionPath:'expression',origin:'elaborated-expression'},conditions:[],...extra,
});
describe('shared application composition',()=>{
  it('composes ordinary, graph, and inverse map stages in evaluation order',()=>{
    const first=relation('application',{function:'f','input 1':'x',output:'fx'});
    const second=relation('graph-map',{map:'g','source vertex':'fx','target vertex':'gfx'});
    const third=relation('restricted-application',{map:'e',input:'gfx',output:'inverse'},{restrictedDirection:'inverse'});
    expect(expressionMapPath('inverse',[third,first,second])).toMatchObject({inputs:['x'],maps:['f','g','e'],directions:['forward','forward','inverse'],output:'inverse',collapsed:false});
  });
  it('uses coloring application roles without treating a coloring introduction as an application',()=>{
    expect(applicationFlow(relation('graph-coloring',{graph:'G',coloring:'c',colors:'C'}))).toBeUndefined();
    expect(applicationFlow(relation('graph-coloring',{graph:'G',coloring:'c',colors:'C',vertex:'x',color:'cx'}))).toMatchObject({functionId:'c',inputIds:['x'],outputId:'cx'});
  });
  it('rejects incomplete, structural, duplicate, and out-of-order input contracts',()=>{
    expect(applicationFlow(relation('restricted-application',{map:'e',input:'x',output:'ex'}))).toBeUndefined();
    expect(applicationFlow(relation('application',{function:'f','input 2':'x',output:'fx'}))).toBeUndefined();
    const complete=relation('application',{function:'f','input 1':'x',output:'fx'});
    expect(applicationFlow({...complete,fidelity:'structural'})).toBeUndefined();
    expect(applicationFlow({...complete,ports:[...complete.ports,{role:'function',objectId:'other'}]})).toBeUndefined();
  });
  it('does not compose across clause or local-expression scopes',()=>{
    const outer=relation('restricted-application',{map:'e',input:'fx',output:'out'},{restrictedDirection:'inverse'});
    for(const extra of [{nodeId:'other'},{scopeId:'scope:lambda'}]){
      const inner=relation('application',{function:'f','input 1':'x',output:'fx'},extra);
      expect(expressionMapPath('out',[inner,outer])).toMatchObject({inputs:['fx'],maps:['e'],directions:['inverse']});
    }
  });
});
