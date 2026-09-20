import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import { analyzeEditorContext } from '../server/editor-context.ts';
import type { Analysis, StatementNode } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import { compileReading } from '../src/reading/index.ts';
import { compileGraphConstraint } from '../src/graphs/model.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
const rootDir=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const backend=createWorkerBackend({rootDir});
const config=JSON.parse(await readFile(path.join(rootDir,'.local/config.json'),'utf8'));
const temporary=await mkdtemp(path.join(os.tmpdir(),'statementlens-graph-test-'));
let checks=0;
const allNodes=(node:StatementNode):StatementNode[]=>[node,...node.children.flatMap(allNodes)];
function validate(analysis:Analysis):SemanticDocument {
  const doc=compileSemanticDocument(analysis); const reading=compileReading(doc);
  assert.equal(reading.nodes.length,allNodes(analysis.tree).length);
  for(const relation of doc.relations.filter(relation=>relation.pluginId==='graphs')) {
    assert.ok(doc.scopes.some(scope=>scope.id===relation.scopeId));
    assert.ok(relation.ports.every(port=>doc.objects.some(object=>object.id===port.objectId)));
    assert.ok(compileGraphConstraint(doc,relation),`No model for ${relation.kind}`);
  }
  return doc;
}
async function standalone(source:string):Promise<SemanticDocument>{const result=await backend.analyze(source);assert.equal(result.ok,true,JSON.stringify(result));checks++;return validate(result as unknown as Analysis);}
async function editor(prefix:string,term:string):Promise<{doc:SemanticDocument;analysis:Analysis}> {
  const fileName=path.join(temporary,'GraphFixture.lean');
  const source=prefix+'\n#check '+term+'\n';
  await writeFile(fileName,'-- The active buffer is supplied separately.\n');
  const lines=prefix.split('\n').length;
  const result=await analyzeEditorContext({engineDirectory:rootDir,fileName,source,selection:{start:{line:lines,character:7},end:{line:lines,character:7+term.length}},workspaceTrusted:true,libraryPaths:config.leanPath.filter((p:string)=>!p.includes('/leantex/'))});
  assert.equal(result.ok,true,JSON.stringify(result)); checks++;
  const analysis=result as unknown as Analysis;return{doc:validate(analysis),analysis};
}
const kind=(doc:SemanticDocument,name:string)=>doc.relations.filter(relation=>relation.kind===name);
try {
  await writeFile(path.join(temporary,'lean-toolchain'),'leanprover/lean4:v4.28.0\n');
  const basic='∀ (V C : Type) (G : SimpleGraph V) (c : G.Coloring C) (u v : V), G.Adj u v → c u ≠ c v';
  const colored=await standalone(basic);
  assert.equal(kind(colored,'graph-adjacency').length,1);
  assert.equal(kind(colored,'graph-coloring').length,3,'bound coloring plus its two applications');
  const application=kind(colored,'graph-coloring').find(relation=>relation.ports.some(port=>port.role==='vertex'))!;
  assert.ok(colored.scopes.find(scope=>scope.id===application.scopeId)?.assumptionNodeIds.length);
  const recolored=await standalone(basic.replace(/\bc\b/g,'paint').replace(/\bu\b/g,'left').replace(/\bv\b/g,'right'));
  assert.deepEqual(colored.relations.map(relation=>[relation.kind,relation.ports.map(port=>port.role)]),recolored.relations.map(relation=>[relation.kind,relation.ports.map(port=>port.role)]));
  const bound=await standalone('∀ (V : Type) (G : SimpleGraph V), G.Colorable 4');
  const boundModel=compileGraphConstraint(bound,kind(bound,'graph-colorable')[0]!)!;
  assert.equal(boundModel.palette?.count,'4');assert.equal(boundModel.coloring,undefined);
  const zero=await standalone('∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 0)), True');
  assert.equal(compileGraphConstraint(zero,kind(zero,'graph-coloring')[0]!)?.palette?.count,'0');
  const symbolic=await standalone('∀ (V : Type) (G : SimpleGraph V) (n : Nat), G.Colorable n');
  assert.equal(compileGraphConstraint(symbolic,kind(symbolic,'graph-colorable')[0]!)?.palette?.kind,'symbolic');
  const hom=await standalone('∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : SimpleGraph.Hom G H) (u : V), f u = f u');
  assert.equal(kind(hom,'graph-map').length,2);assert.ok(kind(hom,'graph-map').every(relation=>relation.graphMapKind==='homomorphism'));
  const embedding=await standalone('∀ (V W : Type) (G : SimpleGraph V) (H : SimpleGraph W) (f : SimpleGraph.Embedding G H) (u : V), f u = f u');
  assert.equal(kind(embedding,'graph-map').length,2);assert.ok(kind(embedding,'graph-map').every(relation=>relation.graphMapKind==='embedding'));
  const logic=await standalone('∀ (V : Type) (G : SimpleGraph V) (u v : V), ¬ G.Adj u v ∨ G.Adj u u');
  assert.equal(kind(logic,'graph-adjacency').length,2);
  assert.ok(logic.scopes.find(scope=>scope.id===kind(logic,'graph-adjacency')[0]!.scopeId)?.context.includes('Inside a negation'));
  assert.equal(compileGraphConstraint(logic,kind(logic,'graph-adjacency')[1]!)?.sameEndpoint,true);
  const partial=await standalone('∀ (V : Type) (G : SimpleGraph V) (u : V), Function.Injective (G.Adj u)');
  assert.equal(kind(partial,'graph-adjacency').length,0);
  const partialColorable=await standalone('∀ (V : Type) (G : SimpleGraph V) (P : (Nat → Prop) → Prop), P G.Colorable');
  assert.equal(kind(partialColorable,'graph-colorable').length,0);
  const partialColor=await standalone('∀ (V C : Type) (G : SimpleGraph V) (c : G.Coloring C) (P : (V → C) → Prop), P (c : V → C)');
  assert.equal(kind(partialColor,'graph-coloring').length,1);assert.ok(!kind(partialColor,'graph-coloring')[0]!.ports.some(port=>port.role==='vertex'));
  const scoped=await standalone('∀ (V C : Type) (G : SimpleGraph V), (∃ c : G.Coloring C, True) ∨ G.Colorable 4');
  const c=kind(scoped,'graph-coloring')[0]!, n=kind(scoped,'graph-colorable')[0]!;
  assert.notEqual(c.scopeId,n.scopeId);
  const binderPort=c.ports.find(port=>port.role==='coloring')!;
  assert.ok(!scoped.scopes.find(scope=>scope.id===n.scopeId)?.objectIds.includes(binderPort.objectId));
  const prefix='import Mathlib.Combinatorics.SimpleGraph.Coloring';
  const nativeEditor=await editor(prefix,'∀ (V : Type) (G : SimpleGraph V) (c : G.Coloring (Fin 4)) (u v : V), G.Adj u v → c u ≠ c v');
  assert.equal(kind(nativeEditor.doc,'graph-coloring').length,3);
  assert.equal(compileGraphConstraint(nativeEditor.doc,kind(nativeEditor.doc,'graph-coloring')[0]!)?.palette?.count,'4');
  const custom=await editor(prefix+'\ninstance (priority := 2000) {V C : Type} {G : SimpleGraph V} : FunLike (G.Coloring C) V C := RelHom.instFunLike',basic);
  assert.equal(kind(custom.doc,'graph-coloring').length,1,'a custom global coercion keeps bundle typing but not color application semantics');
  assert.ok(custom.doc.opaqueRegions.length>0);
  const fake=await editor('def SimpleGraph (V : Type) := V\ndef SimpleGraph.Adj {V : Type} (G : SimpleGraph V) (u v : V) : Prop := True\ndef SimpleGraph.Colorable {V : Type} (G : SimpleGraph V) (n : Nat) : Prop := True','∀ (V : Type) (G : SimpleGraph V) (u v : V), SimpleGraph.Adj G u v ∧ SimpleGraph.Colorable G 4');
  assert.equal(fake.doc.relations.filter(relation=>relation.pluginId==='graphs').length,0);
  assert.ok(fake.doc.opaqueRegions.length>0);
  console.log(`Graph integration: ${checks} real Lean/semantic/model cases passed.`);
} finally {backend.close?.();await rm(temporary,{recursive:true,force:true});}
