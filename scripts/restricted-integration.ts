import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { createWorkerBackend } from '../server/worker.ts';
import { analyzeEditorContext } from '../server/editor-context.ts';
import type { Analysis, StatementNode } from '../src/core/types.ts';
import { compileSemanticDocument } from '../src/semantic/index.ts';
import type { SemanticDocument } from '../src/semantic/types.ts';
const rootDir=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const backend=createWorkerBackend({rootDir});
const config=JSON.parse(await readFile(path.join(rootDir,'.local/config.json'),'utf8'));
const temporary=await mkdtemp(path.join(os.tmpdir(),'statementlens-restricted-test-'));
let checks=0;
const allNodes=(node:StatementNode):StatementNode[]=>[node,...node.children.flatMap(allNodes)];
const restricted=(doc:SemanticDocument)=>doc.relations.filter(relation=>relation.pluginId==='restricted-maps');
const kind=(doc:SemanticDocument,name:string)=>restricted(doc).filter(relation=>relation.kind===name);
function validate(analysis:Analysis):SemanticDocument {
  const doc=compileSemanticDocument(analysis);
  for(const relation of restricted(doc)) {
    assert.ok(doc.scopes.some(scope=>scope.id===relation.scopeId));
    assert.ok(relation.ports.every(port=>doc.objects.some(object=>object.id===port.objectId)));
  }
  return doc;
}
async function standalone(source:string):Promise<SemanticDocument>{const result=await backend.analyze(source);assert.equal(result.ok,true,JSON.stringify(result));checks++;return validate(result as unknown as Analysis);}
async function editor(prefix:string,term:string):Promise<{doc:SemanticDocument;analysis:Analysis}> {
  const fileName=path.join(temporary,'RestrictedFixture.lean');
  const source=prefix+'\n#check '+term+'\n';
  await writeFile(fileName,'-- The active buffer is supplied separately.\n');
  const lines=prefix.split('\n').length;
  const result=await analyzeEditorContext({engineDirectory:rootDir,fileName,source,selection:{start:{line:lines,character:7},end:{line:lines,character:7+term.length}},workspaceTrusted:true,libraryPaths:config.leanPath.filter((p:string)=>!p.includes('/leantex/'))});
  assert.equal(result.ok,true,JSON.stringify(result));checks++;
  const analysis=result as unknown as Analysis;return{doc:validate(analysis),analysis};
}
const prefix='import Mathlib.Topology.OpenPartialHomeomorph.Defs\nimport Mathlib.Combinatorics.SimpleGraph.Coloring';
const base='∀ (X Y : Type) (e : PartialEquiv X Y) (x : X), x ∈ e.source → e x ∈ e.target ∧ e.symm (e x) = x';
try {
  await writeFile(path.join(temporary,'lean-toolchain'),'leanprover/lean4:v4.28.0\n');
  const normal=await standalone(base);
  assert.equal(kind(normal,'restricted-equivalence').length,1);
  assert.equal(kind(normal,'restricted-region').length,2);
  assert.ok(kind(normal,'restricted-application').some(relation=>relation.restrictedDirection==='inverse'));
  const renamed=await standalone(base.replace(/\be\b/g,'chart').replace(/\bx\b/g,'point'));
  assert.deepEqual(restricted(renamed).map(r=>[r.kind,r.restrictedDirection,r.restrictedRegion,r.ports.map(p=>p.role)]),restricted(normal).map(r=>[r.kind,r.restrictedDirection,r.restrictedRegion,r.ports.map(p=>p.role)]));
  const unrestricted=await standalone('∀ (X Y : Type) (e : PartialEquiv X Y) (x : X), e.symm (e x) = x');
  assert.equal(kind(unrestricted,'restricted-region').length,0,'applications must not invent membership');
  assert.equal(kind(unrestricted,'restricted-application').length,2);
  const symmetric=await standalone('∀ (X Y : Type) (e : PartialEquiv X Y), e.symm.source = e.target ∧ e.symm.target = e.source');
  const mapIds=kind(symmetric,'restricted-region').map(r=>r.ports.find(p=>p.role==='map')!.objectId);
  assert.equal(new Set(mapIds).size,1);
  assert.deepEqual(kind(symmetric,'restricted-region').map(r=>r.restrictedRegion),['target','target','source','source']);
  const direct=await standalone('∀ (X Y : Type) (e : PartialEquiv X Y) (y : Y), e.invFun y = e.symm y');
  assert.ok(kind(direct,'restricted-application').every(r=>r.restrictedDirection==='inverse'));
  const doubled=await standalone('∀ (X Y : Type) (e : PartialEquiv X Y) (x : X), e.symm.symm x = e x');
  assert.ok(kind(doubled,'restricted-application').every(r=>r.restrictedDirection==='forward'));
  const open=await standalone('∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (e : OpenPartialHomeomorph X Y) (x : X), x ∈ e.source → e.symm (e x) = x');
  assert.ok(restricted(open).every(r=>r.restrictedMapKind==='open-partial-homeomorphism'));
  const nativeEditor=await editor(prefix,base);
  assert.deepEqual(restricted(nativeEditor.doc).map(r=>r.kind),restricted(normal).map(r=>r.kind));
  const partial=await standalone('∀ (X Y : Type) (e : PartialEquiv X Y) (P : (X → Y) → Prop), P e.toFun');
  assert.equal(kind(partial,'restricted-application').length,0);
  const fake=await editor('import Mathlib.Data.Set.Defs\nstructure PartialEquiv (X Y : Type) where\n  source : Set X','∀ (X Y : Type) (e : PartialEquiv X Y) (x : X), x ∈ e.source');
  assert.equal(restricted(fake.doc).length,0);
  const alias=await editor(prefix+'\nabbrev MyMap (X Y : Type) := PartialEquiv X Y','∀ (X Y : Type) (e : MyMap X Y), True');
  assert.equal(kind(alias.doc,'restricted-equivalence').length,1);
  const aliasBinder=allNodes(alias.analysis.tree).find(n=>n.binder?.name==='e')!.binder!;
  assert.equal(aliasBinder.type,'MyMap X Y');
  assert.equal(aliasBinder.typeExpansion?.definitionalEquality,true);
  assert.deepEqual(aliasBinder.typeExpansion?.constants,['MyMap']);
  const doubleAlias=await editor(prefix+'\nabbrev First (X Y : Type) := PartialEquiv X Y\nabbrev Second (X Y : Type) := First X Y','∀ (X Y : Type) (e : Second X Y), True');
  assert.equal(kind(doubleAlias.doc,'restricted-equivalence').length,1);
  assert.deepEqual(allNodes(doubleAlias.analysis.tree).find(n=>n.binder?.name==='e')?.binder?.typeExpansion?.constants,['Second','First']);
  const deep=await editor(prefix+'\nabbrev First (X Y : Type) := PartialEquiv X Y\nabbrev Second (X Y : Type) := First X Y\nabbrev Third (X Y : Type) := Second X Y','∀ (X Y : Type) (e : Third X Y), True');
  assert.equal(kind(deep.doc,'restricted-equivalence').length,0,'two-step exposure must not traverse a third alias');
  assert.equal(allNodes(deep.analysis.tree).find(n=>n.binder?.name==='e')?.binder?.typeExpansion?.constants.length,2);
  const openAlias=await editor(prefix+'\nabbrev Chart (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] := OpenPartialHomeomorph X Y','∀ (X Y : Type) [TopologicalSpace X] [TopologicalSpace Y] (e : Chart X Y), True');
  assert.equal(kind(openAlias.doc,'restricted-equivalence')[0]?.restrictedMapKind,'open-partial-homeomorphism');
  const graphAlias=await editor(prefix+'\nabbrev Paint {V : Type} (G : SimpleGraph V) (C : Type) := G.Coloring C','∀ (V C : Type) (G : SimpleGraph V) (c : Paint G C), True');
  assert.equal(graphAlias.doc.relations.filter(r=>r.kind==='graph-coloring').length,1);
  const functionAlias=await editor(prefix+'\nabbrev MapType (X Y : Type) := X → Y','∀ (X Y : Type) (f : MapType X Y), True');
  assert.equal(allNodes(functionAlias.analysis.tree).find(n=>n.binder?.name==='f')?.binder?.typeExpansion?.expression.kind,'forall');
  const opaque=await editor(prefix+'\nopaque Hidden (X Y : Type) : Type := PartialEquiv X Y','∀ (X Y : Type) (e : Hidden X Y), True');
  assert.equal(allNodes(opaque.analysis.tree).find(n=>n.binder?.name==='e')?.binder?.typeExpansion,undefined);
  const huge=await editor(prefix+'\ndef Huge := '+Array.from({length:50},()=>'(Nat × Nat)').join(' × '),'∀ (e : Huge), True');
  assert.equal(allNodes(huge.analysis.tree).find(n=>n.binder?.name==='e')?.binder?.typeExpansion,undefined);
  console.log(`Restricted-map integration: ${checks} real Lean and semantic cases passed.`);
} finally {backend.close?.();await rm(temporary,{recursive:true,force:true});}
