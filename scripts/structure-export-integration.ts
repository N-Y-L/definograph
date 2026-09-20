/** Native reflection boundaries independent of the presentation layer. */
import assert from 'node:assert/strict';
import { mkdtemp, readFile, rm, writeFile } from 'node:fs/promises';
import os from 'node:os';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { analyzeEditorContext } from '../server/editor-context.ts';
import { runBoundedProcess } from '../server/worker.ts';
import type { Analysis, StatementNode } from '../src/core/types.ts';
const rootDir=path.resolve(path.dirname(fileURLToPath(import.meta.url)),'..');
const config=JSON.parse(await readFile(path.join(rootDir,'.local/config.json'),'utf8'));
const temporary=await mkdtemp(path.join(os.tmpdir(),'statementlens-structure-export-'));
let checks=0;
const nodes=(node:StatementNode):StatementNode[]=>[node,...node.children.flatMap(nodes)];
async function context(prefix:string,term:string):Promise<Analysis>{
  const fileName=path.join(temporary,'Record.lean'), source=prefix+'\n#check '+term+'\n', line=prefix.split('\n').length;
  await writeFile(fileName,'-- saved source is deliberately different\n');
  const result=await analyzeEditorContext({engineDirectory:rootDir,fileName,source,selection:{start:{line,character:7},end:{line,character:7+term.length}},workspaceTrusted:true,libraryPaths:config.leanPath.filter((p:string)=>!p.includes('/leantex/'))});
  assert.equal(result.ok,true,JSON.stringify(result));
  assert.equal(await readFile(fileName,'utf8'),'-- saved source is deliberately different\n');
  checks++;return result as unknown as Analysis;
}
try{
  await writeFile(path.join(temporary,'lean-toolchain'),'leanprover/lean4:v4.28.0\n');
  const nested=await context('structure PointData where\n  val : Nat\nstructure NestedLaw : Type where\n  law : ∀ p : PointData, p.val = p.val','∀ r : NestedLaw, True');
  const nestedRecord=nodes(nested.tree).find(n=>n.binder?.name==='r')!.binder!.structure!;
  assert.ok(nestedRecord?.kernelChecked);
  const nestedLaw=nestedRecord.fields[0]!.law!;
  assert.equal(nodes(nestedLaw).find(n=>n.binder?.name==='p')?.binder?.structure,undefined,'law trees must not recursively reflect newly introduced structures');
  const proposition=await context('structure OnlyLaw where\n  law : True','∀ h : OnlyLaw, True');
  const hypothesis=nodes(proposition.tree).find(n=>n.binder?.name==='h')!.binder!;
  assert.equal(hypothesis.role,'assumption');assert.equal(hypothesis.structure?.fields[0]?.kind,'law');
  const parent=await context('structure ParentData where\n  value : Nat\nstructure ChildData extends ParentData where\n  extra : Nat','∀ c : ChildData, True');
  const parentRecord=nodes(parent.tree).find(n=>n.binder?.name==='c')!.binder!.structure!;
  assert.deepEqual(parentRecord.fields.map(f=>f.name),['toParentData','extra']);
  assert.equal(parentRecord.fields[0]!.parent,'ParentData');
  const broken=await context('structure BrokenField where\n  value : (sorry : Type)','∀ b : BrokenField, True');
  const brokenRecord=nodes(broken.tree).find(n=>n.binder?.name==='b')!.binder!.structure!;
  assert.ok(brokenRecord);assert.equal(brokenRecord.fields.length,0);assert.equal(brokenRecord.omittedFields,1);assert.ok(brokenRecord.stopReason);
  const deep=await context('structure FinalRecord where\n  data : Nat\nabbrev AliasOne := FinalRecord\nabbrev AliasTwo := AliasOne\nabbrev AliasThree := AliasTwo','∀ x : AliasThree, True');
  const stopped=nodes(deep.tree).find(n=>n.binder?.name==='x')!.binder!;
  assert.equal(stopped.type,'AliasThree');assert.equal(stopped.structure,undefined);assert.match(stopped.structureOmission??'',/two checked definition steps/);
  const opaque=await context('opaque SecretType : Type := Nat','∀ s : SecretType, True');
  assert.equal(nodes(opaque.tree).find(n=>n.binder?.name==='s')?.binder?.structure,undefined);
  const counter=path.join(temporary,'counter');
  await writeFile(counter,'');
  const once=await context(`import Lean\n#eval do IO.FS.writeFile ${JSON.stringify(counter)} ((← IO.FS.readFile ${JSON.stringify(counter)}) ++ ".")\nstructure SinglePass where\n  data : Nat\n  law : data = data`,'∀ s : SinglePass, True');
  assert.ok(nodes(once.tree).find(n=>n.binder?.name==='s')?.binder?.structure);
  assert.equal(await readFile(counter,'utf8'),'.','reflection must reuse the original elaboration, never replay #eval');
  const boundsFile=path.join(temporary,'Bounds.lean');
  await writeFile(boundsFile,`import StatementLens.Response\nopen Lean\ndef main : IO Unit := do\n  let source := String.ofList (List.replicate 10000 'a')\n  let extra := String.ofList (List.replicate 20000 'b')\n  let binder := Json.mkObj [("id", toJson "owned"), ("name", toJson "x"), ("structure", Json.mkObj [("fields", toJson extra)])]\n  let original := Json.mkObj [("ok", toJson true), ("source", toJson source), ("tree", Json.mkObj [("binder", binder)]), ("expression", Json.mkObj [("binder", binder)])]\n  let result := StatementLens.Response.serializeResponse original 12000\n  unless result.utf8ByteSize <= 12000 do throw (IO.userError "optional structure broke the output cap")\n  let parsed ← IO.ofExcept (Json.parse result)\n  unless (parsed.getObjValAs? String "source").toOption == some source do throw (IO.userError "mandatory source was modified")\n  let tree ← IO.ofExcept (parsed.getObjVal? "tree")\n  let b ← IO.ofExcept (tree.getObjVal? "binder")\n  if (b.getObjVal? "structure").isOk then throw (IO.userError "oversized structure was retained")\n  unless (b.getObjValAs? String "structureOmission").isOk do throw (IO.userError "omission was not reported")\n  IO.println "structure bounds passed"\n`);
  const output=await runBoundedProcess(config.leanExecutable,{args:['--run',boundsFile],cwd:temporary,env:{...process.env,LEAN_PATH:config.leanPath.join(path.delimiter)},timeoutMs:10000});
  assert.match(output,/structure bounds passed/);checks++;
  console.log(`Generic structure export: ${checks} native isolation and bounds checks passed.`);
}finally{await rm(temporary,{recursive:true,force:true});}
