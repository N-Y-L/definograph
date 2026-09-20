/** Unseen user definitions for generic reflection. None of these names belongs
 * in a semantic recognizer or a renderer dispatch table. */
export interface StructureFixture {
  id: string;
  title: string;
  source: string;
  selection: string;
  structureName: string;
  fields: readonly { name: string; kind: 'data' | 'law' }[];
  /** A named opaque proposition must remain visible in the reflected law. */
  opaqueLawHead?: string;
  /** The declared type name must survive bounded checked alias reduction. */
  declaredAlias?: string;
  /** A bounded prefix is acceptable only with an explicit omission count. */
  fieldCount?: number;
  compareRenameWith?: string;
  /** A structure beyond the type-head limit must not be invented. */
  reflectionMayBeUnavailable?: boolean;
  owners?: number;
  ownerRole?: 'assumption' | 'existential';
}

const corridorDeclaration = `import Mathlib.Data.Set.Basic
abbrev RegionOf (A : Type) := Set A
abbrev Messenger (A B : Type) := A → B
structure DriftWitness (X Y : Type) where
  carry : Messenger X Y
  recover : Y → X
  entrance : RegionOf X
  exit : Set Y
  tag : Nat
  intoExit : ∀ x, x ∈ entrance → carry x ∈ exit
  roundTrip : ∀ x, x ∈ entrance → recover (carry x) = x
`;
const corridorTerm = '∀ (X Y : Type) (bridge : DriftWitness X Y), True';
const algebraDeclaration = `structure FoldLaw where
  Carrier : Type
  combine : Carrier → Carrier → Carrier
  seed : Carrier
  neutral : ∀ x, combine seed x = x
  associate : ∀ x y z, combine (combine x y) z = combine x (combine y z)
`;
const algebraTerm = '∀ algebra : FoldLaw, True';
const opaqueDeclaration = `opaque QuietConstraint (A : Type) (x : A) : Prop := True
opaque HiddenCarrier : Type := Nat
structure SealRecord (A : Type) where
  chosen : A
  unexplained : HiddenCarrier
  certified : QuietConstraint A chosen
`;
const opaqueTerm = '∀ (A : Type) (packet : SealRecord A), True';
const width = 23;
const wideDeclaration = `structure WidePacket where\n${Array.from({ length: width }, (_, i) => `  entry${i} : Nat`).join('\n')}\n`;
const deepDeclaration = `structure RootPacket where\n  value : Nat\n${Array.from({ length: 12 }, (_, i) => `abbrev AliasLayer${i} := ${i ? `AliasLayer${i - 1}` : 'RootPacket'}`).join('\n')}\n`;
const recursiveDeclaration = `inductive BranchingRecord where
  | leaf : Nat → BranchingRecord
  | fork : BranchingRecord → BranchingRecord → BranchingRecord
`;
const renamedFields: Record<string, string> = { DriftWitness: 'SilentTransport', RegionOf: 'PatchType', Messenger: 'RelayType', carry: 'advance', recover: 'retreat', entrance: 'origin', exit: 'arrival', tag: 'label', intoExit: 'arrives', roundTrip: 'undo' };
const renamedCorridor = corridorDeclaration.replace(/\b(DriftWitness|RegionOf|Messenger|carry|recover|entrance|exit|tag|intoExit|roundTrip)\b/g, value => renamedFields[value]!);
const renamedTerm = '∀ (X Y : Type) (bridge : SilentTransport X Y), True';

export const structureFixtures: readonly StructureFixture[] = [
  { id: 'unseen-restricted-record', title: 'Unseen record with arbitrary map, region, and law names', source: `${corridorDeclaration}#check ${corridorTerm}\n`, selection: corridorTerm, structureName: 'DriftWitness',
    fields: [{ name: 'carry', kind: 'data' }, { name: 'recover', kind: 'data' }, { name: 'entrance', kind: 'data' }, { name: 'exit', kind: 'data' }, { name: 'tag', kind: 'data' }, { name: 'intoExit', kind: 'law' }, { name: 'roundTrip', kind: 'law' }] },
  { id: 'renamed-unseen-record', title: 'Renamed unknown record and fields retain the same primitive structure', source: `${renamedCorridor}#check ${renamedTerm}\n`, selection: renamedTerm, structureName: 'SilentTransport', compareRenameWith: 'unseen-restricted-record',
    fields: [{ name: 'advance', kind: 'data' }, { name: 'retreat', kind: 'data' }, { name: 'origin', kind: 'data' }, { name: 'arrival', kind: 'data' }, { name: 'label', kind: 'data' }, { name: 'arrives', kind: 'law' }, { name: 'undo', kind: 'law' }] },
  { id: 'unseen-algebra-record', title: 'An internal carrier, binary operation, element, and laws', source: `${algebraDeclaration}#check ${algebraTerm}\n`, selection: algebraTerm, structureName: 'FoldLaw',
    fields: [{ name: 'Carrier', kind: 'data' }, { name: 'combine', kind: 'data' }, { name: 'seed', kind: 'data' }, { name: 'neutral', kind: 'law' }, { name: 'associate', kind: 'law' }] },
  { id: 'unseen-opaque-law', title: 'An opaque property is retained as a field law', source: `${opaqueDeclaration}#check ${opaqueTerm}\n`, selection: opaqueTerm, structureName: 'SealRecord', opaqueLawHead: 'QuietConstraint',
    fields: [{ name: 'chosen', kind: 'data' }, { name: 'unexplained', kind: 'data' }, { name: 'certified', kind: 'law' }] },
  { id: 'unseen-aliased-record', title: 'A fresh user alias reaches generic reflection', source: `${corridorDeclaration}abbrev LocalPassage (X Y : Type) := DriftWitness X Y\n#check ∀ (X Y : Type) (route : LocalPassage X Y), True\n`, selection: '∀ (X Y : Type) (route : LocalPassage X Y), True', structureName: 'DriftWitness', declaredAlias: 'LocalPassage',
    fields: [{ name: 'carry', kind: 'data' }, { name: 'recover', kind: 'data' }, { name: 'entrance', kind: 'data' }, { name: 'exit', kind: 'data' }, { name: 'tag', kind: 'data' }, { name: 'intoExit', kind: 'law' }, { name: 'roundTrip', kind: 'law' }] },
  { id: 'wide-user-record', title: 'Wide structures report their bounded field prefix', source: `${wideDeclaration}#check ∀ packet : WidePacket, True\n`, selection: '∀ packet : WidePacket, True', structureName: 'WidePacket', fields: [], fieldCount: width },
  { id: 'deep-user-alias', title: 'Deep type aliases terminate at the declared bound', source: `${deepDeclaration}#check ∀ packet : AliasLayer11, True\n`, selection: '∀ packet : AliasLayer11, True', structureName: 'RootPacket', declaredAlias: 'AliasLayer11', fields: [], reflectionMayBeUnavailable: true },
  { id: 'recursive-user-type', title: 'A recursive inductive type stays finite and explicit', source: `${recursiveDeclaration}#check ∀ branch : BranchingRecord, True\n`, selection: '∀ branch : BranchingRecord, True', structureName: 'BranchingRecord', fields: [], reflectionMayBeUnavailable: true },
  { id: 'law-only-record', title: 'A proposition record contributes laws only under its hypothesis', source: 'structure MirrorLaw (A : Type) (f : A → A) : Prop where\n  twice : ∀ x, f (f x) = x\n#check ∀ (A : Type) (f : A → A) (h : MirrorLaw A f), True\n', selection: '∀ (A : Type) (f : A → A) (h : MirrorLaw A f), True', structureName: 'MirrorLaw', fields: [{ name: 'twice', kind: 'law' }], ownerRole: 'assumption' },
  { id: 'separate-record-witnesses', title: 'Same-named record witnesses retain separate negated alternatives', source: `${corridorDeclaration}#check ∀ (X Y : Type), ¬ ((∃ bridge : DriftWitness X Y, True) ∨ (∃ bridge : DriftWitness X Y, True))\n`, selection: '∀ (X Y : Type), ¬ ((∃ bridge : DriftWitness X Y, True) ∨ (∃ bridge : DriftWitness X Y, True))', structureName: 'DriftWitness', owners: 2, ownerRole: 'existential',
    fields: [{ name: 'carry', kind: 'data' }, { name: 'recover', kind: 'data' }, { name: 'entrance', kind: 'data' }, { name: 'exit', kind: 'data' }, { name: 'tag', kind: 'data' }, { name: 'intoExit', kind: 'law' }, { name: 'roundTrip', kind: 'law' }] },
];
