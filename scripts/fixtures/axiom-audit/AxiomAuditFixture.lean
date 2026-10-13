/-!
Negative control for `scripts/axiom-audit.mjs`. The audit must reject this module, and must name
each planted declaration under the rule given beside it. Nothing imports this file.
-/
namespace AxiomAuditFixture

-- Accepted: no axiom, and not named by any rule.
theorem clean : 1 + 1 = 2 := rfl

-- Accepted: a certificate recorded with no axioms that uses none.
theorem cleanCertificate (n : Nat) : n = n := rfl

-- forbidden-axiom (sorryAx): a proof left as a placeholder.
theorem plantedSorry : 2 + 2 = 5 := sorry

-- forbidden-axiom (sorryAx): clean text, resting on the lemma above.
theorem dependsOnPlantedSorry : 2 + 2 = 5 := plantedSorry

-- forbidden-axiom (sorryAx): a definition, not a theorem.
def plantedSorryDefinition : Nat := sorry

-- forbidden-axiom (Lean.ofReduceBool, Lean.trustCompiler): the compiler is trusted, not the kernel.
theorem plantedNativeDecide : 2 ^ 10 = 1024 := by native_decide

-- unlisted-ratcheted-axiom: the proof adds Classical.choice and no exception lists it.
theorem plantedChoice (p : Prop) : p ∨ ¬p := Classical.em p

-- exception-kind: listed as entering through the statement; it enters through the proof.
theorem plantedChoiceListedAsStatement (p : Prop) : ¬¬p → p := Classical.byContradiction

-- certificate-axioms: recorded with no axioms, but the proof uses propext.
theorem regressedCertificate (p q : Prop) (h : p ↔ q) : p = q := propext h

-- declared-axiom: an audited module may not declare one.
axiom plantedAxiom : ∀ n : Nat, n + 0 = n

-- forbidden-axiom (AxiomAuditFixture.plantedAxiom): use of an axiom outside the policy.
theorem dependsOnPlantedAxiom : 3 + 0 = 3 := plantedAxiom 3

end AxiomAuditFixture
