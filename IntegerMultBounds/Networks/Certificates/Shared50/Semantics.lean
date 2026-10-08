import IntegerMultBounds.Networks.Certificates.Shared50.Data
import IntegerMultBounds.Networks.Certificates.Shared50.Kinds
import IntegerMultBounds.Networks.SharedPointFamily

/-! The compact certificate supplies actual duplicate witnesses in the
fifty-copy family. All membership, signature and counting premises are closed. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50

open SharedPointWitnessCheck

attribute [local irreducible] Paired49.entries Paired49.bank Paired49.signatureCoreBank
  Paired49.signatureUnionBank Paired49Certificate.nodes

/-- The numeric interval is backed by the actual checked entry kinds. -/
theorem isAddition_sound (i : ℕ) (ha : isAddition i = true) :
    ∃ entry, Paired49.entries[i]? = some entry ∧ ∃ l r, entry.kind = .add l r := by
  have hbounds : 1176 ≤ i ∧ i < 10989 := by simpa only [isAddition, decide_eq_true_eq] using ha
  have hi : i < Paired49.entries.length := by rw [Paired49.entries_length]; exact hbounds.2
  refine ⟨Paired49.entries[i], List.getElem?_eq_getElem hi, ?_⟩
  exact checkKinds_sound 1176 0 Paired49.entries kinds_checked i hi (by simpa using hbounds.1)

theorem isAddition_domain (node : SharedPointMatching.CopyNode 50)
    (ha : isAddition node.2 = true) : node ∈ SharedPointFamily.domain :=
  (SharedPointFamily.mem_domain_entries node).mpr (isAddition_sound node.2 ha)

theorem signaturePayload_eq : Paired49.signaturePayload = (SharedPointLift.pairPayload 49) := by
  funext i
  exact (SharedPointLift.pairPayload_eq_filter 49 i).symm

/-- The compact summary banks describe the actual family support at every
certified addition index, not a separately supplied abstract support family. -/
theorem bank_correct : BankCorrect (SharedPointLift.pairPayload 49) SharedPointFamily.localSupport
    isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup := by
  intro i ha
  have hbounds : 1176 ≤ i ∧ i < 10989 := by simpa only [isAddition, decide_eq_true_eq] using ha
  have hi : i < Paired49Certificate.nodes.length := by rw [Paired49Certificate.node_count]; exact hbounds.2
  refine ⟨?_, ?_⟩
  · rw [SharedPointFamily.localSupport_get i hi]
    exact DisjointUnique.valid_nonempty _ Paired49Certificate.valid _ (List.getElem_mem hi)
  · intro c u hc hu
    have hh := Paired49.signature_banks_correct Paired49.entries_checked i
      (by rw [Paired49.entries_length]; exact hbounds.2)
    rw [hc, hu, signaturePayload_eq] at hh
    cases hm : Paired49.bank.lookup i with
    | none => simp [hm] at hh
    | some mask =>
      simp only [hm, Option.map_some, Option.some.injEq] at hh
      rw [SharedPointFamily.localSupport_bank i hbounds.2, hm]
      exact hh

end IntegerMultBounds.Networks.Certificates.Shared50
