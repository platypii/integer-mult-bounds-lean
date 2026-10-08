import IntegerMultBounds.Networks.Certificates.Shared50.Checked
import IntegerMultBounds.Networks.Certificates.Shared50.Semantics

/-! Every compact duplicate certificate is a genuine witness in the actual
fifty-copy family, giving the concrete optimized support-count bound. -/

namespace IntegerMultBounds.Networks.Certificates.Shared50

open SharedPointWitnessCheck

attribute [local irreducible] rows

/-- Every listed match satisfies the genuine family-witness predicate. -/
theorem witnesses_genuine (row : SharedPointWitnessCheck.Witness 49) (hr : row ∈ witnesses) :
    SharedPointMatching.IsWitness SharedPointFamily.family row := by
  have hr' : row ∈ rows := List.mem_toFinset.mp hr
  have hc := (checkFrom_sound isAddition Paired49.signatureCoreBank.lookup
    Paired49.signatureUnionBank.lookup none rows rows_checked).2.1 row hr'
  obtain ⟨ho, hl, hr, he⟩ := checkRow_sound (SharedPointLift.pairPayload 49)
    (SharedPointLift.pairPayload_card 49) SharedPointFamily.localSupport
    isAddition Paired49.signatureCoreBank.lookup Paired49.signatureUnionBank.lookup bank_correct row hc
  exact ⟨isAddition_domain row.1 hl, isAddition_domain row.2 hr, ho, he⟩

/-- Certified cross-copy sharing saves at least 40,256 actual additions. -/
theorem support_image_bound :
    (SharedPointFamily.domain.image SharedPointFamily.support).card ≤ 450394 := by
  apply SharedPointMatching.h50_bound SharedPointFamily.family witnesses witnesses_genuine
  · exact SharedPointFamily.domain_card.le
  · exact witnesses_card.ge

end IntegerMultBounds.Networks.Certificates.Shared50
