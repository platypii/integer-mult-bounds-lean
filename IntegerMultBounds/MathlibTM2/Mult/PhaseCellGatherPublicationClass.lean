module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCorePublicationGroups

/-! A fitting halo-length gather class publishes cores of length H-2*radius.
The original ordered core keys are retained, rather than conflating halo and core lengths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix

def gatherPublicationClass (s width radius H : ℕ) : CorePublicationClass s width where
  length := H-2*radius
  indices := coreGatherIndices s width radius H
  sublist := by
    let keep := fun k => decide (coreLength s width k = H-2*radius)
    have hsub := (List.filter_sublist (l := coreIndices s width)
      (p := fun k => decide (radius ≤ coreStart width k ∧
        coreStart width k+coreLength s width k+radius ≤ s ∧ coreLength s width k+2*radius = H))).filter keep
    have hfilter : (coreGatherIndices s width radius H).filter keep = coreGatherIndices s width radius H := by
      apply List.filter_eq_self.mpr
      intro k hk
      have hh := (coreGatherIndices_spec s width radius H k hk).2.2
      simp only [keep,decide_eq_true_eq]
      omega
    change ((coreGatherIndices s width radius H).filter keep).Sublist (corePublicationIndices s width (H-2*radius)) at hsub
    rw [hfilter] at hsub
    exact hsub

theorem gatherPublicationClass_coreLength (s width radius H k : ℕ)
    (hk : k ∈ (gatherPublicationClass s width radius H).indices) :
    coreLength s width k = (gatherPublicationClass s width radius H).length := by
  have hk' : k ∈ coreGatherIndices s width radius H := by simpa only [gatherPublicationClass] using hk
  have hh := (coreGatherIndices_spec s width radius H k hk').2.2
  change coreLength s width k = H-2*radius
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
