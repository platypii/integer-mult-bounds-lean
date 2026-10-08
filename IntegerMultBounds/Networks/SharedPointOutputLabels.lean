import IntegerMultBounds.Networks.SharedPointOutputMap
import IntegerMultBounds.Networks.FanoutFrames

/-! The actual lifted output supports carry exactly the rational source-span
labels used for terminal attachment in the shared-point network. -/

namespace IntegerMultBounds.Networks.SharedPointOutputLabels

open NeighborCounts SharedPointLift SharedPointMap SharedPointLabels Labels

theorem filter_label (h : ℕ) (c : Fin h) (T : Triple h) (hc : c ∈ T.val) :
    FanoutFrames.label (fun S : Triple h => S.val)
        (Finset.univ.filter (fun S : Triple h => S.val ∩ T.val = {c})) = outputSpan c T := by
  rw [outputSpan_eq_sourceSpan c T hc]
  unfold FanoutFrames.label indexedSpan
  congr 1
  ext S
  constructor
  · rintro ⟨U, hU, rfl⟩
    exact ⟨U.property, (Finset.mem_filter.mp hU).2⟩
  · rintro ⟨hS, hST⟩
    exact ⟨⟨S,hS⟩, Finset.mem_filter.mpr ⟨Finset.mem_univ _, hST⟩, rfl⟩

/-- Canonical checked output masks give exactly the existing output-span label. -/
theorem exclusion_label (n : ℕ) (c : Fin (n+1)) (j : Fin (n.choose 2)) :
    FanoutFrames.label (fun S : Triple (n+1) => S.val)
        (lift (pairPayload n) (pairPayload_card n) c
          (MaskDAG.decode (PairMask.exclusion n (PairMask.pairAt n j).1 (PairMask.pairAt n j).2))) =
      outputSpan c (source (pairPayload n) (pairPayload_card n) c j) := by
  rw [SharedPointOutputMap.lifted_exclusion]
  exact filter_label _ c _ (by simp [source_val])

theorem exclusion_nondegenerate (n : ℕ) (c : Fin (n+1)) (j : Fin (n.choose 2)) :
    ((rational (n+1)).restrict
      (FanoutFrames.label (fun S : Triple (n+1) => S.val)
        (lift (pairPayload n) (pairPayload_card n) c
          (MaskDAG.decode (PairMask.exclusion n (PairMask.pairAt n j).1 (PairMask.pairAt n j).2))))).Nondegenerate := by
  rw [exclusion_label]
  exact outputSpan_nondegenerate _ _

/-- Each actual output source span lies in its target line's orthogonal complement. -/
theorem exclusion_orthogonal (n : ℕ) (c : Fin (n+1)) (j : Fin (n.choose 2)) :
    FanoutFrames.label (fun S : Triple (n+1) => S.val)
        (lift (pairPayload n) (pairPayload_card n) c
          (MaskDAG.decode (PairMask.exclusion n (PairMask.pairAt n j).1 (PairMask.pairAt n j).2))) ≤
      (rational (n+1)).orthogonal
        (ℚ ∙ (indicator (source (pairPayload n) (pairPayload_card n) c j).val : Fin (n+1) → ℚ)) := by
  rw [exclusion_label]
  exact outputSpan_orthogonal c _ (by simp [source_val])

end IntegerMultBounds.Networks.SharedPointOutputLabels
