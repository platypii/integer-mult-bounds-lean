module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCyclicWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSolvedCyclicRecoveryWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedResumedCyclicInteriorWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicPackedRecovery

/-! Compose cached/factor/solve, recovery and resumed interiors on their actual allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def packedCyclicWorkspaceTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce : ℕ) : ℕ :=
  let cw := 16*20+8*ct+8*ce+128
  cachedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce+(65*cw+84)+
    2*cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce

theorem selectedCyclicPackedRecoveryWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce cb : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K J L : ReplicaHaloProblem (Sizes.s m i)) (u target a n replicas : ℕ),
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
      let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
      let q := executionPrecision p l stage 2
      let w := executionWidth p l stage 2
      (∀ D ∈ [H,K,J,L], D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧
        D.target ≤ ct*p ∧ D.rhsExp ≤ ce*p) →
      H.SameLayout J → K.SameLayout L → H.Fs.length = replicas → K.Fs.length = replicas →
      w ≤ cw*p → PhaseCellBand.width p u ≤ cb*p → u ≤ p →
      PhaseCellBand.width p u ≤ s → a ≤ s → n ≤ s →
      cyclicPackedRecoveryWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
        p u l t a n target q w N replicas ≤
        packedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce*replicas*t*p+36*Sizes.T m := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  let push := actualBoundarySolvePushBounds (A := A) (U := U) hQ
  filter_upwards [selectedCachedCyclicReplicaWorkspace_le (A := A) (U := U) hR hQ ct ce cb,
    selectedSolvedCyclicRecoveryWorkspace_le hQ push cw cV,
    selectedResumedReplicaInteriorWorkspace_le (A := A) (U := U) hR hQ ct ce,
    selectedAxisPolynomial_le_volume (48*cw+156) 1 1] with m hc hs hr hv
  intro h i _ H K J L u target a n replicas
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  intro hprofile layoutH layoutK hcountH hcountK hw hbP hu hb ha hn
  have hH := hprofile H (by simp)
  have hK := hprofile K (by simp)
  have hJ := hprofile J (by simp)
  have hL := hprofile L (by simp)
  have hprofileHK : ∀ D ∈ [H,K], D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧
      D.target ≤ ct*p ∧ D.rhsExp ≤ ce*p := by
    intro D hD
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hD
    rcases hD with rfl | rfl
    · exact hH
    · exact hK
  have hcached := hc h i H K u target a n replicas hprofileHK hcountH hcountK hw hbP hu hb ha hn
  have hwidthH := selectedReplicaHaloWidths ct ce h i H hH.1 hH.2.1 hH.2.2.1
    hH.2.2.2.1 hH.2.2.2.2.1 hH.2.2.2.2.2
  have hwidthK := selectedReplicaHaloWidths ct ce h i K hK.1 hK.2.1 hK.2.2.1
    hK.2.2.2.1 hK.2.2.2.2.1 hK.2.2.2.2.2
  have hN : N ≤ s := by simpa only [N,ZMod.card] using
    (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card_le_univ
  have hsolved := hs h i H K replicas N n w hH.1 hK.1 hH.2.1 hK.2.1
    (by simpa only [hH.1] using hwidthH.1) (by simpa only [hK.1] using hwidthK.1)
    (by simpa only [hH.1,cV,cw] using hwidthH.2) (by simpa only [hK.1,cV,cw] using hwidthK.2)
    hcountH hcountK hN hn hw
  have hresumeH := hr h i H J layoutH hJ.1 hJ.2.1 hJ.2.2.1 hJ.2.2.2.1 hJ.2.2.2.2.1 hJ.2.2.2.2.2
  have hresumeK := hr h i K L layoutK hL.1 hL.2.1 hL.2.2.1 hL.2.2.2.1 hL.2.2.2.2.1 hL.2.2.2.2.2
  rw [layoutH.count,hcountH,hJ.1,hJ.2.1] at hresumeH
  rw [layoutK.count,hcountK,hL.1,hL.2.1] at hresumeK
  have hspanH : H.span ≤ t := (show H.span ≤ s by have := H.span_fit; omega).trans (h.good.lt i).le
  have hspanK : K.span ≤ t := (show K.span ≤ s by have := K.span_fit; omega).trans (h.good.lt i).le
  have hvolH := Nat.mul_le_mul hspanH hwidthH.1
  have hvolK := Nat.mul_le_mul hspanK hwidthK.1
  change H.span*H.wordWidth ≤ t*(cw*p) at hvolH
  change K.span*K.wordWidth ≤ t*(cw*p) at hvolK
  have hunit : 1 ≤ t*p := Nat.mul_pos (by have := h.good.lt i; dsimp only [t]; omega)
    (by have := h.thirteen_le_p; dsimp only [p]; omega)
  have htp : t ≤ t*p := Nat.le_mul_of_pos_right _ (by have := h.thirteen_le_p; dsimp only [p]; omega)
  have hmerge : 2*retainedPackedPublicationMergeCost H.span H.wordWidth+
      2*retainedPackedPublicationMergeCost K.span K.wordWidth ≤ Sizes.T m := by
    have hvolume := hv i
    simp only [pow_one] at hvolume
    change (48*cw+156)*t*p ≤ Sizes.T m at hvolume
    unfold retainedPackedPublicationMergeCost
    nlinarith only [hvolume,hvolH,hvolK,hunit,hspanH,hspanK,htp]
  unfold cyclicPackedRecoveryWorkspace cyclicRecoveredInteriorWorkspace packedCyclicWorkspaceTrafficFactor
  change (cachedCyclicReplicaWorkspace (P := Empty) (A := A) (U := U) H K hR hQ p u l t a n target q w N replicas+
    solvedCyclicRecoveryWorkspace (A := A) (U := U) H K replicas N n w hQ)+
    (resumedReplicaInteriorWorkspace (A := A) (U := U) H J hR hQ+
      resumedReplicaInteriorWorkspace (A := A) (U := U) K L hR hQ)+
    (2*retainedPackedPublicationMergeCost H.span H.wordWidth+
      2*retainedPackedPublicationMergeCost K.span K.wordWidth) ≤
    (cachedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce+(65*cw+84)+
      2*cyclicCachedReplicaTrafficFactor (A := A) (U := U) hR hQ ct ce)*replicas*t*p+36*Sizes.T m
  nlinarith only [hcached,hsolved,hresumeH,hresumeK,hmerge]

end IntegerMultBounds.MathlibTM2.Cost
