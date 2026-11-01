module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedBatchedRecoveryFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryMaskInitialization
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisDensity
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! The executed initialized recovery caller pays shared interior setup, one volume allowance,
and fast repeated work at the selected axis density. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedInitializedCachedReplicaRecovery_fast_le (ct ce : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ (target : ℕ) (X : ℕ → ZMod (Sizes.s n i) → ℝ) (B : ReplicaRecoveryBatch H target X),
      ∀ htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card,
      ∀ steps : ℕ, steps ≤ initializedCachedBatchedReplicaRecoveryTime H (B.problem htarget) →
      (steps : ℝ) ≤
        (initializedReplicaHaloSharedTime (B.problem htarget)+Sizes.T n+24 : ℕ)+
        D*H.Fs.length*(H.t : ℝ)*(1+(H.band : ℝ)^2/Sizes.d n)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨D,hD,hfast⟩ := cachedBatchedReplicaRecovery_fast_le 20 cw 20 cV
  refine ⟨D,hD,?_⟩
  filter_upwards [selectedAxis_eventually_polynomial 1 2,
    selectedInitializeRecoveryMasksCost_volume_le cV 1] with n haxis hsetup
  intro h i _ H hp ht hl hu htarget hrhs target X B htargetRecovery steps hn
  obtain ⟨hl',hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hl'
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hr
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVp : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  have hg : H.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
  have hlRing : H.l = haloInverseRingLog (Sizes.s n i) H.t := by rw [ht]; exact hl
  have hc := hfast H target X B htargetRecovery hlH hwH hrH hVp hg hlRing (by simpa only [hp,ht,one_mul] using haxis i)
  have hnR : (steps : ℝ) ≤ (initializeRecoveryMasksCost H.metadataWidth H.span H.band : ℕ)+
      (cachedBatchedReplicaRecoveryTime H (B.problem htargetRecovery) : ℕ) := by exact_mod_cast hn
  have hspan : H.span ≤ Sizes.t n i := by have := H.span_fit; have := h.good.lt i; omega
  have hband : H.band ≤ Sizes.t n i := by have hh : H.band ≤ Sizes.s n i := H.band_fit; have := h.good.lt i; omega
  have hsetupH := hsetup h i H.metadataWidth H.span H.band hspan hband (by simpa only [hp] using hVp)
  have hsetupR : (initializeRecoveryMasksCost H.metadataWidth H.span H.band : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (by simpa only [one_mul] using hsetupH)
  have hv := axisGapVolume_le (band := H.band)
    (by have := h.one_le_d; omega : 0 < Sizes.d n) (h.good.lt i).le (h.good.bounds i)
  rw [←ht] at hv
  have hs := mul_le_mul_of_nonneg_left hv
    (by positivity : (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  push_cast at hc hnR hsetupR hs ⊢
  nlinarith only [hc,hnR,hs,hsetupR]

end IntegerMultBounds.MathlibTM2.Cost
