module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCouplingSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedReplicaSharedSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAxisDensity

/-! Complete selected time for the executed cached first pass. Shared setup is
paid per core; replica work is charged at the manuscript's axis-gap density. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedFirstCachedReplicaPass_total_fast_le (ct ce : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in atTop, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ firstCachedReplicaPassTime H →
      (steps : ℝ) ≤ (2*Sizes.T n+24 : ℕ)+
        F*H.Fs.length*(H.t : ℝ)*(1+(H.band : ℝ)^2/Sizes.d n)*(H.p : ℝ)^(129/128 : ℝ) := by
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨F,hF,hfast⟩ := selectedFirstCachedReplicaPass_fast_le ct ce
  refine ⟨F,hF,?_⟩
  filter_upwards [selectedReplicaHaloSharedTime_volume_le 20 cw 20 cV 1,
    selectedCachedReplicaCouplingSharedTime_volume_le cw cV 1] with n hs hc
  intro h i _ H hp ht hl hu htarget hrhs steps hn
  have hf := hfast h i H hp ht hl hu htarget hrhs steps hn
  obtain ⟨hl',hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hl'
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hr
  have hwH : H.wordWidth ≤ cw*H.p := by simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVp : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  have huH : H.u ≤ H.p := by simpa only [hp] using hu
  have hsH := hs h i H hp ht huH hlH hwH hrH hVp
  have hcH := hc h i H hp ht hwH huH hVp
  have hsR : (initializedReplicaHaloSharedTime H : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (by simpa only [one_mul] using hsH)
  have hcR : (cachedReplicaCouplingSharedTime H : ℝ) ≤ Sizes.T n := by
    exact_mod_cast (by simpa only [one_mul] using hcH)
  have hv := axisGapVolume_le (band := H.band)
    (by have := h.one_le_d; omega : 0 < Sizes.d n) (h.good.lt i).le (h.good.bounds i)
  rw [←ht] at hv
  have hg := mul_le_mul_of_nonneg_left hv
    (by positivity : (0 : ℝ) ≤ F*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  push_cast at hf hsR hcR hg ⊢
  nlinarith only [hf,hsR,hcR,hg]

end IntegerMultBounds.MathlibTM2.Cost
