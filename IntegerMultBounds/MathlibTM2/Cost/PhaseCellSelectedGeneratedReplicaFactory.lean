module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedReplicaFactoryControls
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedFactorCost

/-! The ordinary-header factory is shared across replicas. Its complete bill,
and any fixed stock scale of that bill, fit the selected volume allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedGeneratedReplicaBoundaryFactoryCost_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)) (target : ℕ),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      target ≤ ct*Sizes.p n → H.rhsExp = 2 →
      H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p (target+1)) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card →
      generatedReplicaBoundaryFactoryCost H (target+1) ≤ C*Sizes.t n i^6*Sizes.p n^4 := by
  obtain ⟨D,hfactor⟩ := selectedConstructedBoundaryFactorCost_poly_le ct
  obtain ⟨cw,hcw,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cZ := cw+33000
  let K := 10000*cZ^2
  refine ⟨D+K,?_⟩
  filter_upwards [hfactor] with n hf
  intro h i _ H target hp ht hl hu htarget hrhs hsetup
  let p := Sizes.p n
  let t := Sizes.t n i
  let Z := cZ*t*p
  have hp1 : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht1 : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hband : PhaseCellBand.width p H.u ≤ Sizes.s n i := by simpa only [ReplicaHaloProblem.band,hp,p] using H.band_fit
  obtain ⟨_,_,hq,hw,hV,_,_⟩ := hwidths n h i H.u target H.origin (H.origin+H.span) htarget hband
  obtain ⟨hprecision,hstage,hword⟩ := H.boundary_sizing (boundaryRecoveryTarget H.p (target+1)) hsetup
  have hqH : H.precision ≤ cw*p := by
    rw [hprecision]
    simpa only [hp,ht,hl,hrhs,ReplicaHaloProblem.band,p] using hq
  have hwH : H.wordWidth ≤ cw*p := by
    rw [hword]
    simpa only [hp,ht,hl,hrhs,ReplicaHaloProblem.band,p] using hw
  have hstageH : H.stage+1 ≤ cw*p := by
    have hh : H.stage+1 ≤ H.wordWidth := by
      unfold ReplicaHaloProblem.stage ReplicaHaloProblem.wordWidth executionStagePrecision executionWidth
      omega
    exact hh.trans hwH
  have hVH : publicationGeometryWidth H.t H.band ≤ cw*p := by
    simpa only [ht,hp,ReplicaHaloProblem.band,p] using hV
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z := by
    calc
      x ≤ c*p := hx
      _ ≤ cZ*p := Nat.mul_le_mul_right _ hc
      _ ≤ cZ*t*p := Nat.mul_le_mul_right p (Nat.le_mul_of_pos_right cZ ht1)
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos (by dsimp only [cZ]; omega) ht1) hp1
  have htZ : H.t ≤ Z := by
    rw [ht]
    change t ≤ cZ*t*p
    nlinarith only [hp1,show 1 ≤ cZ by dsimp only [cZ]; omega,
      Nat.mul_le_mul_left t hp1]
  obtain ⟨hl20,_⟩ := haloInverseRingLog_bounds hp1 (h.good.lt i) (h.quarter_p_le_theta i)
  have hlH : H.l ≤ 20*p := by simpa only [hl,p] using hl20
  have hc := generatedReplicaBoundaryFactoryCost_controls_le H (target+1) hZ htZ
    (hparam _ 32768 (by norm_num only [hp,show 2^15 = 32768 by norm_num]; rfl) (by dsimp only [cZ]; omega))
    (hparam _ cw hstageH (by dsimp only [cZ]; omega))
    (hparam _ cw hqH (by dsimp only [cZ]; omega))
    (hparam _ 20 hlH (by dsimp only [cZ]; omega))
    (hparam _ 1 (by simpa only [one_mul,p] using hu) (by dsimp only [cZ]; omega))
    (hparam _ cw hVH (by dsimp only [cZ]; omega))
  have hnum := hf h i H.u target H.origin (H.origin+H.span) hu htarget hband
    (show H.origin ≤ Sizes.s n i by have := H.span_fit; omega) H.span_fit
  have hnumH : constructedBoundaryFactorCost H.p H.u H.l (Sizes.s n i) H.t H.origin (H.origin+H.span)
      (boundaryRecoveryTarget H.p (target+1)) H.rhsExp ≤ D*t^6*p^4 := by
    simpa only [hp,ht,hl,hrhs,p,t] using hnum
  have hscale : 10000*Z^2 ≤ K*t^6*p^4 := by
    have htt : t^2 ≤ t^6 := Nat.pow_le_pow_right ht1 (by decide)
    have hpp : p^2 ≤ p^4 := Nat.pow_le_pow_right hp1 (by decide)
    have hh := Nat.mul_le_mul_left K (Nat.mul_le_mul htt hpp)
    convert hh using 1 <;> dsimp only [Z,K] <;> ring
  change _ ≤ (D+K)*t^6*p^4
  nlinarith only [hc,hnumH,hscale]

theorem selectedGeneratedReplicaBoundaryFactoryCost_scaled_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)) (target : ℕ),
      H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) → H.u ≤ Sizes.p n →
      target ≤ ct*Sizes.p n → H.rhsExp = 2 →
      H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p (target+1)) H.rhsExp
        (haloBoundary (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card →
      scale*generatedReplicaBoundaryFactoryCost H (target+1) ≤ Sizes.T n := by
  obtain ⟨C,hcost⟩ := selectedGeneratedReplicaBoundaryFactoryCost_poly_le ct
  filter_upwards [hcost,selectedAxisPolynomial_le_volume (scale*C) 4 6] with n hc hv
  intro h i _ H target hp ht hl hu htarget hrhs hsetup
  exact (Nat.mul_le_mul_left scale (hc h i H target hp ht hl hu htarget hrhs hsetup)).trans
    (by convert hv i using 1 <;> ring)

end IntegerMultBounds.MathlibTM2.Cost
