module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedInteriorPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSchurColumn
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFamilyBatchFast

/-! Price the actual uncached interior construction used by Schur columns,
then close every shared family setup charge with a uniform polynomial bound. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedInteriorConstruction_weights_le (ct : ℕ) :
    ∃ K : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (haloBoundary s t band a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      solveHaloInteriorCost p l s t u stage 2 a b ≤
        familyHaloInteriorGeometryCost p l s t u stage 2 a b+K*t*p^4 := by
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cZ := 3*c+500000
  refine ⟨10000000*cZ^4,?_⟩
  intro n h i _ u target a b hu htarget hband
  dsimp only
  obtain ⟨hpt,hN,hq,hw,hV,hW,hB⟩ := hwidths n h i u target a b htarget hband
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hst : s < t := h.good.lt i
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x d : ℕ) (hx : x ≤ d*p) (hd : d ≤ cZ) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p hd)
  have hPZ := hparam (2^15*p) (2^15) le_rfl (by dsimp only [cZ]; omega)
  have hwZ := hparam w c hw (by dsimp only [cZ]; omega)
  have hqZ := hparam q c hq (by dsimp only [cZ]; omega)
  have hNZ : executionStagePrecision p l stage 2+1 ≤ Z :=
    (show executionStagePrecision p l stage 2+1 ≤ w by dsimp only [w,executionWidth,executionStagePrecision]; omega).trans hwZ
  obtain ⟨hl,_⟩ := haloInverseRingLog_bounds hp hst (h.quarter_p_le_theta i)
  have hlZ := hparam l 20 hl (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa using hu) (by dsimp only [cZ]; omega)
  have hv := selectedWeightWorkspaceWidth_le c h i q w u hw
    (by dsimp only [q,w,executionPrecision,executionWidth]; omega) hu
  have hvZ := hparam _ (2*c+426009) hv (by dsimp only [cZ]; omega)
  have hcell := phaseGap_cellLength_le hp hst (h.quarter_p_le_theta i)
  have hkeys : ∀ L ∈ haloLengthCandidates s t band a b, L ≤ Z := by
    intro L hL
    have hlen := haloLengthCandidates_uniform hst band a b hL
    apply hparam L 5 (by omega)
    dsimp only [cZ]; omega
  have hcost := haloInteriorCostBound_weights_poly p l u stage 2 a b Z hst hZ
    hPZ hNZ hqZ hlZ huZ hwZ hvZ hkeys
  have hrun := solveHaloInteriorCost_le hst p l u stage 2 a b
  have heq : 10000000*t*Z^4 = (10000000*cZ^4)*t*p^4 := by dsimp only [Z]; ring
  rw [heq] at hcost
  exact hrun.trans hcost

theorem selectedInteriorConstruction_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let stage := initialSchurTarget p u bits 2
      (solveHaloInteriorCost p l s t u stage 2 a b : ℝ) ≤ C*(t : ℝ)*(p : ℝ)^4 := by
  obtain ⟨D,hD,hpair⟩ := selectedInteriorPair_fast_le ct
  obtain ⟨K,hK⟩ := selectedInteriorConstruction_weights_le ct
  refine ⟨D+(K : ℝ),by positivity,?_⟩
  filter_upwards [hpair] with n hn
  intro h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let initialCost := familyHaloInteriorGeometryCost p l s t u stage 2 a b
  let recoveryCost := familyHaloInteriorGeometryCost p l s t u (recoveryTarget p bits)
    (recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)) a b
  have hpairs := hn h i u target a b hu htarget hband ha hb
  change (initialCost : ℝ)+(recoveryCost : ℝ) ≤ D*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) at hpairs
  have hpos : (0 : ℝ) ≤ recoveryCost := Nat.cast_nonneg _
  have hfamily : (initialCost : ℝ) ≤ D*(t : ℝ)*(p : ℝ)^(129/128 : ℝ) := by linarith only [hpairs,hpos]
  have hp : (1 : ℝ) ≤ p := by exact_mod_cast (show 1 ≤ p by have := h.thirteen_le_p; dsimp only [p]; omega)
  have hpow : (p : ℝ)^(129/128 : ℝ) ≤ (p : ℝ)^4 := by
    simpa only [Real.rpow_natCast] using Real.rpow_le_rpow_of_exponent_le hp (show (129/128 : ℝ) ≤ (4 : ℕ) by norm_num)
  have hscaled := mul_le_mul_of_nonneg_left hpow (show 0 ≤ D*(t : ℝ) by positivity)
  have he := hK n h i u target a b hu htarget hband
  change solveHaloInteriorCost p l s t u stage 2 a b ≤ initialCost+K*t*p^4 at he
  have heR : (solveHaloInteriorCost p l s t u stage 2 a b : ℝ) ≤ (initialCost : ℝ)+(K : ℝ)*(t : ℝ)*(p : ℝ)^4 := by exact_mod_cast he
  nlinarith only [heR,hfamily,hscaled]

theorem selectedFamilySetup_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      (generatedFamilyComplexSetupCostBound A p u (haloInverseRingLog s t) s t a b target : ℝ) ≤
        C*(t : ℝ)^6*(p : ℝ)^4 := by
  obtain ⟨J,hJ⟩ := selectedFamilySetup_interiorConstruction_le ct
  obtain ⟨K,hK,hconstruct⟩ := selectedInteriorConstruction_poly_le ct
  refine ⟨(J : ℝ)+K,by positivity,?_⟩
  filter_upwards [hconstruct] with n hn
  intro h i _ A u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
  let stage := initialSchurTarget p u bits 2
  let constructionCost := solveHaloInteriorCost p l s t u stage 2 a b
  have hcost := hn h i u target a b hu htarget hband ha hb
  change (constructionCost : ℝ) ≤ K*(t : ℝ)*(p : ℝ)^4 at hcost
  have hs := hJ n h i A u target a b hu htarget hband ha hb
  change generatedFamilyComplexSetupCostBound A p u l s t a b target ≤ N*constructionCost+J*t^6*p^4 at hs
  have hsR : (generatedFamilyComplexSetupCostBound A p u l s t a b target : ℝ) ≤
      (N : ℝ)*(constructionCost : ℝ)+(J : ℝ)*(t : ℝ)^6*(p : ℝ)^4 := by exact_mod_cast hs
  have hN : N ≤ t :=
    (show N ≤ s by simpa [N] using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans (h.good.lt i).le
  have hNR : (N : ℝ) ≤ t := by exact_mod_cast hN
  have hcharge := mul_le_mul hNR hcost (Nat.cast_nonneg constructionCost) (Nat.cast_nonneg t)
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hpow : (t : ℝ)^2 ≤ (t : ℝ)^6 := by exact_mod_cast (Nat.pow_le_pow_right ht (show 2 ≤ 6 by decide))
  have hscale := mul_le_mul_of_nonneg_left hpow (show 0 ≤ K*(p : ℝ)^4 by positivity)
  nlinarith only [hsR,hcharge,hscale]

theorem selectedFamilyBatch_poly_fast_le (ct : ℕ) :
    ∃ C D : ℝ, 0 ≤ C ∧ 0 ≤ D ∧ ∀ᶠ n : ℕ in atTop,
      ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ A u target a b replicas : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let band := PhaseCellBand.width p u
      (generatedClosedFamilyComplexBatchCost A p u (haloInverseRingLog s t) s t a b target replicas : ℝ) ≤
        C*(t : ℝ)^6*(p : ℝ)^4+
          (replicas : ℝ)*D*(t : ℝ)*(1+(band : ℝ)^2/Sizes.d n)*(p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨C,hC,hsetup⟩ := selectedFamilySetup_poly_le ct
  obtain ⟨D,hD,hbatch⟩ := selectedFamilyBatch_density_fast_le ct
  refine ⟨C,D,hC,hD,?_⟩
  filter_upwards [hsetup,hbatch] with n hs hb
  intro h i _ A u target a b replicas hu htarget hband ha hbound
  dsimp only
  have hc := hs h i A u target a b hu htarget hband ha hbound
  have hd := hb h i A u target a b replicas hu htarget hband ha hbound
  dsimp only at hc hd
  exact hd.trans (add_le_add hc le_rfl)

end IntegerMultBounds.MathlibTM2.Cost
