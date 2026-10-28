module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSharedHaloControl
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedBoundary
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellHaloRingSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoverySizing

/-! Apply initialization pricing to the inverse caller's actual first and recovery precisions. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def executionLengthKeySetupCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  initializeHaloLengthKeysBound (2^15*p) (executionStagePrecision p l target rhsExp+1)
    (executionPrecision p l target rhsExp) l s t u (PhaseCellBand.width p u) a b

def executionSharedHaloControlCost (p l s t u target rhsExp a b : ℕ) : ℕ :=
  let q := executionPrecision p l target rhsExp
  let w := executionWidth p l target rhsExp
  ((haloLengthCandidates s t (PhaseCellBand.width p u) a b).map (fun L =>
    haloOriginControlsSharedCost (2^15*p) q s t u (PhaseCellBand.width p u) a b L+
      advanceControlsSharedCost (haloGeometryWidth t w) s w)).sum

theorem executionSharedHaloControlCost_congr (p l s t u j k e f a b : ℕ)
    (hE : executionExponent p l j e = executionExponent p l k f) :
    executionSharedHaloControlCost p l s t u j e a b = executionSharedHaloControlCost p l s t u k f a b := by
  simp only [executionSharedHaloControlCost,executionPrecision,executionWidth,hE]

theorem selectedInverseWorkingWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    [NeZero (Sizes.s n i)] (u target a b : ℕ) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
      (haloBoundary s t (PhaseCellBand.width p u) a b).card
    executionWidth p l (initialSchurTarget p u bits 2) 2 ≤ (1032+8*ct)*p := by
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let N := (haloBoundary s t (PhaseCellBand.width p u) a b).card
  change PhaseCellBand.width p u ≤ s at hband
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hst : s < t := h.good.lt i
  have hθ := h.quarter_p_le_theta i
  obtain ⟨hl,hr⟩ := haloInverseRingLog_bounds hp hst hθ
  have hbits : Nat.size (2*s+1) ≤ Nat.size t+2 := by
    apply Nat.size_le.mpr
    rw [pow_add]
    norm_num
    have := Nat.lt_size_self t
    omega
  have htbits := selectedAxisBits_le n i
  have hell : Sizes.ℓ n ≤ p := selectedAxisLog_le_precision h
  have hgeometry : Nat.size (2*s+1) ≤ 2*p := by have := h.thirteen_le_p; dsimp [t,p] at *; omega
  have hN : N ≤ s := by simpa [N] using Finset.card_le_univ (s := haloBoundary s t (PhaseCellBand.width p u) a b)
  have hNlog : Nat.size N ≤ 2*p := (Nat.size_le_size (by omega : N ≤ 2*s+1)).trans hgeometry
  have hBlog : Nat.size (2*PhaseCellBand.width p u+1) ≤ 2*p :=
    (Nat.size_le_size (by omega)).trans hgeometry
  have hw := inverseExecutionWidth_le p l target N (PhaseCellBand.width p u) 20 ct 2 2 hp hl htarget hNlog hBlog
  rw [inverseExecutionExponent_eq p u l target N] at hw
  simpa only [executionWidth,show 16*20+8*ct+8*2+8*2+680 = 1032+8*ct by omega] using hw

theorem selectedInteriorSetupControls_fast_le (ct : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ (u target a b : ℕ), u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
        (haloBoundary s t (PhaseCellBand.width p u) a b).card
      let firstTarget := initialSchurTarget p u bits 2
      let secondTarget := recoveryTarget p bits
      let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
      executionLengthKeySetupCost p l s t u firstTarget 2 a b+
        executionLengthKeySetupCost p l s t u secondTarget recoveryExp a b+
        executionSharedHaloControlCost p l s t u firstTarget 2 a b+
        executionSharedHaloControlCost p l s t u secondTarget recoveryExp a b ≤ C*t*p := by
  obtain ⟨C,hC⟩ := selectedExecutionLengthKeyInitialization_fast_le (1032+8*ct) 20
  obtain ⟨K,hK⟩ := selectedSharedHaloControlCandidates_fast_le (1032+8*ct)
  refine ⟨2*C+2*K,?_⟩
  intro n h i _ u target a b hu htarget hband ha hb
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2
    (haloBoundary s t (PhaseCellBand.width p u) a b).card
  let firstTarget := initialSchurTarget p u bits 2
  let secondTarget := recoveryTarget p bits
  let recoveryExp := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hw := selectedInverseWorkingWidth_le ct h i u target a b htarget hband
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp [p]; omega
  have hst : s < t := h.good.lt i
  have hθ := h.quarter_p_le_theta i
  have hl := (haloInverseRingLog_bounds hp hst hθ).1
  have hfirst := hC n h i l u firstTarget 2 a b hw hl hu hband ha hb
  have hE : executionExponent p l firstTarget 2 = executionExponent p l secondTarget recoveryExp :=
    recovery_execution_exponent p l secondTarget 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
  have hw₂ : executionWidth p l secondTarget recoveryExp ≤ (1032+8*ct)*p := by
    simpa only [executionWidth,← hE] using hw
  have hsecond := hC n h i l u secondTarget recoveryExp a b hw₂ hl hu hband ha hb
  have hq : executionPrecision p l firstTarget 2 ≤ (1032+8*ct)*p := by
    have hh : executionPrecision p l firstTarget 2 ≤ executionWidth p l firstTarget 2 := by
      dsimp [executionPrecision,executionWidth]; omega
    exact hh.trans hw
  have hshared := hK n h i (executionPrecision p l firstTarget 2) u (PhaseCellBand.width p u) a b
    hq hu hband ha hb
  have hqw : 2*executionPrecision p l firstTarget 2+8 = executionWidth p l firstTarget 2 := by
    dsimp [executionPrecision,executionWidth]; omega
  have hshared₁ : executionSharedHaloControlCost p l s t u firstTarget 2 a b ≤ K*t*p := by
    simpa only [executionSharedHaloControlCost,hqw] using hshared
  have hshared₂ : executionSharedHaloControlCost p l s t u secondTarget recoveryExp a b ≤ K*t*p := by
    rw [← executionSharedHaloControlCost_congr p l s t u firstTarget secondTarget 2 recoveryExp a b hE]
    exact hshared₁
  change executionLengthKeySetupCost p l s t u firstTarget 2 a b+
    executionLengthKeySetupCost p l s t u secondTarget recoveryExp a b+
    executionSharedHaloControlCost p l s t u firstTarget 2 a b+
    executionSharedHaloControlCost p l s t u secondTarget recoveryExp a b ≤ (2*C+2*K)*t*p
  dsimp only [executionLengthKeySetupCost]
  nlinarith only [hfirst,hsecond,hshared₁,hshared₂]

end IntegerMultBounds.MathlibTM2.Cost
