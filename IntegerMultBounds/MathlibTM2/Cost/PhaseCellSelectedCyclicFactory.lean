module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicFactorCostEnvelope
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicTableColumn

/-! The entire actual cyclic factory is one selected polynomial setup charge. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem selectedConstructedCyclicFactorCost_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a span : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → span ≤ Sizes.s n i →
      (constructedCyclicFactorCost (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (Sizes.s n i) (Sizes.t n i) a span
        (boundaryRecoveryTarget (Sizes.p n) (target+1)) 2 : ℝ) ≤ C*(Sizes.t n i : ℝ)^6 := by
  obtain ⟨C,hC,htable⟩ := selectedCyclicTableColumnsLoopCost_poly_le ct
  let cw := 1032+8*ct
  let d := 2*cw+1000
  let K := 10000020+1000000+10000000*(ssMulConst+1)
  refine ⟨C+K*d^6+17,by positivity,?_⟩
  filter_upwards [htable] with n hn
  intro h i _ u target a span hu htarget hband ha hspan
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a span
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let bits := boundaryTableBits p solveTarget 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let R := d*t
  have hp := selectedPrecision_le_axis h i
  have hs := (h.good.lt i).le
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [t]; omega
  have hrows : B.card ≤ t := by
    have hb : B.card ≤ s := by simpa only [ZMod.card] using B.card_le_univ
    exact hb.trans hs
  have hb : band ≤ t := hband.trans hs
  have hw : executionWidth p l (initialSchurTarget p u bits 2) 2 ≤ cw*p :=
    selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have hqw : q ≤ executionWidth p l (initialSchurTarget p u bits 2) 2 := by
    dsimp [q,executionPrecision,executionWidth]; omega
  have hq : q ≤ cw*t := hqw.trans (hw.trans (Nat.mul_le_mul_left cw hp))
  have hR : 1 ≤ R := by dsimp [R,d]; nlinarith only [ht,Nat.zero_le (cw*t)]
  have henv : p+2*q+24*band+B.card+100 ≤ R := by
    dsimp [R,d]; nlinarith only [hp,hq,hb,hrows,ht]
  have he := constructedCyclicFactorCost_le_envelope p u l s t a span solveTarget 2 R
    hR (by change q ≤ R; omega) (by change band ≤ R; omega)
    (by change 24*band+1 ≤ R; omega) (by change B.card ≤ R; omega) (by
      have heq : 2*q+8 = executionWidth p l (initialSchurTarget p u bits 2) 2 := by
        dsimp [q,executionPrecision,executionWidth]; omega
      rw [heq]; have hh := hw.trans (Nat.mul_le_mul_left cw hp)
      dsimp [R,d]; nlinarith only [hh,ht]) (by
      change B.card+2*(24*band+1)+2 ≤ R
      dsimp [R,d]; nlinarith only [hrows,hb,ht]) henv
  have hpow : R^5 ≤ R^6 := Nat.pow_le_pow_right hR (by decide)
  have he' : constructedCyclicFactorCost p u l s t a span solveTarget 2 ≤
      cyclicTableColumnsLoopCost p u l s t a span bits+8*B.card+9+K*R^6 := by
    dsimp only [K]
    nlinarith only [he,hpow]
  have hr := (Nat.cast_le (α := ℝ)).mpr he'
  have hc := hn h i u target a span hu htarget hband ha hspan
  have hp6 := (Nat.cast_le (α := ℝ)).mpr (Nat.le_self_pow (by decide : 6 ≠ 0) t)
  have hone := (Nat.cast_le (α := ℝ)).mpr (Nat.one_le_pow 6 t ht)
  have hbR := (Nat.cast_le (α := ℝ)).mpr hrows
  dsimp only [p,s,t,l,band,B,solveTarget,bits,R] at hr hc hp6 hone hbR
  push_cast at hr hp6 hone
  nlinarith only [hr,hc,hp6,hone,hbR]

end IntegerMultBounds.MathlibTM2.Cost
