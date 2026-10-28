module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellMaskPhaseCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGenerateRecoveryCouplingMask

/-! Actual publication, coupling and doubled-band recovery masks cost O(t*p) on selected axes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem selectedMaskGeometryWidth_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    {B : ℕ} (hB : B ≤ 2*Sizes.s n i) :
    publicationGeometryWidth (Sizes.t n i) B+4 ≤ 6*Sizes.p n ∧
      (publicationGeometryWidth (Sizes.t n i) B+4)^2 ≤ 4096*Sizes.d n*Sizes.p n := by
  have hst := h.good.lt i
  have hB2t : B ≤ 2*Sizes.t n i := hB.trans (Nat.mul_le_mul_left 2 hst.le)
  have hbits : Nat.size B ≤ Nat.size (Sizes.t n i)+1 := by
    apply Nat.size_le.mpr
    have ht := Nat.mul_lt_mul_of_pos_left (Nat.lt_size_self (Sizes.t n i)) (by decide : 0 < 2)
    rw [pow_succ]
    nlinarith only [hB2t,ht]
  have htbits := selectedAxisBits_le n i
  have hL : publicationGeometryWidth (Sizes.t n i) B+4 ≤ 4*Sizes.ℓ n+17 := by
    dsimp only [publicationGeometryWidth]
    omega
  have hl := h.ℓ_bounds.2
  have hdl : Sizes.ℓ n ≤ Sizes.d n*Sizes.ℓ n := Nat.le_mul_of_pos_left _ h.one_le_d
  have hell : Sizes.ℓ n ≤ Sizes.p n := by nlinarith only [hl,hdl,Nat.zero_le (Sizes.d n*Sizes.ℓ n)]
  have hp := h.thirteen_le_p
  have hell2 := h.two_le_ℓ
  refine ⟨by omega,?_⟩
  have hL' : publicationGeometryWidth (Sizes.t n i) B+4 ≤ 13*Sizes.ℓ n := by omega
  have hsq := Nat.pow_le_pow_left hL' 2
  have hlog := Nat.mul_le_mul_left 169 (selectedAxisLog_sq_le h)
  nlinarith only [hsq,hlog,Nat.zero_le (Sizes.d n*Sizes.p n)]

theorem selectedMaskPhaseBudget_le {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n))
    {B a b : ℕ} (hB : B ≤ 2*Sizes.s n i) (ha : a ≤ Sizes.s n i) (hb : b ≤ Sizes.s n i) :
    maskPhaseBudget (Sizes.s n i) (Sizes.t n i) B a b ≤ 10000*Sizes.t n i*Sizes.p n := by
  let g := Sizes.t n i-Sizes.s n i
  let L := publicationGeometryWidth (Sizes.t n i) B+4
  let H := Sizes.s n i+Sizes.t n i+B+a+b+1
  have hwidth := selectedMaskGeometryWidth_le h i hB
  change L ≤ 6*Sizes.p n ∧ L^2 ≤ 4096*Sizes.d n*Sizes.p n at hwidth
  have hgap : Sizes.d n*g ≤ Sizes.t n i :=
    axisGap_mul_dimension_le (h.good.lt i).le (h.good.bounds i)
  have hg : 1 ≤ g := by have := h.good.lt i; dsimp only [g]; omega
  have hgeom := Nat.mul_le_mul_left g hwidth.2
  have hdensity := Nat.mul_le_mul_left (4096*Sizes.p n) hgap
  have hwork : g*L^2 ≤ 4096*Sizes.t n i*Sizes.p n := by nlinarith only [hgeom,hdensity]
  have hN : g+1 ≤ 2*g := by omega
  have hphase := Nat.mul_le_mul_right (L^2) hN
  have hH : H ≤ 7*Sizes.t n i := by
    have := h.good.lt i
    dsimp only [H]
    omega
  have hheaders := Nat.mul_le_mul hH hwidth.1
  change (g+1)*L^2+H*L ≤ 10000*Sizes.t n i*Sizes.p n
  nlinarith only [hwork,hphase,hheaders]

/-- Uniform cost of the actual three mask backends, including doubled-band setup. -/
theorem selectedMasks_fast_le :
    ∃ C : ℕ, ∀ (n : ℕ) (h : Sizes.Big n) (i : Fin (Sizes.d n)) (band a b : ℕ),
      band ≤ Sizes.s n i → a ≤ Sizes.s n i → b ≤ Sizes.s n i →
      closedPublicationMaskCost (Sizes.s n i) (Sizes.t n i) band a b+
        closedCouplingSourceMaskCost (Sizes.s n i) (Sizes.t n i) band a b+
        generateRecoveryCouplingMaskCost (Sizes.s n i) (Sizes.t n i) band a b ≤
          C*Sizes.t n i*Sizes.p n := by
  refine ⟨300000014,?_⟩
  intro n h i band a b hband ha hb
  have hc := closedMaskCosts_phase_le (Sizes.s n i) (Sizes.t n i) band a b
  have hr := closedMaskCosts_phase_le (Sizes.s n i) (Sizes.t n i) (2*band) a b
  have hband2 : band ≤ 2*Sizes.s n i := by omega
  have hdouble : 2*band ≤ 2*Sizes.s n i := Nat.mul_le_mul_left 2 hband
  have hb₁ := selectedMaskPhaseBudget_le h i hband2 ha hb
  have hb₂ := selectedMaskPhaseBudget_le h i hdouble ha hb
  have hc' := Nat.mul_le_mul_left 15000 hb₁
  have hr' := Nat.mul_le_mul_left 15000 hb₂
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hbt : band ≤ Sizes.t n i := hband.trans (h.good.lt i).le
  have htp : Sizes.t n i ≤ Sizes.t n i*Sizes.p n := Nat.le_mul_of_pos_right _ (by have := h.thirteen_le_p; omega)
  dsimp only [generateRecoveryCouplingMaskCost]
  nlinarith only [hc,hr,hc',hr',ht,hbt,htp]

end IntegerMultBounds.MathlibTM2.Cost
