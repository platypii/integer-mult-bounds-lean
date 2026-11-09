module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicColumnsWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedOriginalColumnWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedUniformResidualWorkspace

/-! The actual complete Schur-column construction fits selected shared volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem selectedPreparedCyclicColumnsWorkspace_le (J R K rowPush cw : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ u target a n : ℕ,
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      executionWidth p l (initialSchurTarget p u target 2) 2 ≤ cw*p →
      u ≤ p → PhaseCellBand.width p u ≤ s → a ≤ s → n ≤ s →
      preparedCyclicColumnsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J R K rowPush p l s t u target a n ≤ 9*Sizes.T m := by
  let C := cw+20
  filter_upwards [selectedOriginalColumnUniformWorkspace_le (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush cw 1,
    selectedInteriorResidualUniformWorkspace_le (P₀ := P₀) (Q := Q) (A := A) (U := U) J R K rowPush cw,
    selectedAxisPolynomial_le_volume (5000000*C^3) 3 3] with m hc hr hv
  intro h i _ u target a n
  dsimp only
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let w := executionWidth p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let Z := C*t*p
  intro hw hu hb ha hn
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hst : s < t := h.good.lt i
  have hC : 1 ≤ C := by dsimp only [C]; omega
  have hZ : 1 ≤ Z := Nat.mul_pos (Nat.mul_pos hC ht) hp
  have htZ : t ≤ Z := by
    have h₁ := Nat.mul_le_mul_right t hC
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; nlinarith only [h₁,h₂]
  have hwidth : w = 2*q+8 := by dsimp only [w,q,executionWidth,executionPrecision]; omega
  have hqW : q ≤ w := by omega
  have hwZ : w ≤ Z := by
    have h₁ := Nat.mul_le_mul_right p (show cw ≤ C by dsimp only [C]; omega)
    have h₂ := Nat.mul_le_mul_left (C*p) ht
    dsimp only [Z]; nlinarith only [hw,h₁,h₂]
  have hbandT : band ≤ t := hb.trans hst.le
  have hgeom : publicationGeometryWidth t band ≤ 13*t := by
    have hsizeT : Nat.size t ≤ t := Nat.size_le.mpr Nat.lt_two_pow_self
    have hsizeB : Nat.size band ≤ band := Nat.size_le.mpr Nat.lt_two_pow_self
    unfold publicationGeometryWidth
    omega
  have hVZ : publicationGeometryWidth t band ≤ Z := by
    have h₁ := Nat.mul_le_mul_right t (show 13 ≤ C by dsimp only [C]; omega)
    have h₂ := Nat.mul_le_mul_left (C*t) hp
    dsimp only [Z]; nlinarith only [hgeom,h₁,h₂]
  have hcomponents := preparedCyclicColumnsWorkspace_le_components (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J R K rowPush p l s t u target a n Z hst ha hn hZ (hst.le.trans htZ) (hqW.trans hwZ)
    (hb.trans (hst.le.trans htZ)) hVZ
  have hcolumn := hc h i q u (by rw [←hwidth]; exact hw) hu hb
  have hresidual := hr h i u (initialSchurTarget p u target 2) 2 hw hu hb
  simp only [one_mul] at hcolumn
  have hvolume := hv i
  have heq : 5000000*Z^3 = (5000000*C^3)*t^3*p^3 := by dsimp only [Z]; ring
  have hcontrols : 5000000*Z^3 ≤ Sizes.T m := by rw [heq]; exact hvolume
  nlinarith only [hcomponents,hcolumn,hresidual,hcontrols]

end IntegerMultBounds.MathlibTM2.Cost
