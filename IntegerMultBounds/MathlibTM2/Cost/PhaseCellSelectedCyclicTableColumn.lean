module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicTableColumnLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedArbitraryColumn
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicResidual
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicCollection
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableColumnsLoop

/-! Compose all actual column costs at one joint cyclic precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedCyclicTableColumnCost_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a span k j : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → span ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let band := PhaseCellBand.width p u
      let B := cyclicPrincipalBoundary s t band a span
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
      k ≤ B.card → j < s →
      (cyclicTableColumnCost p u (haloInverseRingLog s t) s t a span bits k j : ℝ) ≤ C*(t : ℝ)^5 := by
  obtain ⟨O,hO⟩ := selectedJointCyclicOriginalColumn_poly_le ct
  obtain ⟨R,hR,hres⟩ := selectedCyclicWindowedResidual_poly_le ct
  obtain ⟨A,hA⟩ := selectedJointCyclicCollection_poly_le ct
  obtain ⟨c,hc,hwidths⟩ := selectedInverseBoundaryWidths_le ct
  let cw := 1032+8*ct
  let D := 10000*(c+4)*(cw+c+1)
  refine ⟨O+2*R+A+D,by positivity,?_⟩
  filter_upwards [hres] with n hn
  intro h i _ u target a span k j hu htarget hband ha hspan
  dsimp only
  intro hk hj
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let l := haloInverseRingLog s t
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a span
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  have hbcard : B.card ≤ s := by simpa only [ZMod.card] using B.card_le_univ
  have hleft : a+min span (s-a) ≤ s := by omega
  have hright : span-min span (s-a) ≤ s := by omega
  have ho := (Nat.cast_le (α := ℝ)).mpr (hO n h i u target a span j hu htarget hj hband)
  have hrL := hn h i u target a span a (a+min span (s-a)) hu htarget hband ha hleft
  have hrR := hn h i u target a span 0 (span-min span (s-a)) hu htarget hband (Nat.zero_le _) hright
  have hcol := (Nat.cast_le (α := ℝ)).mpr (hA n h i u target a span a (a+min span (s-a)) k htarget hband ha hleft hk)
  have hw : executionWidth p l (initialSchurTarget p u bits 2) 2 ≤ cw*p :=
    selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have hqw (p l z : ℕ) : executionPrecision p l z 2 ≤ executionWidth p l z 2 := by
    unfold executionPrecision executionWidth; omega
  have hq : q ≤ cw*p := (hqw _ _ _).trans hw
  obtain ⟨_,_,_,_,hV,_,_⟩ := hwidths n h i u target 0 0 htarget hband
  have hd := (Nat.cast_le (α := ℝ)).mpr (selectedCyclicColumnControls_poly_le cw c h i q _ band k j
    hq hV hband (hk.trans hbcard) (Nat.le_of_lt hj))
  have hb := (Nat.cast_le (α := ℝ)).mpr (cyclicTableColumnCost_le_components p u l s t a span bits k j)
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [t]; omega
  have hp3 := (Nat.cast_le (α := ℝ)).mpr (Nat.pow_le_pow_right ht (by decide : 3 ≤ 5))
  have hp2 := (Nat.cast_le (α := ℝ)).mpr (Nat.pow_le_pow_right ht (by decide : 2 ≤ 5))
  have hs3 := mul_le_mul_of_nonneg_left hp3 (Nat.cast_nonneg A : (0 : ℝ) ≤ A)
  have hs2 := mul_le_mul_of_nonneg_left hp2 (Nat.cast_nonneg D : (0 : ℝ) ≤ D)
  dsimp only [p,s,t,l,band,B,bits,q,D,cw] at ho hrL hrR hcol hb hd hs2 hs3 ⊢
  push_cast at ho hcol hb hd hs2 hs3 ⊢
  nlinarith only [ho,hrL,hrR,hcol,hb,hd,hs2,hs3]

theorem selectedCyclicTableColumnsLoopCost_poly_le (ct : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)),
      ∀ [NeZero (Sizes.s n i)], ∀ u target a span : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → a ≤ Sizes.s n i → span ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
      (cyclicTableColumnsLoopCost p u (haloInverseRingLog s t) s t a span bits : ℝ) ≤ C*(t : ℝ)^6 := by
  obtain ⟨C,hC,hcolumn⟩ := selectedCyclicTableColumnCost_poly_le ct
  refine ⟨C+10,by positivity,?_⟩
  filter_upwards [hcolumn] with n hn
  intro h i _ u target a span hu htarget hband ha hspan
  dsimp only
  let p := Sizes.p n
  let s := Sizes.s n i
  let t := Sizes.t n i
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span
  let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
  have hB : B.card ≤ t := by
    have hb : B.card ≤ s := by simpa only [ZMod.card] using B.card_le_univ
    exact hb.trans (h.good.lt i).le
  have hsum := Finset.sum_le_sum (s := Finset.range B.card)
    (f := fun k => (cyclicTableColumnCost p u (haloInverseRingLog s t) s t a span bits k (bFoldAt s B k).val : ℝ)+1+3)
    (g := fun _ => C*(t : ℝ)^5+4) (by
      intro k hk
      have hc := hn h i u target a span k (bFoldAt s B k).val hu htarget hband ha hspan
        (Nat.le_of_lt (Finset.mem_range.mp hk)) (bFoldAt s B k).val_lt
      linarith only [hc])
  simp only [Finset.sum_const,Finset.card_range,nsmul_eq_mul] at hsum
  have hbR := (Nat.cast_le (α := ℝ)).mpr hB
  have hmul := mul_le_mul_of_nonneg_right hbR (by positivity : 0 ≤ C*(t : ℝ)^5+4)
  have ht : 1 ≤ t := by have := h.good.lt i; dsimp [t]; omega
  have hp := (Nat.cast_le (α := ℝ)).mpr (Nat.le_self_pow (by decide : 6 ≠ 0) t)
  have hone := (Nat.cast_le (α := ℝ)).mpr (Nat.one_le_pow 6 t ht)
  unfold cyclicTableColumnsLoopCost
  push_cast at hp hone ⊢
  change _ ≤ (C+10)*(t : ℝ)^6
  nlinarith only [hsum,hmul,hbR,hp,hone]

end IntegerMultBounds.MathlibTM2.Cost
