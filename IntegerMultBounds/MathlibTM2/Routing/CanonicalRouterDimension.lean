module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRouterSupplier

/-! Polynomial bounds for the actual address-dimension setup ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

/-- Terminal setup over arbitrary fixed tape counts. -/
def terminalDimensionBudget (T tapes n L rowLength count : ℕ) : ℕ :=
  (L * (4 * n + 11) + 22 * n + 6 * rowLength + 46) +
    ((11 * (n + rowLength) + 10 * n + 24) +
      (count * ((elementaryCompileBase n L 0 rowLength +
        7 * (rowLength + 3 * n + 11) + 4 * L + 6) +
        (4 * T + 12 * tapes + 60) + 2 + (12 * tapes + 22) * (rowLength + 3 * n + 11)) + 10) +
      (4 * n + 9)) + (6 * n + 2 * rowLength + 7)

theorem canonicalTerminalPrice_dimension_eq (n L rowLength count : ℕ) :
    canonicalTerminalPrice n 0 0 L 0 rowLength count =
      (terminalDimensionBudget canonicalTerminalT (swapT 6) n L rowLength count : ℕ) := by
  unfold canonicalTerminalPrice canonicalTerminalBaseCost terminalDimensionBudget
  simp only [Nat.zero_mul, Nat.mul_zero, Nat.add_zero, Nat.zero_add,
    Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.cast_zero]
  ring

/-- A cubic majorant proved before instantiating any concrete machine bank. -/
theorem terminalDimensionBudget_le_cube (T tapes n L rowLength count x : ℕ)
    (hn : n ≤ x) (hL : L ≤ x) (hr : rowLength ≤ x) (hc : count ≤ x) (hx : 1 ≤ x) :
    terminalDimensionBudget T tapes n L rowLength count ≤ (1482 + 4 * T + 192 * tapes) * x ^ 3 := by
  have hm : terminalDimensionBudget T tapes n L rowLength count ≤
      terminalDimensionBudget T tapes x x x x := by
    unfold terminalDimensionBudget elementaryCompileBase elementaryCompilerPrepareBound
    gcongr
  have he : terminalDimensionBudget T tapes x x x x =
      20 * x ^ 3 + (429 + 48 * tapes) * x ^ 2 + (937 + 4 * T + 144 * tapes) * x + 96 := by
    unfold terminalDimensionBudget elementaryCompileBase elementaryCompilerPrepareBound
    ring
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
  have hx1 : x ≤ x ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by decide : 1 ≤ 3)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have h₂ := Nat.mul_le_mul_left (429 + 48 * tapes) hx2
  have h₁ := Nat.mul_le_mul_left (937 + 4 * T + 144 * tapes) hx1
  have h₀ := Nat.mul_le_mul_left 96 hx0
  rw [he] at hm
  nlinarith only [hm, h₂, h₁, h₀]

def canonicalTerminalDimensionCoefficient : ℕ :=
  (1482 + 4 * canonicalTerminalT + 192 * swapT 6) * 1310 ^ 3

/-- The actual canonical terminal setup is cubic in address dimension. -/
theorem canonicalTerminalDimension_polynomial (n : ℕ) :
    canonicalTerminalPrice n 0 0 (canonicalScalarWidth n) 0 1 (131 * canonicalRouterGap n) ≤
      (canonicalTerminalDimensionCoefficient * (n + 1) ^ 3 : ℕ) := by
  have hl := canonicalScalarWidth_le_self n
  have hg := canonicalScalarWidth_le_self (n + 1)
  change Nat.clog 2 (n + 2) ≤ n + 1 at hg
  have hcount : 131 * canonicalRouterGap n ≤ 1310 * (n + 1) := by
    unfold canonicalRouterGap
    omega
  have hb := terminalDimensionBudget_le_cube canonicalTerminalT (swapT 6) n (canonicalScalarWidth n)
    1 (131 * canonicalRouterGap n) (1310 * (n + 1)) (by omega) (by omega)
    (by omega) hcount (by omega)
  have scale (C x : ℕ) : C * (1310 * x) ^ 3 = (C * 1310 ^ 3) * x ^ 3 := by ring
  rw [scale] at hb
  have hs : terminalDimensionBudget canonicalTerminalT (swapT 6) n (canonicalScalarWidth n) 1
      (131 * canonicalRouterGap n) ≤ canonicalTerminalDimensionCoefficient * (n + 1) ^ 3 := by
    exact hb
  rw [canonicalTerminalPrice_dimension_eq]
  exact Nat.cast_le.mpr hs

theorem canonicalRouterUniformMetadataWidth_polynomial (n : ℕ) :
    canonicalRouterUniformMetadataWidth n 1 0 ≤ 64 * (n + 1) ^ 2 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hL := canonicalScalarWidth_le_self n
  have hW := canonicalScalarWidth_le_self (2 * D)
  have hm := Nat.mul_le_mul_left (2 * n) hD
  have hzero : canonicalScalarWidth 0 = 0 := by decide
  have hone : canonicalScalarWidth 1 = 1 := by decide
  unfold canonicalRouterUniformMetadataWidth
  rw [hone, hone, hzero]
  change 2 * n + n * (2 * D + 3) + 9 * canonicalScalarWidth n +
    3 * 1 + 3 * 0 + 2 * 1 + 7 * D + canonicalScalarWidth (2 * D) + Nat.log2 1 + 1 ≤ _
  have hlog : Nat.log2 1 = 0 := by decide
  rw [hlog]
  nlinarith only [hL, hW, hm, hD]

theorem canonicalRouterUniformFrameWidth_polynomial (n : ℕ) :
    canonicalRouterUniformFrameWidth n 1 0 ≤
      (257 * originalMatchingScheduleT 6) * (n + 1) ^ 2 := by
  have hmeta := canonicalRouterUniformMetadataWidth_polynomial n
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hwidth := canonicalScalarWidth_le_self (n * (4 * D + 2))
  have hm := Nat.mul_le_mul_left (12 * n) hD
  have hb : canonicalRouterUniformMetadataWidth n 1 0 + canonicalScalarWidth (n * (4 * D + 2)) +
      2 * n * (4 * D + 2) + 26 * D + 13 ≤ 257 * (n + 1) ^ 2 := by
    nlinarith only [hmeta, hwidth, hm, hD]
  have h := Nat.mul_le_mul_left (originalMatchingScheduleT 6) hb
  have scale (T x : ℕ) : T * (257 * x ^ 2) = (257 * T) * x ^ 2 := by ring
  rw [scale] at h
  exact h

/-- The complete outer directional frame is cubic in address dimension. -/
theorem canonicalDirectionalUniformFrameBudget_polynomial (n : ℕ) :
    canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1 (canonicalRouterStride n) ≤
      ((canonicalRouterCommonT + 3) * (4096 + 200000 * originalMatchingScheduleT 6)) * (n + 1) ^ 3 := by
  let x := n + 1
  have hx : 1 ≤ x := by dsimp only [x]; omega
  have hL : canonicalScalarWidth n ≤ x := (canonicalScalarWidth_le_self n).trans (by omega)
  have hg := canonicalScalarWidth_le_self (n + 1)
  change Nat.clog 2 (n + 2) ≤ n + 1 at hg
  have hgap : canonicalRouterGap n ≤ 10 * x := by
    unfold canonicalRouterGap
    dsimp only [x]
    omega
  have hcount : canonicalRouterStride n ≤ 640 * x := by
    unfold canonicalRouterStride
    omega
  have hf := canonicalRouterUniformFrameWidth_polynomial n
  have hframes := Nat.mul_le_mul hcount hf
  have hcoords := Nat.mul_le_mul (Nat.mul_le_mul_left 131 hgap)
    (show 2 * canonicalScalarWidth n + 2 ≤ 2 * x by
      have hl := canonicalScalarWidth_le_self n
      dsimp only [x]
      omega)
  have bound (n L gap count frame T x : ℕ) (hx : 1 ≤ x) (hL : L ≤ x)
      (hf : count * frame ≤ (640 * x) * ((257 * T) * x ^ 2))
      (hc : (131 * gap) * (2 * L + 2) ≤ (131 * (10 * x)) * (2 * x)) :
      L + 0 + 1 + (131 * gap) * (2 * L + 2) + count * frame + 1 ≤
        (4096 + 200000 * T) * x ^ 3 := by
    have hx1 : x ≤ x ^ 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by decide : 1 ≤ 3)
    have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
    have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
    nlinarith only [hf, hc, hL, hx1, hx2, hx0, Nat.zero_le (T * x ^ 3)]
  have hb := bound n (canonicalScalarWidth n) (canonicalRouterGap n) (canonicalRouterStride n)
    (canonicalRouterUniformFrameWidth n 1 0) (originalMatchingScheduleT 6) x hx hL hframes hcoords
  have h := Nat.mul_le_mul_left (canonicalRouterCommonT + 3) hb
  have scale (a b x : ℕ) : a * (b * x ^ 3) = (a * b) * x ^ 3 := by ring
  rw [scale] at h
  exact h

theorem matchingFullProfileProductionBound_le_cube (N L Lk Lc x : ℕ)
    (hN : N ≤ x) (hL : L ≤ x) (hk : Lk ≤ x) (hc : Lc ≤ x) (hx : 1 ≤ x) :
    matchingFullProfileProductionBound N L Lk Lc ≤ 440 * x ^ 3 := by
  have hm : matchingFullProfileProductionBound N L Lk Lc ≤ matchingFullProfileProductionBound x x x x := by
    unfold matchingFullProfileProductionBound binaryPrefixExtractCost residueDispatchCost
    gcongr
  have he : matchingFullProfileProductionBound x x x x =
      20 * x ^ 3 + 181 * x ^ 2 + 205 * x + 34 := by
    unfold matchingFullProfileProductionBound binaryPrefixExtractCost residueDispatchCost
    ring
  have hx1 : x ≤ x ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by decide : 1 ≤ 3)
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  rw [he] at hm
  nlinarith only [hm, hx1, hx2, hx0]

theorem canonicalMatchingProfileProduction_polynomial (n : ℕ) :
    let D := Nat.clog 2 (4 * n + 2) + 1
    matchingFullProfileProductionBound n (2 * D) D (canonicalScalarWidth (n * (4 * D + 2))) ≤
      (440 * 18 ^ 3) * (n + 1) ^ 6 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hwidth := canonicalScalarWidth_le_self (n * (4 * D + 2))
  have hm := Nat.mul_le_mul_left (4 * n) hD
  have hc : canonicalScalarWidth (n * (4 * D + 2)) ≤ 18 * (n + 1) ^ 2 := by
    nlinarith only [hwidth, hm, Nat.zero_le n]
  have hb := matchingFullProfileProductionBound_le_cube n (2 * D) D _ (18 * (n + 1) ^ 2)
    (by nlinarith) (by nlinarith [hD]) (by nlinarith [hD]) hc (by nlinarith)
  have scale (x : ℕ) : 440 * (18 * x ^ 2) ^ 3 = (440 * 18 ^ 3) * x ^ 6 := by ring
  rw [scale] at hb
  exact hb

theorem reservoirClassLocalTableCost_le_cube (n L x : ℕ)
    (hn : n ≤ x) (hL : L ≤ x) (hx : 1 ≤ x) :
    reservoirClassLocalTableCost n 0 L ≤ 1843 * x ^ 3 := by
  have hm : reservoirClassLocalTableCost n 0 L ≤ reservoirClassLocalTableCost x 0 x := by
    unfold reservoirClassLocalTableCost
    simp only [Nat.mul_zero, Nat.sub_zero]
    gcongr
  have he : reservoirClassLocalTableCost x 0 x = 30 * x ^ 3 + 793 * x ^ 2 + 966 * x + 54 := by
    unfold reservoirClassLocalTableCost
    simp only [Nat.mul_zero, Nat.sub_zero]
    ring
  have hx1 : x ≤ x ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (by omega : 0 < x) (by decide : 1 ≤ 3)
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 3)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  rw [he] at hm
  nlinarith only [hm, hx1, hx2, hx0]

theorem canonicalReservoirTableCost_polynomial (n : ℕ) :
    let D := Nat.clog 2 (4 * n + 2) + 1
    reservoirClassLocalTableCost n 0 (2 * D) ≤ (1843 * 8 ^ 3) * (n + 1) ^ 3 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hb := reservoirClassLocalTableCost_le_cube n (2 * D) (8 * (n + 1))
    (by omega) (by omega) (by omega)
  have scale (x : ℕ) : 1843 * (8 * x) ^ 3 = (1843 * 8 ^ 3) * x ^ 3 := by ring
  rw [scale] at hb
  exact hb

def canonicalRouterOriginalSetupCoefficient : ℕ := 1843 * 8 ^ 3 + 440 * 18 ^ 3 + 200

/-- Table conversion, profile production and copied metadata together have a
fixed degree-six majorant. -/
theorem canonicalRouterOriginalSetupBudget_polynomial (n : ℕ) :
    canonicalRouterOriginalSetupBudget n 1 0 ≤ canonicalRouterOriginalSetupCoefficient * (n + 1) ^ 6 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hslot : n * (4 * D + 2) ≤ 18 * (n + 1) ^ 2 := by
    have hm := Nat.mul_le_mul_left (4 * n) hD
    nlinarith only [hm, Nat.zero_le n]
  have hr := canonicalReservoirTableCost_polynomial n
  have hm := canonicalMatchingProfileProduction_polynomial n
  have hmeta := canonicalRouterUniformMetadataWidth_polynomial n
  have hx3 : (n + 1) ^ 3 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 6)
  have hx2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 6)
  have hx0 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (by omega)
  dsimp only at hr hm
  dsimp only [canonicalRouterOriginalSetupBudget]
  unfold canonicalRouterOriginalSetupCoefficient
  change reservoirClassLocalTableCost n 0 (2 * D) +
    (matchingFullProfileProductionBound n (2 * D) D (canonicalScalarWidth (n * (4 * D + 2))) +
      2 * canonicalRouterUniformMetadataWidth n 1 0 + 2) +
    (2 * (n * (4 * D + 2)) + 2) ≤ _
  nlinarith only [hr, hm, hmeta, hslot, hx3, hx2, hx0]

def stageSetupCoefficient (T C : ℕ) : ℕ := C + 1544 * T + 2

def canonicalRouterStageSetupCoefficient : ℕ :=
  stageSetupCoefficient (originalMatchingScheduleT 6) canonicalRouterOriginalSetupCoefficient

private theorem stage_setup_bound (o f T C X : ℕ) (ho : o ≤ C * X) (hf : f ≤ 257 * T * X) (hx : 1 ≤ X) :
    o + (6 * f + 2 * T + 2) ≤ stageSetupCoefficient T C * X := by
  unfold stageSetupCoefficient
  have hc := Nat.mul_le_mul_left (2 * T + 2) hx
  linarith only [ho, hf, hc]

theorem canonicalRouterStageSetupBudget_polynomial (n : ℕ) :
    canonicalRouterStageSetupBudget n 1 0 ≤ canonicalRouterStageSetupCoefficient * (n + 1) ^ 6 := by
  have ho := canonicalRouterOriginalSetupBudget_polynomial n
  have hf := canonicalRouterUniformFrameWidth_polynomial n
  have hx2 : (n + 1) ^ 2 ≤ (n + 1) ^ 6 := Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by decide : 2 ≤ 6)
  have hx0 : 1 ≤ (n + 1) ^ 6 := Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le n))
  have hf' := hf.trans (Nat.mul_le_mul_left (257 * originalMatchingScheduleT 6) hx2)
  dsimp only [canonicalRouterStageSetupBudget, canonicalRouterStageSetupCoefficient]
  exact stage_setup_bound (canonicalRouterOriginalSetupBudget n 1 0) (canonicalRouterUniformFrameWidth n 1 0)
    (originalMatchingScheduleT 6) canonicalRouterOriginalSetupCoefficient ((n + 1) ^ 6) ho hf' hx0

def canonicalDirectionalFrameCoefficient : ℕ :=
  (canonicalRouterCommonT + 3) * (4096 + 200000 * originalMatchingScheduleT 6)

def directionalSetupCoefficient (stageC frameC outerC tapes : ℕ) : ℕ :=
  640 * (stageC + 2 * frameC + 2) + 6 * outerC + 2 * (tapes + 3) + 6

def canonicalRouterDirectionalSetupCoefficient : ℕ :=
  directionalSetupCoefficient canonicalRouterStageSetupCoefficient (257 * originalMatchingScheduleT 6)
    canonicalDirectionalFrameCoefficient canonicalRouterCommonT

private theorem directional_setup_bound (stage frame outer count tapes stageC frameC outerC x : ℕ)
    (hs : stage ≤ stageC * x ^ 6) (hf : frame ≤ frameC * x ^ 2)
    (ho : outer ≤ outerC * x ^ 3) (hc : count ≤ 640 * x) (hx : 1 ≤ x) :
    count * (stage + 2 + 2 * frame) + 4 + 6 * outer + 2 * (tapes + 3) + 2 ≤
      directionalSetupCoefficient stageC frameC outerC tapes * x ^ 7 := by
  unfold directionalSetupCoefficient
  have hx2 : x ^ 2 ≤ x ^ 6 := Nat.pow_le_pow_right (by omega) (by decide : 2 ≤ 6)
  have hx3 : x ^ 3 ≤ x ^ 7 := Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 7)
  have hx0 : 1 ≤ x ^ 6 := Nat.one_le_pow _ _ hx
  have hx7 : 1 ≤ x ^ 7 := Nat.one_le_pow _ _ hx
  have hf' := hf.trans (Nat.mul_le_mul_left frameC hx2)
  have hi : stage + 2 + 2 * frame ≤ (stageC + 2 * frameC + 2) * x ^ 6 := by
    linarith only [hs, hf', hx0]
  have hm := Nat.mul_le_mul hc hi
  have scale (C x : ℕ) : (640 * x) * (C * x ^ 6) = (640 * C) * x ^ 7 := by ring
  rw [scale] at hm
  have ho' := ho.trans (Nat.mul_le_mul_left outerC hx3)
  have hfixed := Nat.mul_le_mul_left (2 * (tapes + 3) + 6) hx7
  linarith only [hm, ho', hfixed]

private theorem stride_linear_bound (n q : ℕ) (hq : q ≤ n + 1) :
    64 * (6 + 4 * q) ≤ 640 * (n + 1) := by omega

theorem canonicalRouterDirectionalSetupBudget_polynomial (n : ℕ) :
    canonicalRouterDirectionalSetupBudget n 1 0 (canonicalScalarWidth n) 0 1 (canonicalRouterStride n) ≤
      canonicalRouterDirectionalSetupCoefficient * (n + 1) ^ 7 := by
  have hs := canonicalRouterStageSetupBudget_polynomial n
  have hf := canonicalRouterUniformFrameWidth_polynomial n
  have ho : canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1
      (canonicalRouterStride n) ≤ canonicalDirectionalFrameCoefficient * (n + 1) ^ 3 :=
    canonicalDirectionalUniformFrameBudget_polynomial n
  have hg := canonicalScalarWidth_le_self (n + 1)
  change Nat.clog 2 (n + 2) ≤ n + 1 at hg
  have hc : canonicalRouterStride n ≤ 640 * (n + 1) :=
    stride_linear_bound n (Nat.clog 2 (n + 2)) hg
  dsimp only [canonicalRouterDirectionalSetupBudget, canonicalRouterDirectionalSetupCoefficient]
  exact directional_setup_bound (canonicalRouterStageSetupBudget n 1 0)
    (canonicalRouterUniformFrameWidth n 1 0)
    (canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1 (canonicalRouterStride n))
    (canonicalRouterStride n) canonicalRouterCommonT canonicalRouterStageSetupCoefficient
    (257 * originalMatchingScheduleT 6) canonicalDirectionalFrameCoefficient (n + 1) hs hf ho hc (Nat.succ_le_succ (Nat.zero_le n))

/-- Scalar setup for both classifier placements, with fixed banks abstracted. -/
def placementDimensionBudget (T tapes n L : ℕ) : ℕ :=
  36 * L * n + 222 * n + 447 * L + 1549 + 6 * T + 18 * tapes

def placementDimensionCoefficient (T tapes : ℕ) : ℕ := 2254 + 6 * T + 18 * tapes

private theorem placementDimensionBudget_le_square (T tapes n L x : ℕ)
    (hn : n ≤ x) (hL : L ≤ x) (hx : 1 ≤ x) :
    placementDimensionBudget T tapes n L ≤ placementDimensionCoefficient T tapes * x ^ 2 := by
  have hprod := Nat.mul_le_mul hL hn
  have hx1 : x ≤ x ^ 2 := by nlinarith only [hx]
  have hx0 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  have hfixed := Nat.mul_le_mul_left (1549 + 6 * T + 18 * tapes) hx0
  unfold placementDimensionBudget placementDimensionCoefficient
  nlinarith only [hprod, hn, hL, hx1, hfixed]

theorem canonicalRouterPlacementDimensionOverhead_eq (n : ℕ) :
    canonicalRouterPlacementDimensionOverhead n 1 =
      placementDimensionBudget (inactiveClassifierPlacementT 6) (swapT 6) n (canonicalScalarWidth n) := by
  unfold canonicalRouterPlacementDimensionOverhead generatedExchangeUniformOverhead placementDimensionBudget
  have hlog : Nat.log2 1 = 0 := by decide
  simp only [hlog, zero_add, mul_zero, add_zero]
  generalize inactiveClassifierPlacementT 6 = T
  generalize swapT 6 = tapes
  ring

theorem canonicalRouterPlacementDimensionOverhead_polynomial (n : ℕ) :
    canonicalRouterPlacementDimensionOverhead n 1 ≤
      placementDimensionCoefficient (inactiveClassifierPlacementT 6) (swapT 6) * (n + 1) ^ 2 := by
  rw [canonicalRouterPlacementDimensionOverhead_eq]
  exact placementDimensionBudget_le_square _ _ _ _ _ (Nat.le_succ n)
    ((canonicalScalarWidth_le_self n).trans (Nat.le_succ n)) (Nat.succ_le_succ (Nat.zero_le n))

/-- Profile construction is polynomial uniformly in physical coordinates and widths. -/
theorem liveCoordinateProfilesCost_uniform_cube (x : ℕ) (hx : 1 ≤ x) :
    liveCoordinateProfilesCost ⟨x, x, x, x, x⟩ ⟨x, x, x, x, x⟩ ≤ 10000 * x ^ 3 := by
  have hx1 : x ≤ x ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by decide : 1 ≤ 3)
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx (by decide : 2 ≤ 3)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  unfold liveCoordinateProfilesCost livePreparedCoordinateSourceCost liveSelectedProfilesCost
    repairControlProfilesCost repairTemporaryProfilesCost repairYZProfilesCost liveYZSourceBatchCost
    binaryCounterSourceGenerateCost binaryAffineSourceGenerateCost binaryInactiveProfileCost
    optionalAffineSourceGroupIterationCost binaryWordRepeatCost
    sourceCoordinateIterationCost sourceCoordinateRecordCost gatedSelectedSourceIterationCost
    sharedSelectedSourceIterationCost gatedSelectedSourceFrameCost selectedSourceFrameCost
    optionalAffineSourceIterationCost optionalAffineSourceFrameCost optionalBinaryProfileFrameCost
    affineSourceIterationCost affineSourceFrameCost counterSourceIterationCost
    LiveDescriptorWidths.coordinateBits IntegerMultBounds.MathlibTM2.Layer.CompactGadget.Par.wc
  simp only [max_def]
  split_ifs <;> nlinarith only [hx1, hx2, hx0]

theorem canonicalCoordinateProfilesCost_polynomial (n : ℕ) :
    let D := Nat.clog 2 (4 * n + 2) + 1
    let w : LiveDescriptorWidths := ⟨D, D, D, 2 * D, canonicalScalarWidth (2 * D)⟩
    let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
    liveCoordinateProfilesCost q w ≤ (10000 * 10 ^ 3) * (n + 1) ^ 3 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  let w : LiveDescriptorWidths := ⟨D, D, D, 2 * D, canonicalScalarWidth (2 * D)⟩
  let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
  let x := 10 * (n + 1)
  have hn : n ≤ x := by dsimp only [x]; omega
  have hg : canonicalRouterGap n ≤ x := by
    have h := canonicalScalarWidth_le_self (n + 1)
    change Nat.clog 2 (n + 2) ≤ n + 1 at h
    dsimp only [canonicalRouterGap, x]
    omega
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hd : D ≤ x := by dsimp only [x]; omega
  have hs : 2 * D ≤ x := by dsimp only [x]; omega
  have hw : canonicalScalarWidth (2 * D) ≤ x := (canonicalScalarWidth_le_self _).trans hs
  have hp := liveCoordinateProfilesCost_mono q (⟨x, x, x, x, x⟩ : Par) w hn hg
    (Nat.mul_le_mul hn hg)
  have hb := liveCoordinateProfilesCost_widths_mono (⟨x, x, x, x, x⟩ : Par) w
    (⟨x, x, x, x, x⟩ : LiveDescriptorWidths) hd hd hd hs hw
  have hu := liveCoordinateProfilesCost_uniform_cube x (by dsimp only [x]; omega)
  have scale (x : ℕ) : 10000 * (10 * x) ^ 3 = (10000 * 10 ^ 3) * x ^ 3 := by ring
  exact (hp.trans hb).trans (by simpa only [x, scale] using hu)

theorem uniformBackendBudget_le_cube (n slots Li Lg Lk Ls Lw x : ℕ)
    (hn : n ≤ x) (hm : slots ≤ x) (hi : Li ≤ x) (hg : Lg ≤ x)
    (hk : Lk ≤ x) (hs : Ls ≤ x) (hw : Lw ≤ x) (hx : 1 ≤ x) :
    LiveDescriptorMode.uniformBackendBudget n slots Li Lg Lk Ls Lw ≤ 10000 * x ^ 3 := by
  have hmono : LiveDescriptorMode.uniformBackendBudget n slots Li Lg Lk Ls Lw ≤
      LiveDescriptorMode.uniformBackendBudget x x x x x x x := by
    unfold LiveDescriptorMode.uniformBackendBudget affineProfileDescriptorBound groupedProfileDescriptorBound
      affineProfileClosedCost affineProfileCallCost groupedProfileCallCost binaryGroupedPositionCost
      descriptorCompileCallCost
    gcongr
  have hbound : LiveDescriptorMode.uniformBackendBudget x x x x x x x ≤ 10000 * x ^ 3 := by
    have hx1 : x ≤ x ^ 3 := by
      simpa only [pow_one] using Nat.pow_le_pow_right hx (by decide : 1 ≤ 3)
    have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx (by decide : 2 ≤ 3)
    have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
    unfold LiveDescriptorMode.uniformBackendBudget affineProfileDescriptorBound groupedProfileDescriptorBound
      affineProfileClosedCost affineProfileCallCost groupedProfileCallCost binaryGroupedPositionCost
      descriptorCompileCallCost
    nlinarith only [hx1, hx2, hx0]
  exact hmono.trans hbound

theorem canonicalLiveRepairOverhead_polynomial (n : ℕ) :
    let D := Nat.clog 2 (4 * n + 2) + 1
    let L := canonicalScalarWidth n
    liveRepairUniformOverhead n 1 0 0 0 (L + 1) (n + 1) 0 (L + 1)
      ⟨D, D, D, 2 * D, canonicalScalarWidth (2 * D)⟩ ≤ 60000000 * (n + 1) ^ 3 := by
  let D := Nat.clog 2 (4 * n + 2) + 1
  let L := canonicalScalarWidth n
  have hD : D ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    dsimp only [D]
    omega
  have hL : L ≤ n + 1 := (canonicalScalarWidth_le_self n).trans (Nat.le_succ n)
  have hw := canonicalScalarWidth_le_self (2 * D)
  have hb := uniformBackendBudget_le_cube n n D D D (2 * D) (canonicalScalarWidth (2 * D))
    (8 * (n + 1)) (by omega) (by omega) (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega)
  have scale (x : ℕ) : 10000 * (8 * x) ^ 3 = (10000 * 8 ^ 3) * x ^ 3 := by ring
  rw [scale] at hb
  have hx1 : n + 1 ≤ (n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by decide : 1 ≤ 3)
  have hx2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by decide : 2 ≤ 3)
  have hx0 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le n))
  dsimp only
  unfold liveRepairUniformOverhead LiveDescriptorWidths.coordinateBits
  simp only [zero_mul, add_zero]
  dsimp only [D, L] at hb hD hL
  nlinarith only [hb, hL, hD, hx1, hx2, hx0]

private theorem binaryMaskCosts_le_square (n L x : ℕ) (hn : n ≤ x) (hL : L ≤ x) (hx : 1 ≤ x) :
    binaryTemporaryMaskUniformCost n L L L L + binaryPhaseMaskUniformCost n L L L L ≤ 1000 * x ^ 2 := by
  have hm : binaryTemporaryMaskUniformCost n L L L L + binaryPhaseMaskUniformCost n L L L L ≤
      binaryTemporaryMaskUniformCost x x x x x + binaryPhaseMaskUniformCost x x x x x := by
    unfold binaryTemporaryMaskUniformCost binaryPhaseMaskUniformCost binaryWordRepeatCost
    gcongr
  have hx1 : x ≤ x ^ 2 := by nlinarith only [hx]
  have hx0 : 1 ≤ x ^ 2 := Nat.one_le_pow _ _ hx
  unfold binaryTemporaryMaskUniformCost binaryPhaseMaskUniformCost binaryWordRepeatCost at hm ⊢
  nlinarith only [hm, hx1, hx0]

theorem canonicalRouterGeneratedScalarOverhead_polynomial (n : ℕ) :
    canonicalRouterGeneratedScalarOverhead n 1 0 0 ≤ 71000000 * (n + 1) ^ 3 := by
  have hp := canonicalCoordinateProfilesCost_polynomial n
  have hr := canonicalLiveRepairOverhead_polynomial n
  have hm := binaryMaskCosts_le_square n (canonicalScalarWidth n) (n + 1) (Nat.le_succ n)
    ((canonicalScalarWidth_le_self n).trans (Nat.le_succ n)) (Nat.succ_le_succ (Nat.zero_le n))
  have hL := canonicalScalarWidth_le_self n
  have hD : Nat.clog 2 (4 * n + 2) + 1 ≤ 4 * (n + 1) := by
    have h := canonicalScalarWidth_le_self (4 * n + 1)
    change Nat.clog 2 (4 * n + 2) ≤ 4 * n + 1 at h
    omega
  have hx2 : (n + 1) ^ 2 ≤ (n + 1) ^ 3 :=
    Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by decide : 2 ≤ 3)
  have hx1 : n + 1 ≤ (n + 1) ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right (Nat.succ_le_succ (Nat.zero_le n)) (by decide : 1 ≤ 3)
  have hx0 : 1 ≤ (n + 1) ^ 3 := Nat.one_le_pow _ _ (Nat.succ_le_succ (Nat.zero_le n))
  have hzero : canonicalScalarWidth 0 = 0 := by decide
  have hone : canonicalScalarWidth 1 = 1 := by decide
  dsimp only at hp hr
  dsimp only [canonicalRouterGeneratedScalarOverhead]
  rw [hone, hone, hzero]
  simp only [add_zero, mul_zero, zero_add]
  nlinarith only [hp, hr, hm, hL, hD, hx2, hx1, hx0]

def stageDimensionCoefficient (placementC : ℕ) : ℕ := 71002920 + 2 * placementC

def canonicalRouterStageDimensionCoefficient : ℕ :=
  stageDimensionCoefficient (placementDimensionCoefficient (inactiveClassifierPlacementT 6) (swapT 6))

private theorem stage_dimension_bound (generated placement n L placementC x : ℕ)
    (hg : generated ≤ 71000000 * x ^ 3) (hp : placement ≤ placementC * x ^ 2)
    (hn : n ≤ x) (hL : L ≤ x) (hx : 1 ≤ x) :
    generated + 1168 * n + 292 * L + 1460 + 2 * placement ≤
      stageDimensionCoefficient placementC * x ^ 3 := by
  have hx1 : x ≤ x ^ 3 := by
    simpa only [pow_one] using Nat.pow_le_pow_right hx (by decide : 1 ≤ 3)
  have hx2 : x ^ 2 ≤ x ^ 3 := Nat.pow_le_pow_right hx (by decide : 2 ≤ 3)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have hp' := hp.trans (Nat.mul_le_mul_left placementC hx2)
  unfold stageDimensionCoefficient
  nlinarith only [hg, hp', hn, hL, hx1, hx0]

theorem canonicalRouterStageDimensionOverhead_polynomial (n : ℕ) :
    canonicalRouterStageDimensionOverhead n ≤ canonicalRouterStageDimensionCoefficient * (n + 1) ^ 3 := by
  exact stage_dimension_bound _ _ _ _ _ _ (canonicalRouterGeneratedScalarOverhead_polynomial n)
    (canonicalRouterPlacementDimensionOverhead_polynomial n) (Nat.le_succ n)
    ((canonicalScalarWidth_le_self n).trans (Nat.le_succ n)) (Nat.succ_le_succ (Nat.zero_le n))

/-- Integer ledger for the complete dimension-only part of all eighteen passes. -/
def canonicalPermutationDimensionBudget (n : ℕ) : ℕ :=
  18 * (terminalDimensionBudget canonicalTerminalT (swapT 6) n (canonicalScalarWidth n) 1
    (131 * canonicalRouterGap n) +
    (canonicalRouterStride n * (canonicalRouterStageDimensionOverhead n + 1) +
      canonicalRouterDirectionalSetupBudget n 1 0 (canonicalScalarWidth n) 0 1 (canonicalRouterStride n))) +
    (36 * canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1
      (canonicalRouterStride n) + 2)

theorem canonicalPermutationDimensionCost_eq (n : ℕ) :
    canonicalPermutationDimensionCost n = (canonicalPermutationDimensionBudget n : ℕ) := by
  unfold canonicalPermutationDimensionCost canonicalRouterDirectionalDimensionCost
    canonicalPermutationDimensionBudget
  rw [canonicalTerminalPrice_dimension_eq]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

def permutationDimensionCoefficient (terminalC stageC directionalC outerC : ℕ) : ℕ :=
  18 * (terminalC + 640 * (stageC + 1) + directionalC) + 36 * outerC + 2

def canonicalPermutationDimensionCoefficient : ℕ :=
  permutationDimensionCoefficient canonicalTerminalDimensionCoefficient canonicalRouterStageDimensionCoefficient
    canonicalRouterDirectionalSetupCoefficient canonicalDirectionalFrameCoefficient

private theorem permutation_dimension_bound (terminal stage directional outer count
    terminalC stageC directionalC outerC x : ℕ)
    (ht : terminal ≤ terminalC * x ^ 3) (hs : stage ≤ stageC * x ^ 3)
    (hd : directional ≤ directionalC * x ^ 7) (ho : outer ≤ outerC * x ^ 3)
    (hc : count ≤ 640 * x) (hx : 1 ≤ x) :
    18 * (terminal + (count * (stage + 1) + directional)) + (36 * outer + 2) ≤
      permutationDimensionCoefficient terminalC stageC directionalC outerC * x ^ 7 := by
  have hx3 : x ^ 3 ≤ x ^ 7 := Nat.pow_le_pow_right hx (by decide : 3 ≤ 7)
  have hx4 : x ^ 4 ≤ x ^ 7 := Nat.pow_le_pow_right hx (by decide : 4 ≤ 7)
  have hx0 : 1 ≤ x ^ 3 := Nat.one_le_pow _ _ hx
  have hx7 : 1 ≤ x ^ 7 := Nat.one_le_pow _ _ hx
  have hstage : stage + 1 ≤ (stageC + 1) * x ^ 3 := by nlinarith only [hs, hx0]
  have hm := Nat.mul_le_mul hc hstage
  have scale (C x : ℕ) : (640 * x) * ((C + 1) * x ^ 3) = (640 * (C + 1)) * x ^ 4 := by ring
  rw [scale] at hm
  have hm' := hm.trans (Nat.mul_le_mul_left (640 * (stageC + 1)) hx4)
  have ht' := ht.trans (Nat.mul_le_mul_left terminalC hx3)
  have ho' := ho.trans (Nat.mul_le_mul_left outerC hx3)
  unfold permutationDimensionCoefficient
  nlinarith only [hm', ht', ho', hd, hx7]

theorem canonicalPermutationDimensionBudget_polynomial (n : ℕ) :
    canonicalPermutationDimensionBudget n ≤ canonicalPermutationDimensionCoefficient * (n + 1) ^ 7 := by
  have ht := canonicalTerminalDimension_polynomial n
  rw [canonicalTerminalPrice_dimension_eq] at ht
  have ht' := Nat.cast_le (α := ℝ).mp ht
  have hg := canonicalScalarWidth_le_self (n + 1)
  change Nat.clog 2 (n + 2) ≤ n + 1 at hg
  exact permutation_dimension_bound _ _ _ _ _ _ _ _ _ _ ht'
    (canonicalRouterStageDimensionOverhead_polynomial n)
    (canonicalRouterDirectionalSetupBudget_polynomial n)
    (canonicalDirectionalUniformFrameBudget_polynomial n)
    (stride_linear_bound n (Nat.clog 2 (n + 2)) hg) (Nat.succ_le_succ (Nat.zero_le n))

end
end IntegerMultBounds.MathlibTM2.Routing
