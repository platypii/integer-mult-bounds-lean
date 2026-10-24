module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPermutationMetadata
public import IntegerMultBounds.MathlibTM2.Routing.LiveRepairAmortized

/-! Separate scalar metadata sizes from physical stream volume in canonical setup. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def canonicalRouterGeneratedScalarOverhead (n R B width : ℕ) : ℕ :=
  let rb := canonicalScalarWidth R
  let L := canonicalScalarWidth n
  let D := Nat.clog 2 (4 * n + 2) + 1
  let wb := L + canonicalScalarWidth rb + canonicalScalarWidth B
  let w : LiveDescriptorWidths :=
    ⟨D, D, D, 2 * D, canonicalScalarWidth (2 * D)⟩
  let q : Par := ⟨canonicalRouterStride n, 0, n, canonicalRouterGap n, 0⟩
  binaryTemporaryMaskUniformCost n L L L L + binaryPhaseMaskUniformCost n L L L L +
    ((canonicalScalarWidth rb * (4 * rb + 11) + 8 * rb + 12) + (L * (4 * n + 11) + 2 * n + 6) + 1) +
    2 * (14 * n + 18 * rb + 24 * L + 52 * wb + 280) +
    liveCoordinateProfilesCost q w +
    liveRepairUniformOverhead n rb 0 0 width wb (n + rb) (canonicalScalarWidth B)
      (L + canonicalScalarWidth rb) w +
    (11 * (2 * (n * (2 * D + 3)) + 2) + 1) +
    (10 * (2 * width + 2) + 1) + (2 * rb + 2 * n + 5) + (4 * (n + 1) + 5)

theorem canonicalScalarWidth_le_self (x : ℕ) : canonicalScalarWidth x ≤ x := by
  unfold canonicalScalarWidth
  exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Nat.lt_two_pow_self (n := x)))

/-- Scalar-only setup is affine in header width and the payload's binary width. -/
theorem canonicalRouterGeneratedScalarOverhead_split (n R B width : ℕ) :
    canonicalRouterGeneratedScalarOverhead n R B width =
      canonicalRouterGeneratedScalarOverhead n R 0 0 +
        1260 * canonicalScalarWidth B + 292 * width := by
  have hzero : canonicalScalarWidth 0 = 0 := by decide
  unfold canonicalRouterGeneratedScalarOverhead liveRepairUniformOverhead
  simp only [hzero]
  ring

theorem canonicalRouterGeneratedOverhead_split (n R B width : ℕ) :
    canonicalRouterGeneratedOverhead n R B width =
      canonicalRouterGeneratedScalarOverhead n R B width + 272 * (B + R * 2 ^ n) := by
  dsimp only [canonicalRouterGeneratedOverhead, canonicalRouterGeneratedScalarOverhead]
  rw [liveRepairUniformOverhead_split]
  ring

theorem canonicalRouterGeneratedOverhead_amortized (n R B width : ℕ)
    (hR : 1 ≤ R) (hB : 1 ≤ B) :
    canonicalRouterGeneratedOverhead n R B width ≤
      canonicalRouterGeneratedScalarOverhead n R B width + 544 * (R * 2 ^ n * B) := by
  have hM : 1 ≤ R * 2 ^ n := by
    have hp := Nat.two_pow_pos n
    nlinarith
  have hb : B ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hm : R * 2 ^ n ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_left (R * 2 ^ n) hB
  rw [canonicalRouterGeneratedOverhead_split]
  omega

/-- All payload dependence in canonical one-row metadata is absorbed into
linear volume; the remaining additive term depends only on address dimension. -/
theorem canonicalRouterGeneratedOverhead_one_row (n B : ℕ) (hB : 1 ≤ B) :
    let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
    canonicalRouterGeneratedOverhead n 1 B width ≤
      canonicalRouterGeneratedScalarOverhead n 1 0 0 +
        1168 * n + 292 * canonicalScalarWidth n + 1460 + 2680 * (2 ^ n * B) := by
  let width := n + canonicalScalarWidth 1 +
    canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
  have hw1 : canonicalScalarWidth 1 = 1 := by decide
  have hwidth : width ≤ 4 * n + 3 * B + canonicalScalarWidth n + 5 := by
    have h := canonicalScalarWidth_le_self (3 * (n + canonicalScalarWidth 1 + B))
    dsimp only [width]
    rw [hw1] at h ⊢
    omega
  have hc := canonicalRouterGeneratedOverhead_amortized n 1 B width (by decide) hB
  rw [canonicalRouterGeneratedScalarOverhead_split] at hc
  simp only [Nat.one_mul] at hc
  have hlog := canonicalScalarWidth_le_self B
  have hb : B ≤ 2 ^ n * B := by
    have hp : 1 ≤ 2 ^ n := Nat.two_pow_pos n
    simpa using Nat.mul_le_mul_right B hp
  have bound (base width L log n B V : ℕ)
      (hw : width ≤ 4 * n + 3 * B + L + 5) (hl : log ≤ B) (hv : B ≤ V) :
      base + 1260 * log + 292 * width + 544 * V ≤
        base + 1168 * n + 292 * L + 1460 + 2680 * V := by omega
  exact hc.trans (bound _ width (canonicalScalarWidth n) (canonicalScalarWidth B) n B
    (2 ^ n * B) hwidth hlog hb)

/-- The complete generated one-row stage leaves only dimension setup and the
compact supplier power after all repair and metadata volume charges. -/
theorem canonicalRouterGeneratedCost_one_row_amortized (n B : ℕ)
    (hn : 1 ≤ n) (hB : (n + 2) ^ 2 ≤ B)
    (hsetup : let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
      6 * (swapT 6 * (width + 1)) + 2 * repairT + 6 * swapT 6 + 23 ≤ 2 ^ n * B) :
    let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
    canonicalRouterGeneratedCostBound n 1 B width ≤
      (canonicalRouterGeneratedScalarOverhead n 1 0 0 +
        1168 * n + 292 * canonicalScalarWidth n + 1460 : ℕ) + (8887 * (2 ^ n * B) : ℕ) +
      72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (2 ^ n * B : ℕ) *
        ((max 1 (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ) : ℝ) ^
          Parameters.tau + 1 := by
  have hb : 1 ≤ B := by nlinarith only [hB, Nat.zero_le n]
  have hc := canonicalRouterGeneratedCostBound_one_row n B _ hn hB hsetup
  have ho := Nat.cast_le (α := ℝ).mpr (canonicalRouterGeneratedOverhead_one_row n B hb)
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hc ho ⊢
  linarith only [hc, ho]

theorem generatedExchangeUniformOverhead_split (t₀ T n R B L rowLength widthLength bankBound : ℕ) :
    generatedExchangeUniformOverhead t₀ T n R B L rowLength widthLength bankBound =
      generatedExchangeUniformOverhead t₀ T n R 0 0 rowLength widthLength bankBound +
        68 * L + 34 * (R * 2 ^ n * B) := by
  unfold generatedExchangeUniformOverhead
  ring

def canonicalRouterPlacementSupplierCost (n R B : ℕ) : ℝ :=
  let T := inactiveClassifierPlacementT 6
  let H := routingReservoirWidth n (canonicalRouterGap n)
  let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
  (3 * swapConst * (T + 12 * swapT 6 + 5 : ℕ) * (R * 2 ^ n * B : ℕ)) *
    (((max 1 (3 * H) : ℕ) : ℝ) ^ Parameters.tau + 2 * ((max 1 w : ℕ) : ℝ) ^ Parameters.tau)

def canonicalRouterPlacementDimensionOverhead (n R : ℕ) : ℕ :=
  let T := inactiveClassifierPlacementT 6
  let Lc := canonicalScalarWidth n
  3 * (generatedExchangeUniformOverhead 6 T n R 0 0 (R.log2 + 1) Lc 0 +
    (3 * (Lc * (4 * n + 31) + 2 * n + 26) + 10 * Lc + 12) + (2 * n + 2 * Lc + 9)) + 1

theorem canonicalRouterPlacementCostBound_split (n R B : ℕ) :
    canonicalRouterPlacementCostBound n R B = canonicalRouterPlacementSupplierCost n R B +
      (canonicalRouterPlacementDimensionOverhead n R +
        204 * canonicalScalarWidth B + 102 * (R * 2 ^ n * B) : ℕ) := by
  dsimp only [canonicalRouterPlacementCostBound, canonicalRouterPlacementSupplierCost,
    canonicalRouterPlacementDimensionOverhead]
  rw [generatedExchangeUniformOverhead_split]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- Placement's scalar payload width is absorbed while both physical supplier
width powers remain explicit. -/
theorem canonicalRouterPlacementCostBound_amortized (n R B : ℕ) (hR : 1 ≤ R) :
    canonicalRouterPlacementCostBound n R B ≤ canonicalRouterPlacementSupplierCost n R B +
      (canonicalRouterPlacementDimensionOverhead n R + 306 * (R * 2 ^ n * B) : ℕ) := by
  have hM : 1 ≤ R * 2 ^ n := by
    have hp := Nat.two_pow_pos n
    nlinarith
  have hb : B ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hl := canonicalScalarWidth_le_self B
  have hs : canonicalRouterPlacementDimensionOverhead n R +
      204 * canonicalScalarWidth B + 102 * (R * 2 ^ n * B) ≤
      canonicalRouterPlacementDimensionOverhead n R + 306 * (R * 2 ^ n * B) := by omega
  rw [canonicalRouterPlacementCostBound_split]
  exact add_le_add (le_refl _) (Nat.cast_le (α := ℝ).mpr hs)

def canonicalRouterStageDimensionOverhead (n : ℕ) : ℕ :=
  canonicalRouterGeneratedScalarOverhead n 1 0 0 +
    1168 * n + 292 * canonicalScalarWidth n + 1460 +
    2 * canonicalRouterPlacementDimensionOverhead n 1

/-- A complete residue stage includes both physical placements and all generated
repair work; only address-dimension setup and supplier powers remain. -/
theorem canonicalRouterStageCost_one_row_amortized (n B : ℕ)
    (hn : 1 ≤ n) (hB : (n + 2) ^ 2 ≤ B)
    (hsetup : let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
      6 * (swapT 6 * (width + 1)) + 2 * repairT + 6 * swapT 6 + 23 ≤ 2 ^ n * B) :
    canonicalRouterStageCostBound n 1 B ≤
      (canonicalRouterStageDimensionOverhead n : ℕ) + (9499 * (2 ^ n * B) : ℕ) +
      2 * canonicalRouterPlacementSupplierCost n 1 B +
      72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (2 ^ n * B : ℕ) *
        ((max 1 (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ) : ℝ) ^
          Parameters.tau + 1 := by
  have hg := canonicalRouterGeneratedCost_one_row_amortized n B hn hB hsetup
  have hp := canonicalRouterPlacementCostBound_amortized n 1 B (by decide)
  dsimp only [canonicalRouterStageCostBound]
  unfold canonicalRouterStageDimensionOverhead
  simp only [Nat.one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hg hp ⊢
  linarith only [hg, hp]

/-- Separate terminal dimension setup, stream movement and binary payload width. -/
theorem canonicalTerminalPrice_split (n rows B L Lb rowLength count : ℕ) :
    canonicalTerminalPrice n rows B L Lb rowLength count =
      canonicalTerminalPrice n 0 0 L 0 rowLength count +
      count * (6 * swapConst * (canonicalTerminalT + 12 * swapT 6 + 5 : ℕ) + 176) *
        (rows * 2 ^ n * B : ℕ) +
      (8 * (B + rows * 2 ^ n) + (11 + count * (99 + 12 * swapT 6)) * Lb : ℕ) := by
  unfold canonicalTerminalPrice canonicalTerminalBaseCost elementaryCompileBase elementaryCompilerPrepareBound
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat, Nat.zero_mul, Nat.mul_zero, Nat.cast_zero]
  ring

/-- Terminal work is linear in row volume per actual coordinate instruction. -/
theorem canonicalTerminalPrice_one_row_amortized (n B L rowLength count : ℕ) (hB : 1 ≤ B) :
    canonicalTerminalPrice n 1 B L (canonicalScalarWidth B) rowLength count ≤
      canonicalTerminalPrice n 0 0 L 0 rowLength count +
      (count * (6 * swapConst * (canonicalTerminalT + 12 * swapT 6 + 5 : ℕ) +
        275 + 12 * swapT 6) + 27) * (2 ^ n * B : ℕ) := by
  have hM : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  have hb : B ≤ 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hm : 2 ^ n ≤ 2 ^ n * B := by simpa using Nat.mul_le_mul_left (2 ^ n) hB
  have hl : canonicalScalarWidth B ≤ 2 ^ n * B := (canonicalScalarWidth_le_self B).trans hb
  have bound (B M Lb V count tapes : ℕ) (hb : B ≤ V) (hm : M ≤ V) (hl : Lb ≤ V) :
      8 * (B + M) + (11 + count * (99 + 12 * tapes)) * Lb ≤
        (27 + count * (99 + 12 * tapes)) * V := by
    have h := Nat.mul_le_mul_left (11 + count * (99 + 12 * tapes)) hl
    nlinarith only [hb, hm, h]
  have hs := Nat.cast_le (α := ℝ).mpr (bound B (2 ^ n) (canonicalScalarWidth B)
    (2 ^ n * B) count (swapT 6) hb hm hl)
  rw [canonicalTerminalPrice_split]
  simp only [Nat.one_mul, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hs ⊢
  nlinarith only [hs]

theorem canonicalRouterUniformMetadataWidth_split (n R B : ℕ) :
    canonicalRouterUniformMetadataWidth n R B = canonicalRouterUniformMetadataWidth n R 0 +
      3 * canonicalScalarWidth B := by
  have hz : canonicalScalarWidth 0 = 0 := by decide
  unfold canonicalRouterUniformMetadataWidth
  simp only [hz]
  ring

theorem canonicalRouterUniformFrameWidth_split (n R B : ℕ) :
    canonicalRouterUniformFrameWidth n R B = canonicalRouterUniformFrameWidth n R 0 +
      3 * originalMatchingScheduleT 6 * canonicalScalarWidth B := by
  dsimp only [canonicalRouterUniformFrameWidth]
  rw [canonicalRouterUniformMetadataWidth_split]
  ring

theorem canonicalRouterStageSetupBudget_split (n R B : ℕ) :
    canonicalRouterStageSetupBudget n R B = canonicalRouterStageSetupBudget n R 0 +
      (6 + 18 * originalMatchingScheduleT 6) * canonicalScalarWidth B := by
  dsimp only [canonicalRouterStageSetupBudget, canonicalRouterOriginalSetupBudget]
  rw [canonicalRouterUniformMetadataWidth_split, canonicalRouterUniformFrameWidth_split]
  ring

theorem canonicalDirectionalUniformFrameBudget_split (n R B L Lb rowLength count : ℕ) :
    canonicalDirectionalUniformFrameBudget n R B L Lb rowLength count =
      canonicalDirectionalUniformFrameBudget n R 0 L 0 rowLength count +
      (canonicalRouterCommonT + 3) *
        (Lb + 3 * count * originalMatchingScheduleT 6 * canonicalScalarWidth B) := by
  dsimp only [canonicalDirectionalUniformFrameBudget]
  rw [canonicalRouterUniformFrameWidth_split]
  ring

def canonicalRouterDirectionalSetupBudget (n R B L Lb rowLength count : ℕ) : ℕ :=
  count * (canonicalRouterStageSetupBudget n R B + 2 + 2 * canonicalRouterUniformFrameWidth n R B) + 4 +
    6 * canonicalDirectionalUniformFrameBudget n R B L Lb rowLength count +
    2 * (canonicalRouterCommonT + 3) + 2

def canonicalRouterDirectionalSetupSlope (count : ℕ) : ℕ :=
  count * (6 + 24 * originalMatchingScheduleT 6) +
    6 * (canonicalRouterCommonT + 3) * (1 + 3 * count * originalMatchingScheduleT 6)

theorem canonicalRouterDirectionalSetupBudget_split (n R B L rowLength count : ℕ) :
    canonicalRouterDirectionalSetupBudget n R B L (canonicalScalarWidth B) rowLength count =
      canonicalRouterDirectionalSetupBudget n R 0 L 0 rowLength count +
        canonicalRouterDirectionalSetupSlope count * canonicalScalarWidth B := by
  unfold canonicalRouterDirectionalSetupBudget canonicalRouterDirectionalSetupSlope
  rw [canonicalRouterStageSetupBudget_split, canonicalRouterUniformFrameWidth_split,
    canonicalDirectionalUniformFrameBudget_split]
  ring

/-- The entire schedule/frame ledger has only dimension setup and linear volume. -/
theorem canonicalRouterDirectionalSetupBudget_amortized (n R B L rowLength count : ℕ)
    (hR : 1 ≤ R) :
    canonicalRouterDirectionalSetupBudget n R B L (canonicalScalarWidth B) rowLength count ≤
      canonicalRouterDirectionalSetupBudget n R 0 L 0 rowLength count +
        canonicalRouterDirectionalSetupSlope count * (R * 2 ^ n * B) := by
  have hM : 1 ≤ R * 2 ^ n := by
    have hp := Nat.two_pow_pos n
    nlinarith
  have hb : B ≤ R * 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hl := (canonicalScalarWidth_le_self B).trans hb
  rw [canonicalRouterDirectionalSetupBudget_split]
  exact Nat.add_le_add_left (Nat.mul_le_mul_left _ hl) _

def canonicalRouterStageAmortizedBound (n B : ℕ) : ℝ :=
  (canonicalRouterStageDimensionOverhead n : ℕ) + (9499 * (2 ^ n * B) : ℕ) +
      2 * canonicalRouterPlacementSupplierCost n 1 B +
      72 * swapConst * (repairT + 12 * swapT 6 + 5 : ℕ) * (2 ^ n * B : ℕ) *
        ((max 1 (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) : ℕ) : ℝ) ^
          Parameters.tau + 1

def canonicalTerminalAmortizedBound (n B L rowLength count : ℕ) : ℝ :=
  canonicalTerminalPrice n 0 0 L 0 rowLength count +
      (count * (6 * swapConst * (canonicalTerminalT + 12 * swapT 6 + 5 : ℕ) +
        275 + 12 * swapT 6) + 27) * (2 ^ n * B : ℕ)

def canonicalRouterDirectionalAmortizedBound (n B count : ℕ) : ℝ :=
  canonicalTerminalAmortizedBound n B (canonicalScalarWidth n) 1 (131 * canonicalRouterGap n) +
    count * canonicalRouterStageAmortizedBound n B +
    (canonicalRouterDirectionalSetupBudget n 1 0 (canonicalScalarWidth n) 0 1 count +
      canonicalRouterDirectionalSetupSlope count * (2 ^ n * B) : ℕ)

theorem canonicalRouterDirectionalCostBound_eq_components (n R B L Lb rowLength count : ℕ) :
    canonicalRouterDirectionalCostBound n R B L Lb rowLength count =
      canonicalTerminalPrice n R B L Lb rowLength (131 * canonicalRouterGap n) +
        count * canonicalRouterStageCostBound n R B +
        (canonicalRouterDirectionalSetupBudget n R B L Lb rowLength count : ℕ) := by
  dsimp only [canonicalRouterDirectionalCostBound, canonicalRouterDirectionalSetupBudget]
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]
  ring

/-- All executed terminal, bulk, schedule and frame costs of one direction. -/
theorem canonicalRouterDirectionalCost_one_row_amortized (n B count : ℕ)
    (hn : 1 ≤ n) (hB : (n + 2) ^ 2 ≤ B)
    (hsetup : let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
      6 * (swapT 6 * (width + 1)) + 2 * repairT + 6 * swapT 6 + 23 ≤ 2 ^ n * B) :
    canonicalRouterDirectionalCostBound n 1 B (canonicalScalarWidth n) (canonicalScalarWidth B) 1 count ≤
      canonicalRouterDirectionalAmortizedBound n B count := by
  have hb : 1 ≤ B := by nlinarith only [hB, Nat.zero_le n]
  have ht : canonicalTerminalPrice n 1 B (canonicalScalarWidth n) (canonicalScalarWidth B) 1
      (131 * canonicalRouterGap n) ≤
      canonicalTerminalAmortizedBound n B (canonicalScalarWidth n) 1 (131 * canonicalRouterGap n) :=
    canonicalTerminalPrice_one_row_amortized n B (canonicalScalarWidth n) 1 _ hb
  have hs : canonicalRouterStageCostBound n 1 B ≤ canonicalRouterStageAmortizedBound n B :=
    canonicalRouterStageCost_one_row_amortized n B hn hB hsetup
  have hf := Nat.cast_le (α := ℝ).mpr
    (canonicalRouterDirectionalSetupBudget_amortized n 1 B (canonicalScalarWidth n) 1 count (by decide))
  simp only [Nat.one_mul] at hf
  rw [canonicalRouterDirectionalCostBound_eq_components]
  exact add_le_add (add_le_add ht (mul_le_mul_of_nonneg_left hs (Nat.cast_nonneg count))) hf

def canonicalDirectionalFrameSlope (count : ℕ) : ℕ :=
  (canonicalRouterCommonT + 3) * (1 + 3 * count * originalMatchingScheduleT 6)

theorem canonicalDirectionalUniformFrameBudget_one_row_amortized (n B L rowLength count : ℕ) :
    canonicalDirectionalUniformFrameBudget n 1 B L (canonicalScalarWidth B) rowLength count ≤
      canonicalDirectionalUniformFrameBudget n 1 0 L 0 rowLength count +
        canonicalDirectionalFrameSlope count * (2 ^ n * B) := by
  have hM : 1 ≤ 2 ^ n := Nat.two_pow_pos n
  have hb : B ≤ 2 ^ n * B := by simpa using Nat.mul_le_mul_right B hM
  have hl := (canonicalScalarWidth_le_self B).trans hb
  have hm := Nat.mul_le_mul_left (canonicalDirectionalFrameSlope count) hl
  rw [canonicalDirectionalUniformFrameBudget_split]
  unfold canonicalDirectionalFrameSlope at hm ⊢
  nlinarith only [hm]

def canonicalPermutationAmortizedBound (n B : ℕ) : ℝ :=
  18 * canonicalRouterDirectionalAmortizedBound n B (canonicalRouterStride n) +
    (36 * canonicalDirectionalUniformFrameBudget n 1 0 (canonicalScalarWidth n) 0 1
      (canonicalRouterStride n) + 2 +
      36 * canonicalDirectionalFrameSlope (canonicalRouterStride n) * (2 ^ n * B) : ℕ)

/-- All eighteen directions and the final metadata rewind are charged. -/
theorem canonicalPermutationCost_one_row_amortized (n B : ℕ)
    (hn : 1 ≤ n) (hB : (n + 2) ^ 2 ≤ B)
    (hsetup : let width := n + canonicalScalarWidth 1 +
      canonicalScalarWidth (3 * (n + canonicalScalarWidth 1 + B)) + canonicalScalarWidth n + 1
      6 * (swapT 6 * (width + 1)) + 2 * repairT + 6 * swapT 6 + 23 ≤ 2 ^ n * B) :
    canonicalPermutationCostBound n 1 B (canonicalScalarWidth n) (canonicalScalarWidth B) 1 ≤
      canonicalPermutationAmortizedBound n B := by
  have hd := canonicalRouterDirectionalCost_one_row_amortized n B (canonicalRouterStride n) hn hB hsetup
  have hf := Nat.cast_le (α := ℝ).mpr
    (canonicalDirectionalUniformFrameBudget_one_row_amortized n B (canonicalScalarWidth n) 1
      (canonicalRouterStride n))
  unfold canonicalPermutationCostBound canonicalPermutationAmortizedBound
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hf ⊢
  linarith only [hd, hf]

end
end IntegerMultBounds.MathlibTM2.Routing
