module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicNormalizationLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
import Mathlib.Tactic.Linarith

/-! Coarse polynomial envelope for actual zero-replica normalization setup. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem cyclicNormalizationSetup_poly (p q W a L Z : ℕ)
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hP : 2^15*p ≤ Z) (hq : 2*q+8 ≤ Z)
    (hW : W ≤ Z) (ha : a ≤ Z) (hL : L ≤ Z)
    (hB : cyclicNormalizationWidth (2^15*p) q ≤ Z) :
    PackedRecoveryNormalization.normalizationCost p q W a L 0 ≤ 1000000*Z^3 := by
  let B := cyclicNormalizationWidth (2^15*p) q
  have hbits : Nat.size (4*p) ≤ 4*Z :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (Nat.mul_le_mul_left 4 hp)
  have htable : tblC B 0 ≤ 800*Z^2 := by
    have hsq := Nat.pow_le_pow_left (show B+4 ≤ 5*Z by dsimp only [B]; omega) 2
    unfold tblC
    nlinarith only [hsq]
  have hsetup := Nat.mul_le_mul (show 18+(4*Nat.size (4*p)+31) ≤ 16*Z+49 by omega) htable
  have hsub : W-(2*p+13) ≤ Z := (Nat.sub_le _ _).trans hW
  have hnorm : normalizePackedBatchCost B (2*q+8) p W 0 L ≤
      13*(800*Z^2)+16*Z+44*Z+54+
        (4*Z+4*(2*Z+13)+2*Z+24+6+8*Z+Z*(6*(2*Z+13)+9)+2*(2*Z+13)+17) := by
    unfold normalizePackedBatchCost roundPackedKeyCost publishRoundedKeyCost widenPackedKeyCost widenPackedPrefixCost
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    gcongr
  have hcontrols : (2^15*p+q)*(4*B+10) ≤ (2*Z)*(4*Z+10) :=
    Nat.mul_le_mul (by omega) (by dsimp only [B]; omega)
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  unfold PackedRecoveryNormalization.normalizationCost
  dsimp only
  change _ ≤ 1000000*Z^3
  dsimp only [B] at htable hsetup hnorm hcontrols
  nlinarith only [hsetup,hnorm,hcontrols,h₂,h₃,hZ,hp,hP,hq,hW,ha,hL,hB]

theorem cyclicNormalizationSetup_axis_poly (p q W a L t cw cW : ℕ)
    (ht : 1 ≤ t) (hp : p ≤ t) (hq : 2*q+8 ≤ cw*p) (hW : W ≤ cW*p)
    (ha : a ≤ t) (hL : L ≤ t) :
    PackedRecoveryNormalization.normalizationCost p q W a L 0 ≤
      1000000*(32775+cw+cW)^3*t^3 := by
  let c := 32775+cw+cW
  let Z := c*t
  have hZ : 1 ≤ Z := by
    apply Nat.mul_pos (show 1 ≤ c by dsimp only [c]; omega) ht
  have hpZ : p ≤ Z := by dsimp only [Z,c]; nlinarith
  have hPZ : 2^15*p ≤ Z := by dsimp only [Z,c]; nlinarith
  have hqZ : 2*q+8 ≤ Z := by
    have hh := Nat.mul_le_mul_left cw hp
    dsimp only [Z,c]
    nlinarith only [hq,hh, Nat.zero_le (cW*t),Nat.zero_le t]
  have hWZ : W ≤ Z := by
    have hh := Nat.mul_le_mul_left cW hp
    dsimp only [Z,c]
    nlinarith only [hW,hh,Nat.zero_le (cw*t),Nat.zero_le t]
  have htZ : t ≤ Z := by dsimp only [Z,c]; nlinarith
  have hB : cyclicNormalizationWidth (2^15*p) q ≤ Z := by
    have hbitsP : Nat.size (2^15*p) ≤ 2^15*p := Nat.size_le.mpr Nat.lt_two_pow_self
    have hbitsq : Nat.size q ≤ q := Nat.size_le.mpr Nat.lt_two_pow_self
    have hh := Nat.mul_le_mul_left cw hp
    unfold cyclicNormalizationWidth
    dsimp only [Z,c]
    nlinarith only [hbitsP,hbitsq,hq,hh,hp,ht,Nat.zero_le (cW*t)]
  have hh := cyclicNormalizationSetup_poly p q W a L Z hZ hpZ hPZ hqZ hWZ
    (ha.trans htZ) (hL.trans htZ) hB
  calc
    _ ≤ 1000000*Z^3 := hh
    _ = _ := by dsimp only [Z,c]; ring

/-- Actual zero-replica normalization setup is shared per scheduled call, with
both physical pieces charged and no multiplier from the RHS replica count. -/
theorem selectedCyclicNormalizationSetupSchedule_volume_le (cw cW scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big n) (i : Fin (Sizes.d n))
      (jobs : List ι) (q a span : ι → ℕ) (W : ℕ),
      jobs.length ≤ 2*Sizes.t n i → W ≤ cW*Sizes.p n →
      (∀ j ∈ jobs, 2*q j+8 ≤ cw*Sizes.p n ∧ a j ≤ Sizes.t n i ∧ span j ≤ Sizes.t n i) →
      scale*(jobs.map (fun j =>
        PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q j) W (a j)
          (min (span j) (Sizes.s n i-a j)) 0+
        PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q j) W 0
          (span j-min (span j) (Sizes.s n i-a j)) 0)).sum ≤ Sizes.T n := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (2000000*(32775+cw+cW)^3) 0 3 scale] with n hs
  intro ι h i jobs q a span W hcount hW hparams
  apply hs i jobs _ hcount
  intro j hj
  obtain ⟨hq,ha,hL⟩ := hparams j hj
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hp : Sizes.p n ≤ Sizes.t n i := selectedPrecision_le_axis h i
  have hl := cyclicNormalizationSetup_axis_poly (Sizes.p n) (q j) W (a j)
    (min (span j) (Sizes.s n i-a j)) (Sizes.t n i) cw cW ht hp hq hW ha
    ((Nat.min_le_left _ _).trans hL)
  have hr := cyclicNormalizationSetup_axis_poly (Sizes.p n) (q j) W 0
    (span j-min (span j) (Sizes.s n i-a j)) (Sizes.t n i) cw cW ht hp hq hW (Nat.zero_le _)
    ((Nat.sub_le _ _).trans hL)
  simp only [pow_zero,Nat.mul_one]
  nlinarith only [hl,hr]

end IntegerMultBounds.MathlibTM2.Cost
