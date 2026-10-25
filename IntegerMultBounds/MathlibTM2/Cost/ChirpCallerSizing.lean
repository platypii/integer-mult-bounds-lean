module

public import IntegerMultBounds.MathlibTM2.Cost.ChirpForwardBudget
public import IntegerMultBounds.MathlibTM2.Mult.Sizes

/-! # Discharging forward amortization at the executable caller's dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv
open Filter Finset

/-- Polynomially large axes and complementary batches pay the selected scalar startup. -/
theorem chirp_caller_size_gates (s t α p N : ℕ) (hp : 4 * 1200 ^ 3 ≤ p)
    (hst : s < t) (hαp : α ^ 2 ≤ p) (ht : t ≤ 2 ^ p)
    (hpt : p ^ 4 ≤ 2 * t) (hpN : p ^ 4 ≤ 4 * N) :
    p ^ 2 ≤ t ∧
      (chirpForwardTableWord
        (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α))
        (chirpForwardCallerBase s t p) + 1) ^ 3 ≤ N := by
  have hp1 : 1 ≤ p := by omega
  have hq := (chirpForwardWidths_le p α hp1 hαp).1
  have hB : chirpForwardCallerBase s t p < 2 ^ (p + 8) := by
    have hpPow : p ≤ 2 ^ p := Nat.lt_two_pow_self.le
    have hpos : 0 < 2 ^ p := by positivity
    have hbase : chirpForwardCallerBase s t p = t + 125 * p := by
      unfold chirpForwardCallerBase
      omega
    rw [hbase, pow_add]
    norm_num
    omega
  have hsize : Nat.size (chirpForwardCallerBase s t p) ≤ p + 8 := Nat.size_le.mpr hB
  have hW : chirpForwardTableWord
      (chirpForwardPrecision p (chirpForwardGrowth p) (chirpForwardRingLog p α))
      (chirpForwardCallerBase s t p) + 1 ≤ 1200 * p := by
    unfold chirpForwardTableWord
    omega
  have hcube := Nat.mul_le_mul_right (p ^ 3) hp
  have hWcube := Nat.pow_le_pow_left hW 3
  have hpSq : 2 ≤ p ^ 2 := by nlinarith only [hp1, hp]
  constructor
  · nlinarith only [hpt, hpSq]
  · nlinarith only [hcube, hWcube, hpN]

/-- Every source modulus is more than half its target length in a valid axis family. -/
theorem chirp_source_half {d s t : ℕ} (hd : 1 ≤ d) (h : Moduli.AxisBounds d s t) :
    t < 2 * s := by
  by_contra hc
  have hmul := Nat.mul_le_mul_left d (not_lt.mp hc)
  have hdt : t ≤ d * t := Nat.le_mul_of_pos_left _ hd
  nlinarith only [hmul, hdt, h.lower]

/-- One other live axis already gives a lower bound for a whole complementary batch. -/
theorem chirp_complement_ge {d R : ℕ} (dims : Fin d → ℕ) (hd : 2 ≤ d)
    (hpos : ∀ j, 1 ≤ dims j) (hR : ∀ j, R ≤ 4 * dims j) (i : Fin d) :
    R ≤ 4 * ∏ j ∈ (Finset.univ.erase i), dims j := by
  have : Nontrivial (Fin d) := Fin.nontrivial_iff_two_le.mpr hd
  obtain ⟨j, hji⟩ := exists_ne i
  have hj : j ∈ (Finset.univ.erase i) := Finset.mem_erase.mpr ⟨hji, Finset.mem_univ _⟩
  exact (hR j).trans (Nat.mul_le_mul_left 4
    (Finset.single_le_prod (fun k _ => hpos k) hj))

/-- Executable source and target dimensions share the same exponential radius scale. -/
theorem chirp_runtime_axis_bounds {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) :
    Sizes.r n ≤ 2 * Sizes.t n i ∧ Sizes.t n i ≤ 2 ^ Sizes.p n ∧
      Sizes.r n ≤ 4 * Sizes.s n i := by
  have hl := h.four_le_ℓ
  have hpow : 2 ^ Sizes.ℓ n = 2 * 2 ^ (Sizes.ℓ n - 1) := by
    rw [← pow_succ']
    congr 1
    omega
  have hr : Sizes.r n ≤ 2 * Sizes.t n i := by
    unfold Sizes.t Sizes.r
    split_ifs <;> omega
  have ht : Sizes.t n i ≤ Sizes.r n := by
    unfold Sizes.t Sizes.r
    split_ifs
    · exact Nat.pow_le_pow_right (by decide) (Nat.sub_le _ _)
    · exact le_rfl
  have hlp : Sizes.ℓ n ≤ Sizes.p n := by
    have hdl : Sizes.ℓ n ≤ 3 * Sizes.d n * Sizes.ℓ n :=
      Nat.le_mul_of_pos_left _ (by have := h.one_le_d; omega)
    exact hdl.trans h.ℓ_bounds.2
  have hhalf := chirp_source_half h.one_le_d (h.good.bounds i)
  exact ⟨hr, ht.trans (Nat.pow_le_pow_right (by decide) hlp), by nlinarith only [hr, hhalf]⟩

/-- Full complementary batches at the executable sizes eventually satisfy both cost gates.
Every mixture of source and target axes is covered by the lower bound on live dimensions. -/
theorem chirp_runtime_size_gates : ∀ᶠ n : ℕ in atTop,
    ∀ (dims : Fin (Sizes.d n) → ℕ), (∀ j, Sizes.s n j ≤ dims j) →
      ∀ i : Fin (Sizes.d n),
        Sizes.p n ^ 2 ≤ Sizes.t n i ∧
          (chirpForwardTableWord
            (chirpForwardPrecision (Sizes.p n) (chirpForwardGrowth (Sizes.p n))
              (chirpForwardRingLog (Sizes.p n) (Sizes.alpha n)))
            (chirpForwardCallerBase (Sizes.s n i) (Sizes.t n i) (Sizes.p n)) + 1) ^ 3 ≤
            ∏ j ∈ (Finset.univ.erase i), dims j := by
  filter_upwards [Sizes.eventually_big, Sizes.eventually_pow_p_le_r 4,
    Sizes.tendsto_b.eventually (eventually_ge_atTop (4 * 1200 ^ 3))] with n h hpow hb
  intro dims hdims i
  have hp : 4 * 1200 ^ 3 ≤ Sizes.p n := by unfold Sizes.p; omega
  have hd : 2 ≤ Sizes.d n := by have := h.2; omega
  have hpos (j : Fin (Sizes.d n)) : 1 ≤ dims j := by
    have hj : 3 ≤ Sizes.s n j := Sizes.three_le_srcLen n j.val
    exact (by omega : 1 ≤ Sizes.s n j).trans (hdims j)
  have hR (j : Fin (Sizes.d n)) : Sizes.r n ≤ 4 * dims j :=
    (chirp_runtime_axis_bounds h j).2.2.trans (Nat.mul_le_mul_left 4 (hdims j))
  have hcount := chirp_complement_ge dims hd hpos hR i
  have haxis := chirp_runtime_axis_bounds h i
  exact chirp_caller_size_gates _ _ _ _ _ hp (h.good.lt i) h.alpha_sq_le_p haxis.2.1
    (hpow.trans haxis.1) (hpow.trans hcount)

/-- The actual scalar budget for complete live-axis batches has the intended uniform cost.
This matches the S2 primitive; tensor scheduling and transfer remain separate obligations. -/
theorem chirp_runtime_group_cost : ∀ᶠ n : ℕ in atTop,
    ∀ (dims : Fin (Sizes.d n) → ℕ), (∀ j, Sizes.s n j ≤ dims j) →
      ∀ i : Fin (Sizes.d n),
        let N := ∏ j ∈ (Finset.univ.erase i), dims j
        (LinePlacement.selectedGroupCost (Sizes.s n i) (Sizes.t n i) (Sizes.alpha n) (Sizes.p n) N : ℝ) ≤
          chirpForwardCostConstant * (N : ℝ) * (Sizes.t n i : ℝ) *
            (Sizes.p n : ℝ) ^ (129 / 128 : ℝ) := by
  filter_upwards [chirp_runtime_size_gates, Sizes.eventually_big] with n hg h
  intro dims hdims i
  have hs : 3 ≤ Sizes.s n i := Sizes.three_le_srcLen n i.val
  have hst := h.good.lt i
  have : NeZero (Sizes.s n i) := ⟨by omega⟩
  have : NeZero (Sizes.t n i) := ⟨by omega⟩
  have hα : 1 ≤ Sizes.alpha n := (by decide : 1 ≤ 2).trans (Sizes.two_le_alpha' n)
  exact chirp_selected_amortized_budget _ _ _ _ _ hst hα h.alpha_sq_le_p
    (hg dims hdims i).1 (hg dims hdims i).2

end IntegerMultBounds.MathlibTM2.Cost
