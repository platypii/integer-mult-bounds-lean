module

public import IntegerMultBounds.MathlibTM2.Cost.ChirpSupplier

/-! # Absorbing selected address widths into the chirp line cost -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.ShortConv

/-- Squared binary length is uniformly linear in the represented positive integer. -/
theorem chirp_size_sq_le (N : ℕ) (hN : 1 ≤ N) : Nat.size N ^ 2 ≤ 262144 * N := by
  have hs : Nat.size N ≤ Nat.log 2 N + 1 :=
    Nat.size_le.mpr (Nat.lt_pow_succ_log_self (by decide) N)
  have hlog := compact_natLog_succ_le hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hs' : (Nat.size N : ℝ) ≤ 512 * (N : ℝ) ^ (1 / 256 : ℝ) :=
    (by exact_mod_cast hs : (Nat.size N : ℝ) ≤ (Nat.log 2 N + 1 : ℕ)).trans hlog
  have hsq : (Nat.size N : ℝ) ^ 2 ≤ 262144 * (N : ℝ) ^ (1 / 128 : ℝ) := by
    calc
      _ ≤ (512 * (N : ℝ) ^ (1 / 256 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (Nat.cast_nonneg _) hs' 2
      _ = _ := by
        rw [mul_pow, ← Real.rpow_natCast ((N : ℝ) ^ (1 / 256 : ℝ)), ← Real.rpow_mul hN0.le]
        norm_num
  have hpow : (N : ℝ) ^ (1 / 128 : ℝ) ≤ N :=
    Real.rpow_le_self_of_one_le hN1 (by norm_num)
  have h := hsq.trans (mul_le_mul_of_nonneg_left hpow (by norm_num : (0 : ℝ) ≤ 262144))
  exact_mod_cast h

/-- The selected address word contributes only a quadratic precision term and linear length. -/
theorem chirp_address_sq_le {s t p q : ℕ} (hp : 1 ≤ p) (hst : s < t)
    (hq : q ≤ 83 * p) :
    (chirpForwardTableWord q (chirpForwardCallerBase s t p) + 1) ^ 2 ≤
      5000000000 * (p ^ 2 + t) := by
  have hbase : chirpForwardCallerBase s t p = t + 125 * p := by
    unfold chirpForwardCallerBase
    omega
  have hsize := chirp_size_sq_le (t + 125 * p) (by omega)
  have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
  have hW : chirpForwardTableWord q (chirpForwardCallerBase s t p) + 1 ≤
      1096 * p + 8 * Nat.size (t + 125 * p) := by
    rw [hbase]
    unfold chirpForwardTableWord
    omega
  have hsq := Nat.pow_le_pow_left hW 2
  have hsplit (x y : ℕ) : (x + y) ^ 2 ≤ 2 * x ^ 2 + 2 * y ^ 2 := by nlinarith [sq_nonneg (x - (y : ℤ))]
  have hsplit' := hsplit (1096 * p) (8 * Nat.size (t + 125 * p))
  nlinarith only [hsq, hsplit', hsize, hp2]

/-- All line work, including address and product startup, fits a uniform precision envelope. -/
theorem chirp_selected_fast_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α s t : ℕ, 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let q := chirpForwardPrecision p (chirpForwardGrowth p) l
      let w := q + l + chirpForwardGrowth p + 5
      let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
      (chirpForwardFastBound W s t q l m w : ℝ) ≤
        C * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hwork⟩ := chirp_selected_work_le
  let K : ℕ := 32000 * 5000000000 + (7056 * mtCvKf 125 + 264000)
  refine ⟨(K : ℝ) + 5 * C, by positivity, ?_⟩
  intro p α s t hp hα hαp hst
  dsimp only
  let m := chirpForwardWindow p α
  let l := chirpForwardRingLog p α
  let q := chirpForwardPrecision p (chirpForwardGrowth p) l
  let w := q + l + chirpForwardGrowth p + 5
  let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
  have hq : q ≤ 83 * p := (chirpForwardWidths_le p α hp hαp).1
  have haddr := chirp_address_sq_le hp hst hq
  have hfix := chirp_selected_fixed_le p α W hp hα hαp
  have hcombine (k x y z : ℕ) (hx : x ≤ 5000000000 * (y + z)) :
      32000 * x + k * y ≤ (32000 * 5000000000 + k) * (y + z) := by
    nlinarith only [hx, Nat.zero_le (k * z)]
  have hfixed : chirpLineFixedBound W q l w m ≤ K * (p ^ 2 + t) :=
    hfix.trans (hcombine _ _ _ _ haddr)
  have hfixed' : (chirpLineFixedBound W q l w m : ℝ) ≤ (K : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) := by
    exact_mod_cast hfixed
  have hm : m ≤ 2 * p := chirpForwardWindow_le p α hαp
  have hp2 : p ≤ p ^ 2 := by nlinarith only [hp]
  have hT : s + t + m + 1 ≤ 5 * (p ^ 2 + t) := by omega
  have hT' : ((s + t + m + 1 : ℕ) : ℝ) ≤ 5 * ((p ^ 2 + t : ℕ) : ℝ) := by exact_mod_cast hT
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  have hPow : (1 : ℝ) ≤ (p : ℝ) ^ (129 / 128 : ℝ) := Real.one_le_rpow hp1 (by norm_num)
  have hF := le_mul_of_one_le_right (show 0 ≤ (K : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) by positivity) hPow
  have hTcost := mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hT' hC)
    (show 0 ≤ (p : ℝ) ^ (129 / 128 : ℝ) by positivity)
  calc
    _ ≤ (chirpLineFixedBound W q l w m : ℝ) +
        C * ((s + t + m + 1 : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) :=
      hwork p α s t W hp hα hαp
    _ ≤ (K : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) +
        C * (5 * ((p ^ 2 + t : ℕ) : ℝ)) * (p : ℝ) ^ (129 / 128 : ℝ) :=
      add_le_add (hfixed'.trans hF) hTcost
    _ = _ := by ring

/-- Long lines absorb the fixed startup into the intended per-output multiplier allowance. -/
theorem chirp_selected_long_line_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ p α s t : ℕ, 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t → p ^ 2 ≤ t →
      let m := chirpForwardWindow p α
      let l := chirpForwardRingLog p α
      let q := chirpForwardPrecision p (chirpForwardGrowth p) l
      let w := q + l + chirpForwardGrowth p + 5
      let W := chirpForwardTableWord q (chirpForwardCallerBase s t p)
      (chirpForwardFastBound W s t q l m w : ℝ) ≤
        C * (t : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hcost⟩ := chirp_selected_fast_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro p α s t hp hα hαp hst ht
  have hsize : ((p ^ 2 + t : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast (show p ^ 2 + t ≤ 2 * t by omega)
  calc
    _ ≤ C * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := hcost p α s t hp hα hαp hst
    _ ≤ C * (2 * (t : ℝ)) * (p : ℝ) ^ (129 / 128 : ℝ) :=
      mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hsize hC) (by positivity)
    _ = _ := by ring

/-- The actual scalar group budget has only one shared startup term. -/
theorem chirp_selected_group_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p α s t N : ℕ) [NeZero s] [NeZero t], 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t →
      (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
        (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
          C * (N : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hunit⟩ := chirp_selected_fast_le
  refine ⟨C, hC, ?_⟩
  intro p α s t N _ _ hp hα hαp hst
  have hfast := LinePlacement.selectedGroupCost_le_fast s t α p N hst hα
  have hfast' : (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
      (LinePlacement.selectedGroupFastCost s t α p N : ℝ) := by exact_mod_cast hfast
  have h := mul_le_mul_of_nonneg_left (hunit p α s t hp hα hαp hst) (Nat.cast_nonneg N)
  have hcast (S N K : ℕ) : ((S + N * K : ℕ) : ℝ) = (S : ℝ) + (N : ℝ) * K := by push_cast; rfl
  apply hfast'.trans
  unfold LinePlacement.selectedGroupFastCost
  rw [hcast]
  calc
    _ ≤ (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
        (N : ℝ) * (C * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ)) := add_le_add le_rfl h
    _ = _ := by ring

/-- Long-line groups pay the intended per-output multiplier cost after one shared setup. -/
theorem chirp_selected_long_group_le :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (p α s t N : ℕ) [NeZero s] [NeZero t], 1 ≤ p → 1 ≤ α → α ^ 2 ≤ p → s < t → p ^ 2 ≤ t →
      (LinePlacement.selectedGroupCost s t α p N : ℝ) ≤
        (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
          C * (N : ℝ) * (t : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := by
  obtain ⟨C, hC, hcost⟩ := chirp_selected_group_le
  refine ⟨2 * C, by positivity, ?_⟩
  intro p α s t N _ _ hp hα hαp hst ht
  have hsize : ((p ^ 2 + t : ℕ) : ℝ) ≤ 2 * (t : ℝ) := by exact_mod_cast (show p ^ 2 + t ≤ 2 * t by omega)
  calc
    _ ≤ (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
        C * (N : ℝ) * ((p ^ 2 + t : ℕ) : ℝ) * (p : ℝ) ^ (129 / 128 : ℝ) := hcost p α s t N hp hα hαp hst
    _ ≤ (LinePlacement.selectedGroupCost s t α p 0 : ℝ) +
        C * (N : ℝ) * (2 * (t : ℝ)) * (p : ℝ) ^ (129 / 128 : ℝ) :=
      add_le_add le_rfl (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hsize (by positivity)) (by positivity))
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
