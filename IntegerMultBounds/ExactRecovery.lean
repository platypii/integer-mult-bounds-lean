import IntegerMultBounds.NLogN.MainReduction
import IntegerMultBounds.NLogN.ResamplingNumeric
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics

/-! Precision and exact recovery (§8, "The final integer coefficients"). The
computed source transforms `F'` approximate the exact contraction `F` with
scaled error `E_s` on the half ball, the computed opposite transform `G'`
likewise approximates the contraction `G`, and the pointwise product is
truncated to the grid. For inputs of norm at most `1/4` the computed arrays
stay in the disk, the truncated product has norm below `1/2`, and the computed
opposite transform of it is within `(3 E_s + 2) 2^(-p)` of `G (F u · F v)`.
With the convolution identity `G (F u · F v) = (u ∗ v) / S²`, the numerator
scalings return the normalised convolution within `16 S (3 E_s + 2) 2^(-p)`,
and the rounding recovery of `MainReduction` gives the exact product once
`2^(2k+4) S² (3 E_s + 2) < 2^(p-1)`. With `E_s = 9 · 2^γ T L`, `S ≤ T < 2^k`,
`L < k`, `γ ≤ k/4` and `p = 6k`, this is the manuscript's
`448 k 2^(-3k/4) < 1/2`, which holds for all large `k`. Tape costs are not
part of this file. -/

namespace IntegerMultBounds.ExactRecovery

open NLogN Filter Topology

/-! ### Pointwise products in the sup norm -/

section Pointwise

variable {κ : Type*} [Fintype κ]

theorem norm_pointwise_mul_le (a b : κ → ℂ) : ‖fun k => a k * b k‖ ≤ ‖a‖ * ‖b‖ := by
  rw [pi_norm_le_iff_of_nonneg (by positivity)]
  intro k
  rw [norm_mul]
  exact mul_le_mul (norm_le_pi_norm a k) (norm_le_pi_norm b k) (norm_nonneg _) (norm_nonneg _)

/-- The bilinear contraction bound: replacing both operands adds the two errors
weighted by the other operand's norm. -/
theorem norm_pointwise_mul_sub_le (a' a b' b : κ → ℂ) :
    ‖(fun k => a' k * b' k) - fun k => a k * b k‖ ≤ ‖a' - a‖ * ‖b'‖ + ‖a‖ * ‖b' - b‖ := by
  have e : ((fun k => a' k * b' k) - fun k => a k * b k) =
      (fun k => (a' - a) k * b' k) + fun k => a k * (b' - b) k := by
    funext k
    simp only [Pi.sub_apply, Pi.add_apply]
    ring
  rw [e]
  exact (norm_add_le _ _).trans
    (add_le_add (norm_pointwise_mul_le _ _) (norm_pointwise_mul_le _ _))

end Pointwise

/-! ### The computed convolution against the exact one -/

section Recovery

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {p : ℕ} {Es : ℝ}
  (F : (ι → ℂ) →L[ℂ] (κ → ℂ)) (F' : (ι → ℂ) → (κ → ℂ))
  (G : (κ → ℂ) →L[ℂ] (ι → ℂ)) (G' : (κ → ℂ) → (ι → ℂ))

/-- The computed opposite transform of the truncated pointwise product of the
computed source transforms. -/
noncomputable def computed (u v : ι → ℂ) : ι → ℂ :=
  G' (rdV p fun k => F' u k * F' v k)

variable (hF : ‖F‖ ≤ 1) (hF' : ∀ x : ι → ℂ, ‖x‖ ≤ 1 / 2 → 2 ^ p * ‖F' x - F x‖ ≤ Es)
  (hG : ‖G‖ ≤ 1) (hG' : ∀ y : κ → ℂ, ‖y‖ ≤ 1 / 2 → 2 ^ p * ‖G' y - G y‖ ≤ Es)
  (hEs : Es ≤ 2 ^ p / 100)

include hF hF' hEs in
/-- A computed source transform of a quarter-ball input has norm at most `0.26`. -/
theorem norm_computed_source_le {u : ι → ℂ} (hu : ‖u‖ ≤ 1 / 4) :
    ‖F' u‖ ≤ 26 / 100 ∧ 2 ^ p * ‖F' u - F u‖ ≤ Es := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  have h1 := hF' u (by linarith)
  have hFu : ‖F u‖ ≤ 1 / 4 := by
    calc ‖F u‖ ≤ ‖F‖ * ‖u‖ := F.le_opNorm u
      _ ≤ 1 * (1 / 4) := by gcongr
      _ = 1 / 4 := by norm_num
  refine ⟨?_, h1⟩
  have h2 : ‖F' u - F u‖ ≤ 1 / 100 := by
    have h3 : 2 ^ p * ‖F' u - F u‖ ≤ 2 ^ p * (1 / 100) := by linarith
    exact le_of_mul_le_mul_left h3 hp
  calc ‖F' u‖ = ‖(F' u - F u) + F u‖ := by rw [sub_add_cancel]
    _ ≤ ‖F' u - F u‖ + ‖F u‖ := norm_add_le _ _
    _ ≤ 1 / 100 + 1 / 4 := add_le_add h2 hFu
    _ = 26 / 100 := by norm_num

include hF hF' hG hG' hEs in
/-- The manuscript's chain: the computed opposite transform of the truncated
product is within `(3 E_s + 2) 2^(-p)` of `G (F u · F v)`. -/
theorem recovery_error {u v : ι → ℂ} (hu : ‖u‖ ≤ 1 / 4) (hv : ‖v‖ ≤ 1 / 4) :
    2 ^ p * ‖computed (p := p) F' G' u v - G (fun k => F u k * F v k)‖ ≤ 3 * Es + 2 := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  obtain ⟨hu1, hu2⟩ := norm_computed_source_le F F' hF hF' hEs hu
  obtain ⟨hv1, hv2⟩ := norm_computed_source_le F F' hF hF' hEs hv
  have hFu : ‖F u‖ ≤ 1 / 4 := by
    calc ‖F u‖ ≤ ‖F‖ * ‖u‖ := F.le_opNorm u
      _ ≤ 1 * (1 / 4) := by gcongr
      _ = 1 / 4 := by norm_num
  set prod' : κ → ℂ := fun k => F' u k * F' v k with hprod'
  set prod : κ → ℂ := fun k => F u k * F v k with hprod
  set z := rdV p prod' with hz
  -- the product error
  have hpe : 2 ^ p * ‖prod' - prod‖ ≤ 2 * Es := by
    have h := norm_pointwise_mul_sub_le (F' u) (F u) (F' v) (F v)
    have hEs0 : 0 ≤ Es := le_trans (by positivity) hu2
    calc 2 ^ p * ‖prod' - prod‖ ≤ 2 ^ p * (‖F' u - F u‖ * ‖F' v‖ + ‖F u‖ * ‖F' v - F v‖) := by
          gcongr
      _ = (2 ^ p * ‖F' u - F u‖) * ‖F' v‖ + ‖F u‖ * (2 ^ p * ‖F' v - F v‖) := by ring
      _ ≤ Es * (26 / 100) + (1 / 4) * Es := by gcongr
      _ ≤ 2 * Es := by linarith
  -- the truncated product stays in the half ball
  have hz1 : ‖z‖ ≤ 1 / 2 := by
    calc ‖z‖ ≤ ‖prod'‖ := norm_rdV_le p prod'
      _ ≤ ‖F' u‖ * ‖F' v‖ := norm_pointwise_mul_le _ _
      _ ≤ (26 / 100) * (26 / 100) := by gcongr
      _ ≤ 1 / 2 := by norm_num
  have hze : 2 ^ p * ‖z - prod‖ ≤ 2 * Es + 2 := by
    have h1 := norm_rdV_sub_le p prod'
    calc 2 ^ p * ‖z - prod‖ = 2 ^ p * ‖(z - prod') + (prod' - prod)‖ := by
          rw [sub_add_sub_cancel]
      _ ≤ 2 ^ p * (‖z - prod'‖ + ‖prod' - prod‖) := by
          gcongr
          exact norm_add_le _ _
      _ = 2 ^ p * ‖z - prod'‖ + 2 ^ p * ‖prod' - prod‖ := by ring
      _ ≤ 2 + 2 * Es := add_le_add h1 hpe
      _ = 2 * Es + 2 := by ring
  -- insert the exact opposite transform at the computed input
  have hGz := hG' z hz1
  have hGe : 2 ^ p * ‖G z - G prod‖ ≤ 2 * Es + 2 := by
    calc 2 ^ p * ‖G z - G prod‖ = 2 ^ p * ‖G (z - prod)‖ := by rw [map_sub]
      _ ≤ 2 ^ p * (‖G‖ * ‖z - prod‖) := by
          gcongr
          exact G.le_opNorm _
      _ ≤ 2 ^ p * (1 * ‖z - prod‖) := by gcongr
      _ = 2 ^ p * ‖z - prod‖ := by ring
      _ ≤ 2 * Es + 2 := hze
  calc 2 ^ p * ‖computed (p := p) F' G' u v - G prod‖
      = 2 ^ p * ‖(G' z - G z) + (G z - G prod)‖ := by
        rw [sub_add_sub_cancel]
        rfl
    _ ≤ 2 ^ p * (‖G' z - G z‖ + ‖G z - G prod‖) := by
        gcongr
        exact norm_add_le _ _
    _ = 2 ^ p * ‖G' z - G z‖ + 2 ^ p * ‖G z - G prod‖ := by ring
    _ ≤ Es + (2 * Es + 2) := add_le_add hGz hGe
    _ = 3 * Es + 2 := by ring

end Recovery

/-! ### The exact product -/

section Product

variable {κ : Type*} [Fintype κ] {S k p : ℕ} [NeZero S] {Es : ℝ}

/-- The quarter-scaled digit vector `2^(-(k+2)) u`. -/
noncomputable def scaledDigits (S k : ℕ) [NeZero S] (ds : List ℕ) : ZMod S → ℂ :=
  fun j => vecZ S ds j / 2 ^ (k + 2)

theorem norm_vecZ_le {ds : List ℕ} (hds : ∀ d ∈ ds, d < 2 ^ k) (j : ZMod S) :
    ‖vecZ S ds j‖ ≤ 2 ^ k := by
  unfold vecZ
  rw [Complex.norm_natCast]
  rw [List.getD_eq_getElem?_getD]
  rcases h : ds[j.val]? with _ | d
  · simp
  · simp only [Option.getD_some]
    exact_mod_cast (hds d (List.mem_of_getElem? h)).le

theorem norm_scaledDigits_le {ds : List ℕ} (hds : ∀ d ∈ ds, d < 2 ^ k) :
    ‖scaledDigits S k ds‖ ≤ 1 / 4 := by
  rw [pi_norm_le_iff_of_nonneg (by norm_num)]
  intro j
  unfold scaledDigits
  rw [norm_div, norm_pow, Complex.norm_ofNat, pow_add]
  have h := norm_vecZ_le (S := S) hds j
  rw [div_le_iff₀ (by positivity)]
  calc ‖vecZ S ds j‖ ≤ 2 ^ k := h
    _ = 1 / 4 * (2 ^ k * 2 ^ 2) := by ring

/-- The quarter scalings collect into `1/16` in front of the normalised convolution. -/
theorem cconv_scaledDigits (dx dy : List ℕ) (i : ZMod S) :
    (16 * (S : ℂ)) * (cconv (scaledDigits S k dx) (scaledDigits S k dy) i / (S : ℂ) ^ 2) =
      scaledConv S k dx dy i := by
  have hS : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne S)
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  simp only [scaledConv, cconv, scaledDigits, pow_add, Finset.sum_div, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  field_simp
  ring

variable (F : (ZMod S → ℂ) →L[ℂ] (κ → ℂ)) (F' : (ZMod S → ℂ) → (κ → ℂ))
  (G : (κ → ℂ) →L[ℂ] (ZMod S → ℂ)) (G' : (κ → ℂ) → (ZMod S → ℂ))

/-- The computed normalised convolution: the exact numerator scaling `16 S` of the
computed opposite transform. -/
noncomputable def computedConv (x y : List Bool) : ZMod S → ℂ :=
  (16 * (S : ℂ)) • computed (p := p) F' G' (scaledDigits S k (digitsOf k x))
    (scaledDigits S k (digitsOf k y))

/-- The exact product from the computed pipeline: rounding `2^(2k) S` times the
computed normalised convolution gives the digits of the product, provided
`2^(2k+4) S² (3 E_s + 2) < 2^(p-1)`. -/
theorem exact_product (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ S + 1)
    (hF : ‖F‖ ≤ 1) (hF' : ∀ u : ZMod S → ℂ, ‖u‖ ≤ 1 / 2 → 2 ^ p * ‖F' u - F u‖ ≤ Es)
    (hG : ‖G‖ ≤ 1) (hG' : ∀ y : κ → ℂ, ‖y‖ ≤ 1 / 2 → 2 ^ p * ‖G' y - G y‖ ≤ Es)
    (hEs : Es ≤ 2 ^ p / 100)
    (hconv : ∀ u v : ZMod S → ℂ,
      G (fun κ => F u κ * F v κ) = fun i => cconv u v i / (S : ℂ) ^ 2)
    (hfinal : (2 : ℝ) ^ (2 * k + 4) * S ^ 2 * (3 * Es + 2) < 2 ^ p / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin S =>
      (round (((2 : ℂ) ^ (2 * k) * S) *
        computedConv (p := p) (k := k) F' G' x y (i.val : ZMod S)).re).toNat) =
      Machine.binaryValue x * Machine.binaryValue y := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set u := scaledDigits S k (digitsOf k x) with hu
  set v := scaledDigits S k (digitsOf k y) with hv
  have hu1 : ‖u‖ ≤ 1 / 4 := norm_scaledDigits_le (digitsOf_lt hk x)
  have hv1 : ‖v‖ ≤ 1 / 4 := norm_scaledDigits_le (digitsOf_lt hk y)
  have herr := recovery_error F F' G G' hF hF' hG hG' hEs hu1 hv1
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have hEs0 : 0 ≤ Es := le_trans (by positivity) (hF' 0 (by simp))
  refine product_from_approx hk hS (δ := 16 * S * (3 * Es + 2) / 2 ^ p) ?_ ?_
  · intro i
    have hpt : ‖computed (p := p) F' G' u v i - G (fun κ => F u κ * F v κ) i‖ ≤
        ‖computed (p := p) F' G' u v - G (fun κ => F u κ * F v κ)‖ :=
      norm_le_pi_norm (computed (p := p) F' G' u v - G (fun κ => F u κ * F v κ)) i
    have hid : scaledConv S k (digitsOf k x) (digitsOf k y) i =
        (16 * (S : ℂ)) * G (fun κ => F u κ * F v κ) i := by
      rw [← cconv_scaledDigits, hconv]
    have hcc : computedConv (p := p) (k := k) F' G' x y i =
        (16 * (S : ℂ)) * computed F' G' u v i := rfl
    rw [hcc, hid, ← mul_sub, norm_mul, le_div_iff₀ hp]
    have h16 : ‖(16 * (S : ℂ))‖ = 16 * S := by
      rw [norm_mul, Complex.norm_natCast, Complex.norm_ofNat]
    rw [h16]
    calc 16 * (S : ℝ) * ‖computed F' G' u v i - G (fun κ => F u κ * F v κ) i‖ * 2 ^ p
        = 16 * S * (2 ^ p * ‖computed F' G' u v i - G (fun κ => F u κ * F v κ) i‖) := by ring
      _ ≤ 16 * S * (2 ^ p * ‖computed F' G' u v - G (fun κ => F u κ * F v κ)‖) := by gcongr
      _ ≤ 16 * S * (3 * Es + 2) := by gcongr
  · rw [← mul_div_assoc, div_lt_iff₀ hp]
    calc (2 : ℝ) ^ (2 * k) * S * (16 * S * (3 * Es + 2))
        = 2 ^ (2 * k + 4) * S ^ 2 * (3 * Es + 2) := by ring
      _ < 2 ^ p / 2 := hfinal
      _ = 1 / 2 * 2 ^ p := by ring

end Product

/-! ### The size relations -/

section Sizes

/-- `k · 2^(-3k/4) → 0`, so `896 k < 2^(3k/4)` eventually. -/
theorem eventually_threshold :
    ∀ᶠ k : ℕ in atTop, 896 * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 4) < 2 ^ k := by
  have hb : 0 < 3 * Real.log 2 / 4 := by positivity
  have h := (tendsto_rpow_mul_exp_neg_mul_atTop_nhds_zero 1 _ hb).comp
    tendsto_natCast_atTop_atTop
  have h' := h.const_mul 896
  rw [mul_zero] at h'
  have hev := h'.eventually (gt_mem_nhds (by norm_num : (0 : ℝ) < 1))
  filter_upwards [hev] with k hk
  simp only [Function.comp, Real.rpow_one] at hk
  have hpos : (0 : ℝ) < 2 ^ k := by positivity
  have hq : (0 : ℝ) < (2 : ℝ) ^ ((k : ℝ) / 4) := by positivity
  have e : Real.exp (-(3 * Real.log 2 / 4) * k) = (2 : ℝ) ^ ((k : ℝ) / 4) / 2 ^ k := by
    rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.rpow_natCast,
      Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 2), ← Real.exp_sub]
    congr 1
    ring
  rw [e] at hk
  rw [← div_lt_one hpos]
  calc 896 * (k : ℝ) * 2 ^ ((k : ℝ) / 4) / 2 ^ k
      = 896 * (k * (2 ^ ((k : ℝ) / 4) / 2 ^ k)) := by ring
    _ < 1 := hk

/-- The manuscript's parameter relations give the margins used above: with
`E_s = 9 · 2^γ T L`, `S ≤ T < 2^k`, `1 ≤ L < k`, `γ ≤ k/4` and `p = 6k`, the
disk margin `E_s ≤ 2^p / 100` and the recovery condition hold once
`896 k 2^(k/4) < 2^k`. -/
theorem margins_of_sizes {S T L γ k : ℕ} (hST : S ≤ T) (hT2 : 2 ≤ T) (hTk : T < 2 ^ k)
    (hL1 : 1 ≤ L) (hLk : L < k) (hγ : (γ : ℝ) ≤ k / 4)
    (hthr : 896 * (k : ℝ) * (2 : ℝ) ^ ((k : ℝ) / 4) < 2 ^ k) :
    (9 * (2 : ℝ) ^ γ * T * L ≤ 2 ^ (6 * k) / 100) ∧
      (2 : ℝ) ^ (2 * k + 4) * S ^ 2 * (3 * (9 * (2 : ℝ) ^ γ * T * L) + 2) < 2 ^ (6 * k) / 2 := by
  have hq : (2 : ℝ) ^ γ ≤ (2 : ℝ) ^ ((k : ℝ) / 4) := by
    rw [← Real.rpow_natCast]
    exact Real.rpow_le_rpow_of_exponent_le (by norm_num) hγ
  have hTr : (T : ℝ) < 2 ^ k := by exact_mod_cast hTk
  have hSr : (S : ℝ) ≤ T := by exact_mod_cast hST
  have hLr : (L : ℝ) < k := by exact_mod_cast hLk
  have hL1r : (1 : ℝ) ≤ L := by exact_mod_cast hL1
  have hT2r : (2 : ℝ) ≤ T := by exact_mod_cast hT2
  have hk1 : 1 ≤ k := by omega
  have hkp : (0 : ℝ) < 2 ^ k := by positivity
  have hS0 : (0 : ℝ) ≤ S := Nat.cast_nonneg _
  have h2k : (2 : ℝ) ≤ 2 ^ k := by
    calc (2 : ℝ) = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := pow_le_pow_right₀ (by norm_num) hk1
  -- `X = 2^γ T L` is at least `2` and at most `m = k 2^(k/4) 2^k`
  have hX2 : 2 ≤ (2 : ℝ) ^ γ * T * L := by
    have h1 : (1 : ℝ) ≤ 2 ^ γ := one_le_pow₀ (by norm_num)
    calc (2 : ℝ) = 1 * 2 * 1 := by ring
      _ ≤ 2 ^ γ * T * L := by gcongr
  have hXm : (2 : ℝ) ^ γ * T * L ≤ (k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k := by
    calc (2 : ℝ) ^ γ * T * L ≤ 2 ^ ((k : ℝ) / 4) * 2 ^ k * k := by gcongr
      _ = (k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k := by ring
  have hm0 : (0 : ℝ) ≤ (k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k := by positivity
  -- the threshold as `896 m < P` with `P = 2^k 2^k`
  have hthr' : 896 * ((k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k) < (2 : ℝ) ^ k * 2 ^ k := by
    have := mul_lt_mul_of_pos_right hthr hkp
    calc 896 * ((k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k)
        = 896 * (k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k := by ring
      _ < 2 ^ k * 2 ^ k := this
  -- `2^(6k) = P³`, `4 ≤ P`
  have hpow : (2 : ℝ) ^ (6 * k) = (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) := by
    rw [show 6 * k = k + k + (k + k) + (k + k) by ring]
    simp only [pow_add]
  have hP4 : (4 : ℝ) ≤ 2 ^ k * 2 ^ k := by
    calc (4 : ℝ) = 2 * 2 := by norm_num
      _ ≤ 2 ^ k * 2 ^ k := by gcongr
  have hP0 : (0 : ℝ) ≤ 2 ^ k * 2 ^ k := by positivity
  have hP2 : ((2 : ℝ) ^ k * 2 ^ k) * 2 ≤ (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) := by
    have h4 : (2 : ℝ) ≤ (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) := by nlinarith
    calc ((2 : ℝ) ^ k * 2 ^ k) * 2 ≤ (2 ^ k * 2 ^ k) * ((2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k)) := by
          gcongr
      _ = (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) := by ring
  have hp4 : (2 : ℝ) ^ (2 * k + 4) = 16 * (2 ^ k * 2 ^ k) := by
    rw [show 2 * k + 4 = k + k + 4 by ring, pow_add, pow_add]
    ring
  have hS2 : (S : ℝ) ^ 2 ≤ 2 ^ k * 2 ^ k := by
    have : (S : ℝ) < 2 ^ k := lt_of_le_of_lt hSr hTr
    calc (S : ℝ) ^ 2 = S * S := sq _
      _ ≤ 2 ^ k * 2 ^ k := by gcongr
  refine ⟨?_, ?_⟩
  · calc 9 * (2 : ℝ) ^ γ * T * L = 9 * (2 ^ γ * T * L) := by ring
      _ ≤ 9 * ((k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k) := by linarith
      _ ≤ 2 ^ (6 * k) / 100 := by rw [hpow]; linarith
  · have h27 : 3 * (9 * ((2 : ℝ) ^ γ * T * L)) + 2 ≤ 28 * (2 ^ γ * T * L) := by linarith
    have hPP : (0 : ℝ) < (2 ^ k * 2 ^ k) * (2 ^ k * 2 ^ k) := by positivity
    have hlast := mul_lt_mul_of_pos_right hthr' hPP
    calc (2 : ℝ) ^ (2 * k + 4) * S ^ 2 * (3 * (9 * 2 ^ γ * T * L) + 2)
        = 16 * ((2 : ℝ) ^ k * 2 ^ k) * S ^ 2 * (3 * (9 * ((2 : ℝ) ^ γ * T * L)) + 2) := by
          rw [hp4]; ring
      _ ≤ 16 * ((2 : ℝ) ^ k * 2 ^ k) * ((2 : ℝ) ^ k * 2 ^ k) * (28 * ((2 : ℝ) ^ γ * T * L)) := by
          gcongr
      _ ≤ 16 * ((2 : ℝ) ^ k * 2 ^ k) * ((2 : ℝ) ^ k * 2 ^ k) *
          (28 * ((k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k)) := by gcongr
      _ = 896 * ((k : ℝ) * 2 ^ ((k : ℝ) / 4) * 2 ^ k) *
          (((2 : ℝ) ^ k * 2 ^ k) * ((2 : ℝ) ^ k * 2 ^ k)) / 2 := by ring
      _ < ((2 : ℝ) ^ k * 2 ^ k) * (((2 : ℝ) ^ k * 2 ^ k) * ((2 : ℝ) ^ k * 2 ^ k)) / 2 := by
          linarith
      _ = 2 ^ (6 * k) / 2 := by rw [hpow]; ring

end Sizes

end IntegerMultBounds.ExactRecovery
