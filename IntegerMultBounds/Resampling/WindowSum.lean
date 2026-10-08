import IntegerMultBounds.Machine.GaussianLineValue
import IntegerMultBounds.NLogN.ExplicitNumeric

/-! The window sums computed by the Gaussian line machine are the numerical
map `Ã` of the resampling interface: with the weight words holding the
rounded weights `ρ(2^p·w)` of each window and the input words holding the
numerators of a grid vector `u` (cyclically extended by `m` records at both
ends), the two accumulator words of output `k` are `2^(p+1)` times the real
and imaginary parts of `resampANum s t m (resampTermNum p s t α) u k`. -/

namespace IntegerMultBounds.Resampling.WindowSum

open IntegerMultBounds.NLogN (rho0 rhoC resampWeight resampTermNum resampANum truncWindow resampCentre)
open IntegerMultBounds.Machine.GaussianLine (termR termI centre accR accI accR_signed accI_signed)
open IntegerMultBounds.Machine.TwosComplement (signed)

section Rounding

/-- Rounding toward zero of a dyadic rational is the truncated division. -/
theorem rho0_div_pow (n : ℤ) (p : ℕ) : rho0 ((n : ℝ) / 2 ^ p) = n.tdiv (2 ^ p) := by
  have hcast : ((2 : ℝ) ^ p) = ((2 ^ p : ℕ) : ℝ) := by push_cast; rfl
  have hz : ((2 ^ p : ℕ) : ℤ) = 2 ^ p := by push_cast; rfl
  unfold rho0
  split_ifs with h
  · have hn : 0 ≤ n := by
      by_contra hc
      push Not at hc
      have : (n : ℝ) / 2 ^ p < 0 := div_neg_of_neg_of_pos (by exact_mod_cast hc) (by positivity)
      linarith
    rw [hcast, Int.floor_div_natCast, Int.floor_intCast, hz, Int.tdiv_eq_ediv_of_nonneg hn]
  · have hn : n < 0 := by
      by_contra hc
      push Not at hc
      exact h (div_nonneg (by exact_mod_cast hc) (by positivity))
    rw [← neg_neg ((n : ℝ) / 2 ^ p), Int.ceil_neg, hcast, ← neg_div, ← Int.cast_neg, Int.floor_div_natCast,
      Int.floor_intCast, hz, ← Int.tdiv_eq_ediv_of_nonneg (by omega : 0 ≤ -n), Int.neg_tdiv, neg_neg]

end Rounding

section Terms

variable {s t : ℕ} [NeZero s] [NeZero t] (p : ℕ) (α : ℝ) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)

theorem rhoC_real (x : ℝ) : rhoC p (x : ℂ) = ((rho0 (2 ^ p * x) : ℝ) / 2 ^ p : ℝ) := by
  apply Complex.ext
  · rw [Complex.ofReal_re]; simp [rhoC]
  · rw [Complex.ofReal_im]; simp [rhoC, rho0]

include hu in
/-- One fixed-point term: its parts are truncated products over `2^p`. -/
theorem term_parts (k : ZMod t) (j : ℤ) :
    resampTermNum p s t α u k j =
      ⟨((rho0 (2 ^ p * resampWeight s t α k j) * ar j).tdiv (2 ^ p) : ℝ) / 2 ^ p,
       ((rho0 (2 ^ p * resampWeight s t α k j) * ai j).tdiv (2 ^ p) : ℝ) / 2 ^ p⟩ := by
  unfold resampTermNum
  rw [rhoC_real, hu]
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  apply Complex.ext
  · simp only [rhoC, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [← rho0_div_pow]
    congr 2
    push_cast
    field_simp
  · simp only [rhoC, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, zero_mul, add_zero]
    rw [← rho0_div_pow]
    congr 2
    push_cast
    field_simp

/-- A sum over an integer interval as a sum over a range. -/
theorem sum_Icc_eq_range (a : ℤ) (n : ℕ) (f : ℤ → ℂ) :
    ∑ j ∈ Finset.Icc a (a + n), f j = ∑ i ∈ Finset.range (n + 1), f (a + i) := by
  symm
  refine Finset.sum_nbij (fun i : ℕ => a + i) (fun i hi => ?_) (fun i _ j _ h => ?_) (fun b hb => ?_)
    (fun i _ => rfl)
  · simp only [Finset.mem_range] at hi; simp only [Finset.mem_Icc]; omega
  · simpa using h
  · simp only [Finset.coe_Icc, Set.mem_Icc] at hb
    refine ⟨(b - a).toNat, ?_, ?_⟩
    · simp only [Finset.coe_range, Set.mem_Iio]; omega
    · simp only; omega

theorem floor_centre (hst : s ≤ t) (k : ℕ) (hk : k < t) :
    ⌊resampCentre s t (k : ZMod t)⌋ = (centre s t k : ℤ) := by
  unfold resampCentre centre
  rw [ZMod.val_natCast_of_lt hk, show ((s : ℝ) * k / t) = ((s * k : ℕ) : ℝ) / ((t : ℕ) : ℝ) by push_cast; ring,
    Int.floor_div_natCast, Int.floor_natCast, Int.natCast_div]

end Terms

section Bridge

variable (wtWords uWords : List (List Bool)) (s t m p w W : ℕ) [NeZero s] [NeZero t] (α : ℝ)
  (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)
  (hwt' : ∀ k j, k < t → j < 2 * m + 1 →
    signed (wtWords.getD (k * (2 * m + 1) + j) []) =
      rho0 (2 ^ p * resampWeight s t α (k : ZMod t) ((centre s t k : ℤ) - m + j)))
  (hre : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q) []) = ar ((q : ℤ) - m))
  (him : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q + 1) []) = ai ((q : ℤ) - m))
  (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
  (hwt : ∀ x ∈ wtWords, x.length = w) (hul' : ∀ x ∈ uWords, x.length = w)
  (hwb : ∀ x ∈ wtWords, |signed x| ≤ 2 ^ p) (hub : ∀ x ∈ uWords, |signed x| ≤ 2 ^ p)
  (hwtl : wtWords.length = t * (2 * m + 1)) (hul : 2 * (s + 2 * m + 1) ≤ uWords.length)
  (hst : s ≤ t) (hs : 0 < s)

include hu hwt' hre hst hs hul in
/-- The real part of the window sum is the sum of the machine's real terms. -/
theorem sum_re (k : ℕ) (hk : k < t) :
    (∑ j ∈ truncWindow s t m (k : ZMod t), resampTermNum p s t α u (k : ZMod t) j).re =
      ((∑ j ∈ Finset.range (2 * m + 1), termR wtWords uWords s t m p k j : ℤ) : ℝ) / 2 ^ p := by
  have hcen : centre s t k < s := by
    unfold centre; exact Nat.div_lt_of_lt_mul (by nlinarith)
  unfold truncWindow
  rw [floor_centre hst k hk, show (centre s t k : ℤ) + m = (centre s t k : ℤ) - m + (2 * m : ℕ) by push_cast; ring,
    sum_Icc_eq_range, Complex.re_sum, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [term_parts p α u ar ai hu]
  simp only
  unfold termR
  rw [hwt' k j hk hj, show 2 * centre s t k + 2 * j = 2 * (centre s t k + j) by ring,
    hre (centre s t k + j) (by omega),
    show ((centre s t k + j : ℕ) : ℤ) - m = (centre s t k : ℤ) - m + j by push_cast; ring]

include hu hwt' him hst hs hul in
/-- The imaginary part of the window sum is the sum of the machine's imaginary terms. -/
theorem sum_im (k : ℕ) (hk : k < t) :
    (∑ j ∈ truncWindow s t m (k : ZMod t), resampTermNum p s t α u (k : ZMod t) j).im =
      ((∑ j ∈ Finset.range (2 * m + 1), termI wtWords uWords s t m p k j : ℤ) : ℝ) / 2 ^ p := by
  have hcen : centre s t k < s := by
    unfold centre; exact Nat.div_lt_of_lt_mul (by nlinarith)
  unfold truncWindow
  rw [floor_centre hst k hk, show (centre s t k : ℤ) + m = (centre s t k : ℤ) - m + (2 * m : ℕ) by push_cast; ring,
    sum_Icc_eq_range, Complex.im_sum, Int.cast_sum, Finset.sum_div]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_range] at hj
  rw [term_parts p α u ar ai hu]
  simp only
  unfold termI
  rw [hwt' k j hk hj, show 2 * centre s t k + 2 * j + 1 = 2 * (centre s t k + j) + 1 by ring,
    him (centre s t k + j) (by omega),
    show ((centre s t k + j : ℕ) : ℤ) - m = (centre s t k : ℤ) - m + j by push_cast; ring]

include hu hwt' hre him hw hwW hW hwt hul' hwb hub hwtl hul hst hs in
/-- The accumulator words of output `k` are `2^(p+1)` times the parts of the
numerical map `Ã` at `k`. -/
theorem accumulators_eq (k : ℕ) (hk : k < t) :
    resampANum s t m (resampTermNum p s t α) u (k : ZMod t) =
      ⟨(signed (accR wtWords uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1),
       (signed (accI wtWords uWords s t m p w W k (2 * m + 1)) : ℝ) / 2 ^ (p + 1)⟩ := by
  rw [accR_signed wtWords uWords s t m p w W hw hwW hW hwt hul' hwb hub hwtl hul hst hs k hk _ le_rfl,
    accI_signed wtWords uWords s t m p w W hw hwW hW hwt hul' hwb hub hwtl hul hst hs k hk _ le_rfl]
  have hr := sum_re wtWords uWords s t m p α u ar ai hu hwt' hre hul hst hs k hk
  have hi := sum_im wtWords uWords s t m p α u ar ai hu hwt' him hul hst hs k hk
  unfold resampANum
  rw [show (1 / 2 : ℂ) = ((1 / 2 : ℝ) : ℂ) by push_cast; rfl]
  apply Complex.ext
  · rw [Complex.re_ofReal_mul, hr]; dsimp only; rw [pow_succ]; ring
  · rw [Complex.im_ofReal_mul, hi]; dsimp only; rw [pow_succ]; ring

end Bridge

end IntegerMultBounds.Resampling.WindowSum
