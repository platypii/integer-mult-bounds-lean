import IntegerMultBounds.Resampling.WindowSum

/-! The off-diagonal map `Ẽ` of the Neumann iteration on the Gaussian line
machine: run with stride one (`s` outputs over `s` inputs, so the window of
output `ℓ` is centred at `ℓ`), with the weight words holding the rounded
weights `ρ(2^p·exp(…))` of the off-diagonal terms and a zero word at the
centre of every window, the two accumulator words of output `ℓ` are `2^p`
times the real and imaginary parts of `offDiagNum m (offDiagTermNum p s t α) u ℓ`. -/

namespace IntegerMultBounds.Resampling.OffDiagSum

open IntegerMultBounds.NLogN (rho0 rhoC normExp offDiagTermNum offDiagNum offDiagWindow)
open IntegerMultBounds.Machine.GaussianLine (termR termI centre accR accI accR_signed accI_signed)
open IntegerMultBounds.Machine.TwosComplement (signed)
open WindowSum (rho0_div_pow rhoC_real sum_Icc_eq_range)

/-- With stride one the window centre is the output index. -/
theorem centre_self (s k : ℕ) (hs : 0 < s) : centre s s k = k := by
  unfold centre; exact Nat.mul_div_cancel_left k hs

section Terms

variable {s : ℕ} (p : ℕ) (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)

include hu in
/-- A rounded product of a rounded real weight with an input entry: its
parts are truncated products over `2^p`. -/
theorem round_term_parts (x : ℝ) (j : ℤ) :
    rhoC p (rhoC p (x : ℂ) * u j) =
      ⟨((rho0 (2 ^ p * x) * ar j).tdiv (2 ^ p) : ℝ) / 2 ^ p,
       ((rho0 (2 ^ p * x) * ai j).tdiv (2 ^ p) : ℝ) / 2 ^ p⟩ := by
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

/-- The off-diagonal sum over its window, with the excluded centre term
written as zero over the full interval, as a sum over a range. -/
theorem offDiag_sum_range (f : ℤ → ℂ) (m : ℕ) :
    ∑ h ∈ offDiagWindow m, f h =
      ∑ j ∈ Finset.range (2 * m + 1), (if (-(m : ℤ) + j) = 0 then 0 else f (-(m : ℤ) + j)) := by
  unfold offDiagWindow
  rw [Finset.sum_congr rfl (g := fun h => if h = 0 then 0 else f h)
      (fun h hh => by simp [Finset.ne_of_mem_erase hh]),
    Finset.sum_erase _ (by simp)]
  have h := sum_Icc_eq_range (-(m : ℤ)) (2 * m) (fun h => if h = 0 then 0 else f h)
  rw [show -(m : ℤ) + ((2 * m : ℕ) : ℤ) = m by push_cast; ring] at h
  exact h

end Terms

section Bridge

variable (wtWords uWords : List (List Bool)) (s t m p w W : ℕ) (α : ℝ)
  (u : ZMod s → ℂ) (ar ai : ℤ → ℤ)
  (hu : ∀ j : ℤ, u (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩)
  (hwt' : ∀ k j, k < s → j < 2 * m + 1 →
    signed (wtWords.getD (k * (2 * m + 1) + j) []) =
      if -(m : ℤ) + j = 0 then 0
      else rho0 (2 ^ p * Real.exp (normExp s t α (k : ZMod s).val (-(m : ℤ) + j))))
  (hre : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q) []) = ar ((q : ℤ) - m))
  (him : ∀ q, q < s + 2 * m → signed (uWords.getD (2 * q + 1) []) = ai ((q : ℤ) - m))
  (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
  (hwt : ∀ x ∈ wtWords, x.length = w) (hul' : ∀ x ∈ uWords, x.length = w)
  (hwb : ∀ x ∈ wtWords, |signed x| ≤ 2 ^ p) (hub : ∀ x ∈ uWords, |signed x| ≤ 2 ^ p)
  (hwtl : wtWords.length = s * (2 * m + 1)) (hul : 2 * (s + 2 * m + 1) ≤ uWords.length)
  (hs : 0 < s)

include hu hwt' hre him hs in
/-- One window term of output `k`: its parts are the machine's terms over `2^p`. -/
theorem term_eq (k j : ℕ) (hk : k < s) (hj : j < 2 * m + 1) :
    (if -(m : ℤ) + j = 0 then 0 else offDiagTermNum p s t α u (k : ZMod s) (-(m : ℤ) + j)) =
      ⟨(termR wtWords uWords s s m p k j : ℝ) / 2 ^ p, (termI wtWords uWords s s m p k j : ℝ) / 2 ^ p⟩ := by
  have hcen := centre_self s k hs
  unfold termR termI
  rw [hwt' k j hk hj, hcen, show 2 * k + 2 * j = 2 * (k + j) by ring,
    show 2 * (k + j) + 1 = 2 * (k + j) + 1 from rfl, hre (k + j) (by omega), him (k + j) (by omega)]
  split_ifs with h0
  · apply Complex.ext <;> simp
  · unfold offDiagTermNum
    rw [show (k : ZMod s) + ((-(m : ℤ) + j : ℤ) : ZMod s) = (((k : ℤ) + (-(m : ℤ) + j) : ℤ) : ZMod s) by
      push_cast; ring, round_term_parts p u ar ai hu,
      show ((k + j : ℕ) : ℤ) - m = (k : ℤ) + (-(m : ℤ) + j) by push_cast; ring]

include hu hwt' hre him hw hwW hW hwt hul' hwb hub hwtl hul hs in
/-- The accumulator words of output `k` are `2^p` times the parts of the
numerical off-diagonal map `Ẽ` at `k`. -/
theorem accumulators_eq (k : ℕ) (hk : k < s) :
    offDiagNum m (offDiagTermNum p s t α) u (k : ZMod s) =
      ⟨(signed (accR wtWords uWords s s m p w W k (2 * m + 1)) : ℝ) / 2 ^ p,
       (signed (accI wtWords uWords s s m p w W k (2 * m + 1)) : ℝ) / 2 ^ p⟩ := by
  rw [accR_signed wtWords uWords s s m p w W hw hwW hW hwt hul' hwb hub hwtl hul le_rfl hs k hk _ le_rfl,
    accI_signed wtWords uWords s s m p w W hw hwW hW hwt hul' hwb hub hwtl hul le_rfl hs k hk _ le_rfl]
  unfold offDiagNum
  rw [offDiag_sum_range]
  have ht := fun j (hj : j ∈ Finset.range (2 * m + 1)) =>
    term_eq wtWords uWords s t m p α u ar ai hu hwt' hre him hs k j hk (Finset.mem_range.mp hj)
  rw [Finset.sum_congr rfl ht]
  apply Complex.ext
  · rw [Complex.re_sum]; push_cast; rw [Finset.sum_div]
  · rw [Complex.im_sum]; push_cast; rw [Finset.sum_div]

end Bridge

end IntegerMultBounds.Resampling.OffDiagSum
