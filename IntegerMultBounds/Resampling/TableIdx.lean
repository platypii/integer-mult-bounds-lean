import IntegerMultBounds.Resampling.WeightNat

/-! Natural-number formulas for the exponent numerators of the weight tables,
as the table machines compute them without signs: the Gaussian numerator
`(s k − t j)²` with `j = ⌊sk/t⌋ − m + i` splits at `i = m`, and the centered
residue `s β(x) = rr x` has magnitude `min (u, s − u)` with `u = t x mod s`. -/

namespace IntegerMultBounds.Resampling.TableIdx

open WeightTable (rr)

/-- The Gaussian numerator in naturals. -/
theorem gauss_num (s t m k i : ℕ) (ht : 0 < t) :
    ((((s : ℤ) * k - t * ((s * k / t : ℕ) - m + i)) ^ 2).toNat) =
      if i ≤ m then (s * k % t + t * (m - i)) ^ 2 else (t * (i - m) - s * k % t) ^ 2 := by
  have hdm := Nat.div_add_mod (s * k) t
  have hlt := Nat.mod_lt (s * k) ht
  set c := s * k / t
  set r := s * k % t
  have e : (s : ℤ) * k - t * ((c : ℤ) - m + i) = (r : ℤ) + t * ((m : ℤ) - i) := by
    have : ((s * k : ℕ) : ℤ) = t * c + r := by exact_mod_cast hdm.symm
    push_cast at this; rw [this]; ring
  rw [e]
  split_ifs with h
  · rw [show (r : ℤ) + t * ((m : ℤ) - i) = ((r + t * (m - i) : ℕ) : ℤ) by push_cast [Nat.cast_sub h]; ring]
    rw [← Nat.cast_pow, Int.toNat_natCast]
  · have hge : r ≤ t * (i - m) := by
      have : 1 ≤ i - m := by omega
      nlinarith
    rw [show (r : ℤ) + t * ((m : ℤ) - i) = -((t * (i - m) - r : ℕ) : ℤ) by
      push_cast [Nat.cast_sub hge, Nat.cast_sub (by omega : m ≤ i)]; ring]
    rw [neg_sq, ← Nat.cast_pow, Int.toNat_natCast]

/-- The residue of `t x` modulo `s`, as a natural number. -/
def res (s t : ℕ) (x : ℤ) : ℕ := ((t * x) % s).toNat

theorem res_lt (s t : ℕ) (hs : 0 < s) (x : ℤ) : res s t x < s := by
  unfold res
  have h1 := Int.emod_nonneg (t * x) (by omega : (s : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (t * x) (by omega : (0 : ℤ) < s)
  omega

/-- The centered residue: `rr x = u` when `2u < s`, else `u − s`. -/
theorem rr_eq (s t : ℕ) (hs : 0 < s) (x : ℤ) :
    rr s t x = if 2 * res s t x < s then (res s t x : ℤ) else (res s t x : ℤ) - s := by
  have h1 := Int.emod_nonneg (t * x) (by omega : (s : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos (t * x) (by omega : (0 : ℤ) < s)
  have hdm : (t * x) % (s : ℤ) + s * ((t * x) / s) = t * x := Int.emod_add_mul_ediv _ _
  have hres : (res s t x : ℤ) = (t * x) % s := by unfold res; exact Int.toNat_of_nonneg h1
  unfold rr
  set u := (t * x) % s
  set q := (t * x) / s
  -- (2 t x + s) / (2 s) = q + [2u ≥ s]
  have key : (2 * (t : ℤ) * x + s) / ((2 * s : ℕ) : ℤ) = q + if 2 * res s t x < s then 0 else 1 := by
    have e : 2 * (t : ℤ) * x + s = (2 * u + s) + q * (2 * s) := by linarith
    push_cast
    rw [e, Int.add_mul_ediv_right _ _ (by omega)]
    split_ifs with hc
    · rw [Int.ediv_eq_zero_of_lt (by omega) (by omega)]; ring
    · rw [show 2 * u + (s : ℤ) = (2 * u - s) + 1 * (2 * s) by ring, Int.add_mul_ediv_right _ _ (by omega),
        Int.ediv_eq_zero_of_lt (by omega) (by omega)]; ring
  rw [key]
  have : (t : ℤ) * x = s * q + u := by linarith
  split_ifs with hc <;> rw [hres] <;> linarith

/-- `|rr x| = min (u, s − u)`. -/
theorem rr_sq (s t : ℕ) (hs : 0 < s) (x : ℤ) :
    (rr s t x) ^ 2 = ((if 2 * res s t x < s then res s t x else s - res s t x : ℕ) : ℤ) ^ 2 := by
  have hl := res_lt s t hs x
  rw [rr_eq s t hs x]
  split_ifs with hc
  · rfl
  · rw [Nat.cast_sub hl.le]; ring

end IntegerMultBounds.Resampling.TableIdx
