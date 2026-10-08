import Mathlib.Tactic

/-! The radix-2 Cooley–Tukey transform as an executable recursion over any
commutative ring, proved equal to the quadratic-time definition whenever the
twiddle element satisfies `ω ^ N = 1`, with its ring-operation count in closed
form. The count is of ring multiplications and additions in the recursion,
with the twiddle powers `ω ^ k` taken as given; it is not a tape-step bound,
and nothing here addresses precision or the choice of `ω`. -/

namespace IntegerMultBounds.NLogN

variable {R : Type*} [CommRing R]

/-- The quadratic-time transform, for any element `ω`. -/
def dftFin {N : ℕ} (ω : R) (a : Fin N → R) : Fin N → R :=
  fun k => ∑ j, ω ^ (j.val * k.val) * a j

theorem pow_mod_eq {ω : R} {M : ℕ} (hω : ω ^ M = 1) (x : ℕ) :
    ω ^ x = ω ^ (x % M) := by
  conv_lhs => rw [← Nat.mod_add_div x M]
  rw [pow_add, pow_mul, hω, one_pow, mul_one]

/-- Even and odd positions of a length `2 ^ (n + 1)` vector. -/
def evenOddEquiv (n : ℕ) : Fin (2 ^ n) ⊕ Fin (2 ^ n) ≃ Fin (2 ^ (n + 1)) where
  toFun
    | .inl i => ⟨2 * i.val, by have := i.isLt; rw [pow_succ]; omega⟩
    | .inr i => ⟨2 * i.val + 1, by have := i.isLt; rw [pow_succ]; omega⟩
  invFun k :=
    if k.val % 2 = 0 then
      .inl ⟨k.val / 2, by have := k.isLt; have h2 := pow_succ 2 n; omega⟩
    else
      .inr ⟨k.val / 2, by have := k.isLt; have h2 := pow_succ 2 n; omega⟩
  left_inv := by
    rintro (i | i)
    · simp
    · simp
      exact Fin.ext (by show (2 * i.val + 1) / 2 = i.val; omega)
  right_inv := by
    intro k
    by_cases h : k.val % 2 = 0
    · simp only [h, ↓reduceIte]
      exact Fin.ext (by simp; omega)
    · simp only [h, ↓reduceIte]
      exact Fin.ext (by simp; omega)

def half (n : ℕ) (k : Fin (2 ^ (n + 1))) : Fin (2 ^ n) :=
  ⟨k.val % 2 ^ n, Nat.mod_lt _ (by positivity)⟩

/-- Decimation in time: transform the even and odd halves with `ω ^ 2`, then
combine with one multiplication and one addition per output. -/
def fft : (n : ℕ) → R → (Fin (2 ^ n) → R) → (Fin (2 ^ n) → R)
  | 0, _, a => a
  | n + 1, ω, a =>
    let E := fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inl i)))
    let O := fft n (ω ^ 2) (fun i => a (evenOddEquiv n (Sum.inr i)))
    fun k => E (half n k) + ω ^ k.val * O (half n k)

theorem pow_twiddle {ω : R} {n : ℕ} (hω : ω ^ (2 ^ (n + 1)) = 1) (i k : ℕ) :
    ω ^ (2 * i * k) = (ω ^ 2) ^ (i * (k % 2 ^ n)) := by
  rw [← pow_mul]
  conv_lhs => rw [← Nat.mod_add_div k (2 ^ n)]
  rw [show 2 * i * (k % 2 ^ n + 2 ^ n * (k / 2 ^ n)) =
      2 * (i * (k % 2 ^ n)) + 2 ^ (n + 1) * (i * (k / 2 ^ n)) by ring]
  rw [pow_add, pow_mul ω (2 ^ (n + 1)), hω, one_pow, mul_one]

/-- The fast recursion agrees with the quadratic definition. -/
theorem fft_eq_dftFin : ∀ (n : ℕ) (ω : R), ω ^ (2 ^ n) = 1 →
    ∀ a : Fin (2 ^ n) → R, fft n ω a = dftFin ω a
  | 0, ω, _, a => by
    funext k
    have hval : ∀ j : Fin (2 ^ 0), j.val = 0 := fun j => by
      have := j.isLt
      have h : (2 : ℕ) ^ 0 = 1 := pow_zero 2
      omega
    have hk : ∀ j : Fin (2 ^ 0), j = k := fun j => Fin.ext (by rw [hval j, hval k])
    simp only [fft, dftFin]
    rw [Finset.sum_eq_single k (fun j _ hj => absurd (hk j) hj)
      (fun h => absurd (Finset.mem_univ k) h)]
    rw [hval k]
    simp
  | n + 1, ω, hω, a => by
    funext k
    have hω2 : (ω ^ 2) ^ (2 ^ n) = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hω
    simp only [fft, fft_eq_dftFin n (ω ^ 2) hω2, dftFin, half]
    rw [← Fintype.sum_equiv (evenOddEquiv n)
      (fun j => ω ^ ((evenOddEquiv n j).val * k.val) * a (evenOddEquiv n j)) _
      (fun _ => rfl)]
    rw [Fintype.sum_sum_type, Finset.mul_sum]
    congr 1
    · apply Finset.sum_congr rfl
      intro i _
      simp only [evenOddEquiv, Equiv.coe_fn_mk]
      rw [pow_twiddle hω]
    · apply Finset.sum_congr rfl
      intro i _
      simp only [evenOddEquiv, Equiv.coe_fn_mk]
      rw [show (2 * i.val + 1) * k.val = 2 * i.val * k.val + k.val by ring,
        pow_add ω (2 * i.val * k.val) k.val, pow_twiddle hω]
      ring

/-- Ring operations of `fft`: each of the `2 ^ (n + 1)` outputs at the top
level costs one multiplication and one addition, on top of the two
half-size recursive calls. -/
def fftCost : ℕ → ℕ
  | 0 => 0
  | n + 1 => 2 * fftCost n + 2 * 2 ^ (n + 1)

theorem fftCost_eq (n : ℕ) : fftCost n = n * 2 ^ (n + 1) := by
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [fftCost, ih]
    ring

theorem fftCost_eq_log (n : ℕ) : fftCost n = 2 * 2 ^ n * Nat.log 2 (2 ^ n) := by
  rw [fftCost_eq, Nat.log_pow (by norm_num)]
  ring

theorem fftCost_le (n : ℕ) : fftCost n ≤ 2 * n * 2 ^ n := by
  rw [fftCost_eq]
  ring_nf
  exact le_refl _

end IntegerMultBounds.NLogN
