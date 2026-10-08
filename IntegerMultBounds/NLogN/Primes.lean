import Mathlib.NumberTheory.Bertrand
import Mathlib.Tactic

/-! Prime selection by Bertrand's postulate. From any `x ≥ 1`, a chain of
primes `x < t₁ < t₂ < ⋯` with `tᵢ ≤ 2ⁱ x` exists; its members are pairwise
coprime, odd when `x ≥ 2`, and the product of the first `d` lies at least
`x^d` (strictly above for `d ≥ 1`) and at most `2^(d(d+1)/2) x^d`. Only existence is proved: no
procedure for finding the primes within a cost bound is given. -/

namespace IntegerMultBounds.NLogN

/-- The chain of primes; `primeChain x 0 = x` is the seed, not a prime. -/
noncomputable def primeChain (x : ℕ) : ℕ → ℕ
  | 0 => x
  | i + 1 =>
    if h : primeChain x i = 0 then 0
    else Classical.choose (Nat.exists_prime_lt_and_le_two_mul (primeChain x i) h)

variable {x : ℕ}

theorem primeChain_pos (hx : 1 ≤ x) (i : ℕ) : 0 < primeChain x i := by
  induction i with
  | zero => simpa [primeChain]
  | succ i ih =>
    have hne : primeChain x i ≠ 0 := by omega
    simp only [primeChain, hne, ↓reduceDIte]
    have := Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (primeChain x i) hne)
    exact this.1.pos

theorem primeChain_spec (hx : 1 ≤ x) (i : ℕ) :
    (primeChain x (i + 1)).Prime ∧ primeChain x i < primeChain x (i + 1) ∧
      primeChain x (i + 1) ≤ 2 * primeChain x i := by
  have hne : primeChain x i ≠ 0 := by have := primeChain_pos hx i; omega
  simp only [primeChain, hne, ↓reduceDIte]
  exact Classical.choose_spec (Nat.exists_prime_lt_and_le_two_mul (primeChain x i) hne)

theorem primeChain_prime (hx : 1 ≤ x) (i : ℕ) : (primeChain x (i + 1)).Prime :=
  (primeChain_spec hx i).1

theorem primeChain_strictMono (hx : 1 ≤ x) : StrictMono (primeChain x) :=
  strictMono_nat_of_lt_succ fun i => (primeChain_spec hx i).2.1

theorem primeChain_gt (hx : 1 ≤ x) (i : ℕ) : x < primeChain x (i + 1) :=
  primeChain_strictMono hx (Nat.succ_pos i)

theorem primeChain_le (hx : 1 ≤ x) (i : ℕ) : primeChain x i ≤ 2 ^ i * x := by
  induction i with
  | zero => simp [primeChain]
  | succ i ih =>
    have := (primeChain_spec hx i).2.2
    rw [pow_succ]
    nlinarith

theorem exists_primes_chain (x : ℕ) (hx : 1 ≤ x) (d : ℕ) :
    ∃ t : Fin d → ℕ, (∀ i, (t i).Prime) ∧ StrictMono t ∧ (∀ i, x < t i) ∧
      (∀ i, t i ≤ 2 ^ (i.val + 1) * x) :=
  ⟨fun i => primeChain x (i.val + 1), fun i => primeChain_prime hx i,
    fun i j h => primeChain_strictMono hx (by simpa using h),
    fun i => primeChain_gt hx i, fun i => primeChain_le hx (i.val + 1)⟩

theorem primeChain_coprime (hx : 1 ≤ x) {i j : ℕ} (h : i ≠ j) :
    Nat.Coprime (primeChain x (i + 1)) (primeChain x (j + 1)) :=
  (Nat.coprime_primes (primeChain_prime hx i) (primeChain_prime hx j)).2
    fun e => h (by simpa using (primeChain_strictMono hx).injective e)

theorem coprime_prod_of_chain (hx : 1 ≤ x) (d : ℕ) :
    Nat.Coprime (primeChain x (d + 1)) (∏ i ∈ Finset.range d, primeChain x (i + 1)) :=
  Nat.Coprime.prod_right fun i hi =>
    primeChain_coprime hx (by have := Finset.mem_range.1 hi; omega)

theorem primeChain_prod_bounds (hx : 1 ≤ x) (d : ℕ) :
    x ^ d ≤ ∏ i ∈ Finset.range d, primeChain x (i + 1) ∧
      ∏ i ∈ Finset.range d, primeChain x (i + 1) ≤ 2 ^ (d * (d + 1) / 2) * x ^ d := by
  induction d with
  | zero => simp
  | succ d ih =>
    obtain ⟨h1, h2⟩ := ih
    rw [Finset.prod_range_succ]
    have hgt := primeChain_gt hx d
    have hle := primeChain_le hx (d + 1)
    have hexp : (d + 1) * (d + 2) / 2 = d * (d + 1) / 2 + (d + 1) := by
      have h := Nat.div_add_mod (d * (d + 1)) 2
      have hmod : d * (d + 1) % 2 = 0 := by
        rcases Nat.even_or_odd d with ⟨k, hk⟩ | ⟨k, hk⟩ <;> subst hk <;> ring_nf <;> omega
      have h' : (d + 1) * (d + 2) = d * (d + 1) + 2 * (d + 1) := by ring
      rw [h', Nat.add_mul_div_left _ _ two_pos]
    constructor
    · calc x ^ (d + 1) = x ^ d * x := pow_succ x d
        _ ≤ _ := Nat.mul_le_mul h1 hgt.le
    · calc _ ≤ 2 ^ (d * (d + 1) / 2) * x ^ d * (2 ^ (d + 1) * x) :=
            Nat.mul_le_mul h2 hle
        _ = 2 ^ (d * (d + 1) / 2 + (d + 1)) * x ^ (d + 1) := by ring
        _ = _ := by rw [hexp]

theorem primeChain_prod_gt (hx : 1 ≤ x) (d : ℕ) :
    x ^ (d + 1) < ∏ i ∈ Finset.range (d + 1), primeChain x (i + 1) := by
  rw [Finset.prod_range_succ, pow_succ]
  exact Nat.mul_lt_mul_of_le_of_lt (primeChain_prod_bounds hx d).1 (primeChain_gt hx d)
    (lt_of_lt_of_le (pow_pos (a := x) (by omega) d) (primeChain_prod_bounds hx d).1)

theorem primeChain_not_dvd_two (hx : 2 ≤ x) (i : ℕ) : ¬ 2 ∣ primeChain x (i + 1) := by
  intro h
  have hx1 : 1 ≤ x := by omega
  have hp := primeChain_prime hx1 i
  have hgt := primeChain_gt hx1 i
  rcases (Nat.dvd_prime hp).1 h with h2 | h2 <;> omega

end IntegerMultBounds.NLogN
