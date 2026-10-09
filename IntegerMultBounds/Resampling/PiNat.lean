import IntegerMultBounds.Resampling.WeightNat

/-! Machin's sums in natural numbers, as the tape machine computes them:
`D_0 = ⌊2^q/m⌋`, `D_{k+1} = ⌊D_k/m²⌋`, the `k`-th term `⌊D_k/(2k+1)⌋`, and the
even and odd partial sums. The alternating sum of these nonincreasing terms
is nonnegative, so `piN` is a natural subtraction of the two. -/

namespace IntegerMultBounds.Resampling.PiNat

open PiApprox (atanSum piApprox)
open WeightTable (piQ)
open WeightNat (piN)

def dSeq (m q : ℕ) : ℕ → ℕ
  | 0 => 2 ^ q / m
  | k + 1 => dSeq m q k / (m * m)

theorem dSeq_eq (m q k : ℕ) : dSeq m q k = 2 ^ q / m ^ (2 * k + 1) := by
  induction k with
  | zero => simp [dSeq]
  | succ k ih => rw [dSeq, ih, Nat.div_div_eq_div_mul]; congr 1; ring

def term (m q k : ℕ) : ℕ := dSeq m q k / (2 * k + 1)

def evA (m q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => evA m q k + if k % 2 = 0 then term m q k else 0

def odA (m q : ℕ) : ℕ → ℕ
  | 0 => 0
  | k + 1 => odA m q k + if k % 2 = 1 then term m q k else 0

theorem term_anti (m q k : ℕ) : term m q (k + 1) ≤ term m q k := by
  unfold term
  calc dSeq m q (k + 1) / (2 * (k + 1) + 1) ≤ dSeq m q k / (2 * (k + 1) + 1) :=
        Nat.div_le_div_right (by rw [dSeq]; exact Nat.div_le_self _ _)
    _ ≤ dSeq m q k / (2 * k + 1) := Nat.div_le_div_left (by omega) (by omega)

theorem od_le_ev (m q K : ℕ) : odA m q K + (if K % 2 = 1 then term m q K else 0) ≤ evA m q K := by
  induction K with
  | zero => simp [evA, odA]
  | succ K ih =>
    have ha := term_anti m q K
    rcases Nat.mod_two_eq_zero_or_one K with h | h
    · have h1 : (K + 1) % 2 = 1 := by omega
      simp only [evA, odA, h, h1, ↓reduceIte] at ih ⊢
      simp at ih ⊢
      omega
    · have h1 : (K + 1) % 2 = 0 := by omega
      simp only [evA, odA, h, h1, ↓reduceIte] at ih ⊢
      simp at ih ⊢
      omega

theorem od_le_ev' (m q K : ℕ) : odA m q K ≤ evA m q K := le_trans (Nat.le_add_right _ _) (od_le_ev m q K)

theorem atanSum_nat (m q K : ℕ) : atanSum m q K = (evA m q K : ℤ) - odA m q K := by
  induction K with
  | zero => simp [atanSum, evA, odA]
  | succ K ih =>
    rw [atanSum, ih]
    have ht : (2 ^ q / m ^ (2 * K + 1) / (2 * K + 1) : ℕ) = term m q K := by rw [term, dSeq_eq]
    rw [ht]
    simp only [evA, odA]
    rcases Nat.mod_two_eq_zero_or_one K with h | h
    · have : Even K := Nat.even_iff.mpr h
      rw [this.neg_one_pow]; simp only [h]; push_cast; ring
    · have : Odd K := Nat.odd_iff.mpr h
      rw [this.neg_one_pow]; simp only [h]; push_cast; ring

/-- `A_m = evA − odA` as a natural number. -/
def atanN (m q K : ℕ) : ℕ := evA m q K - odA m q K

theorem atanSum_eq_atanN (m q K : ℕ) : atanSum m q K = (atanN m q K : ℤ) := by
  rw [atanSum_nat, atanN, Nat.cast_sub (od_le_ev' m q K)]

theorem piN_eq (p : ℕ) (hp : 2 ≤ p) :
    piN p = 16 * atanN 5 (5 * p) (5 * p) - 4 * atanN 239 (5 * p) (5 * p) := by
  have h0 := WeightTable.piQ_nonneg p hp
  have e : piQ p = 16 * (atanN 5 (5 * p) (5 * p) : ℤ) - 4 * atanN 239 (5 * p) (5 * p) := by
    rw [piQ, piApprox, atanSum_eq_atanN, atanSum_eq_atanN]; ring
  rw [e] at h0
  have hle : 4 * atanN 239 (5 * p) (5 * p) ≤ 16 * atanN 5 (5 * p) (5 * p) := by
    have : (4 * (atanN 239 (5 * p) (5 * p) : ℤ)) ≤ 16 * atanN 5 (5 * p) (5 * p) := by linarith
    exact_mod_cast this
  unfold piN
  rw [e, show (16 : ℤ) * (atanN 5 (5 * p) (5 * p) : ℤ) - 4 * atanN 239 (5 * p) (5 * p) =
      ((16 * atanN 5 (5 * p) (5 * p) - 4 * atanN 239 (5 * p) (5 * p) : ℕ) : ℤ) by
    push_cast [Nat.cast_sub hle]; ring]
  exact Int.toNat_natCast _

end IntegerMultBounds.Resampling.PiNat
