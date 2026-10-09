import IntegerMultBounds.Resampling.WeightTable

/-! The weight routine in natural numbers, as the tape machines compute it.
The Taylor terms of `exp (∓Y/2^q)` are `±M_n` with natural magnitudes
`M₀ = 2^q`, `M_{n+1} = ⌊M_n Y / (2^q (n+1))⌋`; the alternating sum is the
difference of the even and odd partial sums. -/

namespace IntegerMultBounds.Resampling.WeightNat

open ExpApprox (expTerm expApprox)
open WeightTable (piQ expPi)

/-- The natural magnitudes of the Taylor terms. -/
def mag (Y q : ℕ) : ℕ → ℕ
  | 0 => 2 ^ q
  | n + 1 => mag Y q n * Y / (2 ^ q * (n + 1))

theorem expTerm_pos (Y q n : ℕ) : expTerm (Y : ℤ) q n = (mag Y q n : ℤ) := by
  induction n with
  | zero => simp [expTerm, mag]
  | succ n ih =>
    simp only [expTerm, mag, ih]
    rw [Int.tdiv_eq_ediv_of_nonneg (by positivity)]
    push_cast; rfl

theorem expTerm_neg (Y q n : ℕ) : expTerm (-(Y : ℤ)) q n = (-1) ^ n * (mag Y q n : ℤ) := by
  induction n with
  | zero => simp [expTerm, mag]
  | succ n ih =>
    simp only [expTerm, mag, ih]
    rw [show (-1 : ℤ) ^ n * (mag Y q n : ℤ) * -(Y : ℤ) = -((-1) ^ n * ((mag Y q n * Y : ℕ) : ℤ)) by push_cast; ring,
      Int.neg_tdiv]
    rcases Nat.even_or_odd n with hn | hn
    · rw [hn.neg_one_pow, one_mul, Int.tdiv_eq_ediv_of_nonneg (by positivity), pow_succ, hn.neg_one_pow]
      push_cast; ring
    · rw [hn.neg_one_pow, neg_one_mul, Int.neg_tdiv, neg_neg, Int.tdiv_eq_ediv_of_nonneg (by positivity),
        pow_succ, hn.neg_one_pow]
      push_cast; ring

/-- Even and odd partial sums of the magnitudes. -/
def evenSum (Y q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => evenSum Y q n + if n % 2 = 0 then mag Y q n else 0

def oddSum (Y q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => oddSum Y q n + if n % 2 = 1 then mag Y q n else 0

def allSum (Y q : ℕ) : ℕ → ℕ
  | 0 => 0
  | n + 1 => allSum Y q n + mag Y q n

theorem expApprox_neg (Y q N : ℕ) : expApprox (-(Y : ℤ)) q N = (evenSum Y q N : ℤ) - oddSum Y q N := by
  induction N with
  | zero => simp [expApprox, evenSum, oddSum]
  | succ N ih =>
    rw [expApprox, Finset.sum_range_succ, ← expApprox, ih, expTerm_neg]
    simp only [evenSum, oddSum]
    rcases Nat.mod_two_eq_zero_or_one N with h | h
    · have : Even N := Nat.even_iff.mpr h
      rw [this.neg_one_pow]; simp only [h]; push_cast; ring
    · have : Odd N := Nat.odd_iff.mpr h
      rw [this.neg_one_pow]; simp only [h]; push_cast; ring

theorem expApprox_pos (Y q N : ℕ) : expApprox (Y : ℤ) q N = (allSum Y q N : ℤ) := by
  induction N with
  | zero => simp [expApprox, allSum]
  | succ N ih =>
    rw [expApprox, Finset.sum_range_succ, ← expApprox, ih, expTerm_pos]
    simp only [allSum]; push_cast; ring

section Positive

open Real WeightTable

theorem pow_gap (p : ℕ) (hp : 13 ≤ p) : 27 ^ p + 7 * p * 9 ^ p < 32 ^ p := by
  induction p, hp using Nat.le_induction with
  | base => norm_num
  | succ n hn ih =>
    rw [pow_succ, pow_succ, pow_succ]
    nlinarith [Nat.one_le_pow n 9 (by norm_num), Nat.one_le_pow n 27 (by norm_num)]

/-- The Taylor sum stays close to `2^q exp (-Y/2^q)` for `Y < p 2^q`. -/
theorem E_close (p Y : ℕ) (hY : Y < p * 2 ^ (5 * p)) :
    |(expApprox (-(Y : ℤ)) (5 * p) (7 * p) : ℝ) - 2 ^ (5 * p) * exp (((-(Y : ℤ) : ℤ) : ℝ) / 2 ^ (5 * p))| ≤
      7 * p * 3 ^ p + 9 ^ p := by
  have hq0 : (0 : ℝ) < 2 ^ (5 * p) := by positivity
  set xt : ℝ := (((-(Y : ℤ)) : ℤ) : ℝ) / 2 ^ (5 * p) with hxt
  have hY' : (Y : ℝ) < p * 2 ^ (5 * p) := by exact_mod_cast hY
  have hxtp : |xt| ≤ p := by
    rw [hxt, abs_div, abs_of_pos hq0, div_le_iff₀ hq0]; push_cast
    rw [abs_neg, abs_of_nonneg (by positivity)]; linarith
  have hE := ExpApprox.expApprox_err (-(Y : ℤ)) (5 * p) (7 * p)
  rw [← hxt] at hE
  have hexpx : exp |xt| ≤ 3 ^ p := (exp_le_exp.mpr hxtp).trans (exp_le_three_pow p)
  have hpow : |xt| ^ (7 * p) / ((7 * p).factorial : ℝ) ≤ exp p * (1 / 2) ^ (5 * p) := by
    have h := pow_div_fact_le p (5 * p)
    rw [show 2 * p + 5 * p = 7 * p by ring] at h
    refine le_trans ?_ h
    gcongr
  have hep : exp (p : ℝ) ≤ 3 ^ p := exp_le_three_pow p
  have hhalfpow : (2 : ℝ) ^ (5 * p) * (1 / 2) ^ (5 * p) = 1 := by rw [← mul_pow]; norm_num
  refine hE.trans ?_
  have t1 : ((7 * p : ℕ) : ℝ) * exp |xt| ≤ 7 * p * 3 ^ p := by push_cast; gcongr
  have t2 : 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p).factorial : ℝ) * exp |xt|) ≤ 9 ^ p := by
    calc 2 ^ (5 * p) * (|xt| ^ (7 * p) / ((7 * p).factorial : ℝ) * exp |xt|)
        ≤ 2 ^ (5 * p) * (exp p * (1 / 2) ^ (5 * p) * 3 ^ p) := by gcongr
      _ = (2 ^ (5 * p) * (1 / 2) ^ (5 * p)) * exp p * 3 ^ p := by ring
      _ ≤ 1 * 3 ^ p * 3 ^ p := by rw [hhalfpow]; gcongr
      _ = 9 ^ p := by rw [one_mul, ← mul_pow]; norm_num
  linarith

/-- Below the shortcut the alternating Taylor sum is positive. -/
theorem odd_le_even (p Y : ℕ) (hp : 13 ≤ p) (hY : Y < p * 2 ^ (5 * p)) :
    oddSum Y (5 * p) (7 * p) ≤ evenSum Y (5 * p) (7 * p) := by
  have h := E_close p Y hY
  rw [expApprox_neg] at h
  have hq0 : (0 : ℝ) < 2 ^ (5 * p) := by positivity
  have hY' : (Y : ℝ) < p * 2 ^ (5 * p) := by exact_mod_cast hY
  have hx : -(p : ℝ) ≤ (((-(Y : ℤ)) : ℤ) : ℝ) / 2 ^ (5 * p) := by
    rw [le_div_iff₀ hq0]; push_cast; linarith
  have hexp : exp (-(p : ℝ)) ≤ exp ((((-(Y : ℤ)) : ℤ) : ℝ) / 2 ^ (5 * p)) := exp_le_exp.mpr hx
  have he : exp (p : ℝ) ≤ 3 ^ p := exp_le_three_pow p
  have hgap : (27 ^ p + 7 * p * 9 ^ p : ℝ) < 32 ^ p := by exact_mod_cast pow_gap p hp
  have h32 : (32 : ℝ) ^ p = 2 ^ (5 * p) := by rw [pow_mul]; norm_num
  -- 2^q e^{-p} > error
  have hlow : 7 * p * (3 : ℝ) ^ p + 9 ^ p < 2 ^ (5 * p) * exp (-(p : ℝ)) := by
    rw [exp_neg, ← div_eq_mul_inv, lt_div_iff₀ (exp_pos _)]
    calc (7 * p * (3 : ℝ) ^ p + 9 ^ p) * exp p ≤ (7 * p * 3 ^ p + 9 ^ p) * 3 ^ p := by gcongr
      _ = 27 ^ p + 7 * p * 9 ^ p := by
          rw [add_mul, show (7 * p * (3 : ℝ) ^ p) * 3 ^ p = 7 * p * 9 ^ p by rw [mul_assoc, ← mul_pow]; norm_num,
            ← mul_pow]; norm_num; ring
      _ < 32 ^ p := hgap
      _ = 2 ^ (5 * p) := h32
  have hm : 2 ^ (5 * p) * exp (-(p : ℝ)) ≤ 2 ^ (5 * p) * exp ((((-(Y : ℤ)) : ℤ) : ℝ) / 2 ^ (5 * p)) :=
    mul_le_mul_of_nonneg_left hexp hq0.le
  have hl := (abs_le.mp h).1
  have : (0 : ℝ) ≤ (evenSum Y (5 * p) (7 * p) : ℝ) - oddSum Y (5 * p) (7 * p) := by
    have e : (((evenSum Y (5 * p) (7 * p) : ℤ) - (oddSum Y (5 * p) (7 * p) : ℤ) : ℤ) : ℝ) =
        (evenSum Y (5 * p) (7 * p) : ℝ) - oddSum Y (5 * p) (7 * p) := by push_cast; ring
    rw [e] at hl
    linarith
  have : (oddSum Y (5 * p) (7 * p) : ℝ) ≤ evenSum Y (5 * p) (7 * p) := by linarith
  exact_mod_cast this

end Positive

section NatForm

/-- `piQ` as a natural number. -/
def piN (p : ℕ) : ℕ := (piQ p).toNat

/-- The weight routine in natural numbers. -/
def expPiNat (neg : Bool) (p a b : ℕ) : ℕ :=
  if neg then
    (if p * 2 ^ (5 * p) ≤ piN p * a / b then 0
     else (evenSum (piN p * a / b) (5 * p) (7 * p) - oddSum (piN p * a / b) (5 * p) (7 * p)) / 2 ^ (4 * p))
  else allSum (piN p * a / b) (5 * p) (7 * p) / 2 ^ (4 * p)

theorem expPi_eq_nat (neg : Bool) (p a b : ℕ) (hp : 13 ≤ p) : expPi neg p a b = (expPiNat neg p a b : ℤ) := by
  have hP : piQ p = (piN p : ℤ) := (Int.toNat_of_nonneg (WeightTable.piQ_nonneg p (by omega))).symm
  have hY : (piQ p * a) / b = ((piN p * a / b : ℕ) : ℤ) := by
    rw [hP]; push_cast; rfl
  unfold expPi expPiNat
  simp only [hY]
  cases neg with
  | true =>
    simp only [ite_true]
    by_cases hs : p * 2 ^ (5 * p) ≤ piN p * a / b
    · have hs' : (p : ℤ) * 2 ^ (5 * p) ≤ ((piN p * a / b : ℕ) : ℤ) := by exact_mod_cast hs
      simp only [hs, hs', ↓reduceIte, Nat.cast_zero]
    · have hs' : ¬ (p : ℤ) * 2 ^ (5 * p) ≤ ((piN p * a / b : ℕ) : ℤ) := by exact_mod_cast hs
      simp only [hs, hs', ite_false]
      rw [expApprox_neg, ← Nat.cast_sub (odd_le_even p _ hp (by omega))]
      push_cast; rfl
  | false =>
    simp only [Bool.false_eq_true, ite_false]
    rw [expApprox_pos]; push_cast; rfl

end NatForm

section Tables

open WeightTable (tableA tableE tableD rr)

def tableANat (s t α p : ℕ) (k : ZMod t) (j : ℤ) : ℕ :=
  expPiNat true p (((s : ℤ) * k.val - t * j) ^ 2).toNat (α ^ 2 * t ^ 2) / α

def tableENat (s t α p : ℕ) (ℓ : ZMod s) (h : ℤ) : ℕ :=
  expPiNat true p (((α : ℤ) ^ 2 * ((t * h + rr s t ℓ.val) ^ 2 - (rr s t (ℓ.val + h)) ^ 2)).toNat) (s ^ 2)

def tableDNat (s t α p : ℕ) (ℓ : ZMod s) : ℕ :=
  expPiNat false p (((α : ℤ) ^ 2 * (rr s t ℓ.val) ^ 2).toNat) (s ^ 2) / 2 ^ (2 * α ^ 2)

theorem tableA_nat (s t α p : ℕ) (hp : 13 ≤ p) (k : ZMod t) (j : ℤ) :
    tableA s t α p k j = (tableANat s t α p k j : ℤ) := by
  unfold tableA tableANat
  rw [expPi_eq_nat _ _ _ _ hp]; push_cast; rfl

theorem tableE_nat (s t α p : ℕ) (hp : 13 ≤ p) (ℓ : ZMod s) (h : ℤ) :
    tableE s t α p ℓ h = (tableENat s t α p ℓ h : ℤ) := by
  unfold tableE tableENat
  rw [expPi_eq_nat _ _ _ _ hp]

theorem tableD_nat (s t α p : ℕ) (hp : 13 ≤ p) (ℓ : ZMod s) :
    tableD s t α p ℓ = (tableDNat s t α p ℓ : ℤ) := by
  unfold tableD tableDNat
  rw [expPi_eq_nat _ _ _ _ hp]; push_cast; rfl

end Tables

end IntegerMultBounds.Resampling.WeightNat
