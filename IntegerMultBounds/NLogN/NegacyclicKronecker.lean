import IntegerMultBounds.NLogN.Kronecker
import IntegerMultBounds.NLogN.FixedOps

/-! The negacyclic product by Kronecker substitution (the paper's Lemma 2.5),
exact arithmetic only. Proved: the integer negacyclic product is the fold
`c_k - c_{k+r}` of the acyclic product coefficients; for nonnegative vectors
with entries below `M`, those coefficients are the base-`B` digits, with
`B = r M² + 1`, of ONE integer product of the two Kronecker-packed values;
signed vectors reduce to four nonnegative products by splitting into positive
and negative parts; and the packed values are below `B^r`, with `B ≤ 2^(3p)`
for `M = 2^(p+1)` and `r < 2^(p-2)`. The complex case is the cast of the
integer case. Bit costs, the fixed-point scaling, and the real/imaginary
split of complex coefficients are not modeled. -/

namespace IntegerMultBounds.NLogN

section Negacyclic

variable {r : ℕ}

/-- The negacyclic product over `ℤ`, with the same sign convention as `negacyclicMul`. -/
def negacyclicMulZ (a b : Fin r → ℤ) : Fin r → ℤ :=
  fun k => ∑ i, (if i ≤ k then 1 else -1) * a i * b (k - i)

theorem negacyclicMul_intCast (a b : Fin r → ℤ) :
    negacyclicMul (fun i => (a i : ℂ)) (fun i => (b i : ℂ)) =
      fun k => ((negacyclicMulZ a b k : ℤ) : ℂ) := by
  funext k
  simp only [negacyclicMul, negacyclicMulZ, negaSign, negaIdx]
  push_cast
  refine Finset.sum_congr rfl fun i _ => ?_
  split_ifs <;> simp

/-- Coefficient `m` of the acyclic (polynomial) product. -/
def aconvZ (a b : Fin r → ℤ) (m : ℕ) : ℤ :=
  ∑ i : Fin r, ∑ j : Fin r, if i.val + j.val = m then a i * b j else 0

theorem aconvZ_inner_le (a b : Fin r → ℤ) (k i : Fin r) (h : i ≤ k) :
    (∑ j : Fin r, if i.val + j.val = k.val then a i * b j else 0) = a i * b (k - i) := by
  have hv : (k - i).val = k.val - i.val := Fin.coe_sub_iff_le.2 h
  rw [Finset.sum_eq_single (k - i)]
  · have hc : i.val + (k - i).val = k.val := by rw [hv]; have := Fin.le_def.1 h; omega
    simp only [hc, ↓reduceIte]
  · intro j _ hj
    have hc : ¬ (i.val + j.val = k.val) := fun hij => hj (Fin.ext (by rw [hv]; omega))
    simp only [hc, ↓reduceIte]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem aconvZ_inner_gt (a b : Fin r → ℤ) (k i : Fin r) (h : ¬ i ≤ k) :
    (∑ j : Fin r, if i.val + j.val = k.val then a i * b j else 0) = 0 := by
  have hik : k.val < i.val := by rw [Fin.le_def] at h; omega
  exact Finset.sum_eq_zero fun j _ => by
    have hc : ¬ (i.val + j.val = k.val) := by omega
    simp only [hc, ↓reduceIte]

theorem aconvZ_inner_wrap (a b : Fin r → ℤ) (k i : Fin r) (h : ¬ i ≤ k) :
    (∑ j : Fin r, if i.val + j.val = k.val + r then a i * b j else 0) = a i * b (k - i) := by
  have hik : k < i := by rw [Fin.lt_def]; rw [Fin.le_def] at h; omega
  have hv : (k - i).val = r + k.val - i.val := Fin.coe_sub_iff_lt.2 hik
  have hi := i.isLt
  rw [Finset.sum_eq_single (k - i)]
  · have hc : i.val + (k - i).val = k.val + r := by rw [hv]; omega
    simp only [hc, ↓reduceIte]
  · intro j _ hj
    have hc : ¬ (i.val + j.val = k.val + r) := fun hij => hj (Fin.ext (by rw [hv]; omega))
    simp only [hc, ↓reduceIte]
  · intro h'; exact absurd (Finset.mem_univ _) h'

theorem aconvZ_inner_wrap_zero (a b : Fin r → ℤ) (k i : Fin r) (h : i ≤ k) :
    (∑ j : Fin r, if i.val + j.val = k.val + r then a i * b j else 0) = 0 := by
  have hik := Fin.le_def.1 h
  exact Finset.sum_eq_zero fun j _ => by
    have hc : ¬ (i.val + j.val = k.val + r) := by have := j.isLt; omega
    simp only [hc, ↓reduceIte]

/-- Folding the acyclic product with the sign of `y^r = -1`. -/
theorem negacyclicMulZ_eq_fold (a b : Fin r → ℤ) (k : Fin r) :
    negacyclicMulZ a b k = aconvZ a b k.val - aconvZ a b (k.val + r) := by
  unfold negacyclicMulZ aconvZ
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : i ≤ k
  · rw [aconvZ_inner_le a b k i h, aconvZ_inner_wrap_zero a b k i h]; simp only [h, ↓reduceIte]; ring
  · rw [aconvZ_inner_gt a b k i h, aconvZ_inner_wrap a b k i h]; simp only [h, ↓reduceIte]; ring

/-! ### Bilinearity and the sign split -/

theorem negacyclicMulZ_add_left (a a' b : Fin r → ℤ) :
    negacyclicMulZ (a + a') b = negacyclicMulZ a b + negacyclicMulZ a' b := by
  funext k; simp only [negacyclicMulZ, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem negacyclicMulZ_add_right (a b b' : Fin r → ℤ) :
    negacyclicMulZ a (b + b') = negacyclicMulZ a b + negacyclicMulZ a b' := by
  funext k; simp only [negacyclicMulZ, Pi.add_apply, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem negacyclicMulZ_neg_left (a b : Fin r → ℤ) :
    negacyclicMulZ (-a) b = -negacyclicMulZ a b := by
  funext k; simp only [negacyclicMulZ, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem negacyclicMulZ_neg_right (a b : Fin r → ℤ) :
    negacyclicMulZ a (-b) = -negacyclicMulZ a b := by
  funext k; simp only [negacyclicMulZ, Pi.neg_apply, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

theorem negacyclicMulZ_sub_left (a a' b : Fin r → ℤ) :
    negacyclicMulZ (a - a') b = negacyclicMulZ a b - negacyclicMulZ a' b := by
  rw [sub_eq_add_neg, negacyclicMulZ_add_left, negacyclicMulZ_neg_left, sub_eq_add_neg]

theorem negacyclicMulZ_sub_right (a b b' : Fin r → ℤ) :
    negacyclicMulZ a (b - b') = negacyclicMulZ a b - negacyclicMulZ a b' := by
  rw [sub_eq_add_neg, negacyclicMulZ_add_right, negacyclicMulZ_neg_right, sub_eq_add_neg]

/-- The positive part of an integer vector, as a natural vector cast back. -/
def posPart (a : Fin r → ℤ) : Fin r → ℤ := fun i => ((a i).toNat : ℤ)

/-- The negative part of an integer vector, as a natural vector cast back. -/
def negPart (a : Fin r → ℤ) : Fin r → ℤ := fun i => ((-a i).toNat : ℤ)

theorem posPart_sub_negPart (a : Fin r → ℤ) : posPart a - negPart a = a := by
  funext i; simp only [posPart, negPart, Pi.sub_apply]; exact Int.toNat_sub_toNat_neg _

/-- A signed negacyclic product is four nonnegative ones. -/
theorem negacyclicMulZ_posneg (a b : Fin r → ℤ) :
    negacyclicMulZ a b =
      negacyclicMulZ (posPart a) (posPart b) - negacyclicMulZ (posPart a) (negPart b)
        - negacyclicMulZ (negPart a) (posPart b) + negacyclicMulZ (negPart a) (negPart b) := by
  conv_lhs => rw [← posPart_sub_negPart a, ← posPart_sub_negPart b]
  rw [negacyclicMulZ_sub_left, negacyclicMulZ_sub_right, negacyclicMulZ_sub_right]
  abel

end Negacyclic

/-! ### Digit extraction from a packed value -/

theorem evalBase_div_mod {B : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, d < B) :
    evalBase B L % B = L.getD 0 0 := by
  cases L with
  | nil => simp [evalBase]
  | cons d ds =>
    have hd := hL d (by simp)
    simp only [evalBase, List.getD_cons_zero]
    rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd]

theorem evalBase_div_base {B : ℕ} {L : List ℕ} (hL : ∀ d ∈ L, d < B) (hB : 2 ≤ B) :
    evalBase B L / B = evalBase B L.tail := by
  cases L with
  | nil => simp [evalBase]
  | cons d ds =>
    have hd := hL d (by simp)
    simp only [evalBase, List.tail_cons]
    rw [Nat.add_mul_div_left _ _ (by omega), Nat.div_eq_of_lt hd, zero_add]

theorem evalBase_div_pow_mod {B : ℕ} (hB : 2 ≤ B) :
    ∀ (k : ℕ) (L : List ℕ), (∀ d ∈ L, d < B) → evalBase B L / B ^ k % B = L.getD k 0
  | 0, L, hL => by simpa using evalBase_div_mod hL
  | k + 1, L, hL => by
    rw [pow_succ', ← Nat.div_div_eq_div_mul, evalBase_div_base hL hB]
    have := evalBase_div_pow_mod hB k L.tail (fun d hd => hL d (List.mem_of_mem_tail hd))
    rw [this]
    cases L <;> simp

/-! ### Kronecker substitution for nonnegative vectors -/

section Kronecker

variable {r M : ℕ} (a b : Fin r → ℕ)

/-- The base of the Kronecker packing: strictly above every product coefficient. -/
def kroneckerBase (r M : ℕ) : ℕ := r * M ^ 2 + 1

/-- The packed value of a vector. -/
def packed (B : ℕ) (a : Fin r → ℕ) : ℕ := evalBase B (List.ofFn a)

/-- Coefficient `m` of the acyclic product of natural vectors. -/
def aconvN (a b : Fin r → ℕ) (m : ℕ) : ℕ :=
  ∑ i : Fin r, ∑ j : Fin r, if i.val + j.val = m then a i * b j else 0

theorem aconvZ_natCast (m : ℕ) :
    aconvZ (fun i => (a i : ℤ)) (fun i => (b i : ℤ)) m = (aconvN a b m : ℤ) := by
  simp only [aconvZ, aconvN]; push_cast
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  split_ifs <;> simp

theorem getD_ofFn (i : ℕ) :
    (List.ofFn a).getD i 0 = if h : i < r then a ⟨i, h⟩ else 0 := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  split_ifs <;> rfl

theorem mem_ofFn_lt (ha : ∀ i, a i < M) : ∀ x ∈ List.ofFn a, x < M := by
  intro x hx
  obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
  exact ha i

/-- The truncated-subtraction-safe summand of `aconv_getD`. -/
theorem aconvN_inner (m : ℕ) (i : Fin r) :
    (∑ j : Fin r, if i.val + j.val = m then a i * b j else 0) =
      if i.val ≤ m then a i * (List.ofFn b).getD (m - i.val) 0 else 0 := by
  by_cases him : i.val ≤ m
  · simp only [him, ↓reduceIte, getD_ofFn]
    by_cases hlt : m - i.val < r
    · simp only [hlt, ↓reduceDIte]
      rw [Finset.sum_eq_single ⟨m - i.val, hlt⟩]
      · have hc : i.val + (⟨m - i.val, hlt⟩ : Fin r).val = m := by simp; omega
        simp only [hc, ↓reduceIte]
      · intro j _ hj
        have hc : ¬ (i.val + j.val = m) := fun hij => hj (Fin.ext (by simp; omega))
        simp only [hc, ↓reduceIte]
      · intro h; exact absurd (Finset.mem_univ _) h
    · simp only [hlt, ↓reduceDIte, mul_zero]
      exact Finset.sum_eq_zero fun j _ => by
        have hc : ¬ (i.val + j.val = m) := by have := j.isLt; omega
        simp only [hc, ↓reduceIte]
  · simp only [him, ↓reduceIte]
    exact Finset.sum_eq_zero fun j _ => by
      have hc : ¬ (i.val + j.val = m) := by omega
      simp only [hc, ↓reduceIte]

theorem aconvN_eq_getD (m : ℕ) : aconvN a b m = (aconv (List.ofFn a) (List.ofFn b)).getD m 0 := by
  rw [aconv_getD]
  simp only [aconvN, aconvN_inner]
  -- both sides are sums of `h` over ranges; `h` vanishes outside `range r ∩ range (m+1)`
  set h : ℕ → ℕ := fun i =>
    if i ≤ m then (if hi : i < r then a ⟨i, hi⟩ else 0) * (List.ofFn b).getD (m - i) 0 else 0
    with hh
  have h1 : (∑ i : Fin r, if i.val ≤ m then a i * (List.ofFn b).getD (m - i.val) 0 else 0)
      = ∑ i ∈ Finset.range r, h i := by
    rw [← Fin.sum_univ_eq_sum_range]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [hh, i.isLt, dite_true]
  have h2 : (∑ i ∈ Finset.range (m + 1), (List.ofFn a).getD i 0 * (List.ofFn b).getD (m - i) 0)
      = ∑ i ∈ Finset.range (m + 1), h i := by
    refine Finset.sum_congr rfl fun i hi => ?_
    rw [Finset.mem_range] at hi
    have hi' : i ≤ m := by omega
    simp only [hh, hi', ↓reduceIte, getD_ofFn]
  rw [h1, h2]
  have hzero : ∀ i, i ∉ Finset.range r → h i = 0 := by
    intro i hi; rw [Finset.mem_range] at hi
    simp only [hh, hi, ↓reduceDIte, zero_mul, ite_self]
  have hzero' : ∀ i, i ∉ Finset.range (m + 1) → h i = 0 := by
    intro i hi; rw [Finset.mem_range] at hi
    have hi' : ¬ i ≤ m := by omega
    simp only [hh, hi', ↓reduceIte]
  rw [Finset.sum_subset (Finset.range_mono (Nat.le_max_left r (m + 1)))
      (fun i _ hi => hzero i hi),
    Finset.sum_subset (Finset.range_mono (Nat.le_max_right r (m + 1)))
      (fun i _ hi => hzero' i hi)]

theorem two_le_kroneckerBase (hr : 0 < r) (hM : 0 < M) : 2 ≤ kroneckerBase r M := by
  unfold kroneckerBase; nlinarith

theorem aconv_lt_kroneckerBase (ha : ∀ i, a i < M) (hb : ∀ i, b i < M) :
    ∀ c ∈ aconv (List.ofFn a) (List.ofFn b), c < kroneckerBase r M := by
  intro c hc
  have := aconv_coeff_le (mem_ofFn_lt a ha) (mem_ofFn_lt b hb) c hc
  rw [List.length_ofFn] at this
  unfold kroneckerBase; omega

/-- The product coefficients are exactly the base-`B` digits of the product of the packed
values: ONE integer multiplication yields every coefficient. -/
theorem product_digit (ha : ∀ i, a i < M) (hb : ∀ i, b i < M) (hr : 0 < r) (hM : 0 < M)
    (k : ℕ) :
    packed (kroneckerBase r M) a * packed (kroneckerBase r M) b / kroneckerBase r M ^ k
        % kroneckerBase r M = aconvN a b k := by
  rw [aconvN_eq_getD, packed, packed, ← evalBase_aconv]
  exact evalBase_div_pow_mod (two_le_kroneckerBase hr hM) k _ (aconv_lt_kroneckerBase a b ha hb)

/-- The negacyclic product of nonnegative vectors from one Kronecker product and the fold. -/
theorem negacyclicMulZ_nat_eq (ha : ∀ i, a i < M) (hb : ∀ i, b i < M) (hr : 0 < r)
    (hM : 0 < M) (k : Fin r) :
    negacyclicMulZ (fun i => (a i : ℤ)) (fun i => (b i : ℤ)) k =
      ((packed (kroneckerBase r M) a * packed (kroneckerBase r M) b
          / kroneckerBase r M ^ k.val % kroneckerBase r M : ℕ) : ℤ)
      - ((packed (kroneckerBase r M) a * packed (kroneckerBase r M) b
          / kroneckerBase r M ^ (k.val + r) % kroneckerBase r M : ℕ) : ℤ) := by
  rw [negacyclicMulZ_eq_fold, aconvZ_natCast, aconvZ_natCast,
    product_digit a b ha hb hr hM, product_digit a b ha hb hr hM]

/-! ### Sizes -/

theorem packed_lt (ha : ∀ i, a i < M) (hr : 0 < r) (hM : 0 < M) :
    packed (kroneckerBase r M) a < kroneckerBase r M ^ r := by
  have hMB : M ≤ kroneckerBase r M := by unfold kroneckerBase; nlinarith
  have := evalBase_lt (B := kroneckerBase r M) (ds := List.ofFn a)
    (fun x hx => lt_of_lt_of_le (mem_ofFn_lt a ha x hx) hMB)
  rwa [List.length_ofFn] at this

/-- The two packed values multiply to fewer than `2 r log₂ B` bits. -/
theorem product_lt (ha : ∀ i, a i < M) (hb : ∀ i, b i < M) (hr : 0 < r) (hM : 0 < M) :
    packed (kroneckerBase r M) a * packed (kroneckerBase r M) b < kroneckerBase r M ^ (2 * r) := by
  rw [two_mul, pow_add]
  exact Nat.mul_lt_mul_of_lt_of_lt (packed_lt a ha hr hM) (packed_lt b hb hr hM)

/-- With `M = 2^(p+1)` and `r < 2^(p-2)`, the base fits in `3p` bits, so the packed values
have at most `3rp` bits: the paper's `M(3rp)`. -/
theorem kroneckerBase_le {p : ℕ} (hr : r < 2 ^ (p - 2)) (hp : 2 ≤ p) :
    kroneckerBase r (2 ^ (p + 1)) ≤ 2 ^ (3 * p) := by
  unfold kroneckerBase
  have h1 : r * (2 ^ (p + 1)) ^ 2 + 1 ≤ (2 ^ (p - 2) - 1) * 2 ^ (2 * p + 2) + 1 := by
    have : (2 ^ (p + 1)) ^ 2 = 2 ^ (2 * p + 2) := by rw [← pow_mul]; ring_nf
    rw [this]
    exact Nat.add_le_add_right (Nat.mul_le_mul_right _ (by omega)) 1
  have h2 : (2 ^ (p - 2) - 1) * 2 ^ (2 * p + 2) + 1 ≤ 2 ^ (3 * p) := by
    have hpos : 1 ≤ 2 ^ (p - 2) := Nat.one_le_two_pow
    have h3 : 2 ^ (p - 2) * 2 ^ (2 * p + 2) = 2 ^ (3 * p) := by
      rw [← pow_add]; congr 1; omega
    have h4 : 1 ≤ 2 ^ (2 * p + 2) := Nat.one_le_two_pow
    calc (2 ^ (p - 2) - 1) * 2 ^ (2 * p + 2) + 1
        = 2 ^ (p - 2) * 2 ^ (2 * p + 2) - 2 ^ (2 * p + 2) + 1 := by
          rw [Nat.sub_mul, one_mul]
      _ ≤ 2 ^ (p - 2) * 2 ^ (2 * p + 2) := by
          have : 2 ^ (2 * p + 2) ≤ 2 ^ (p - 2) * 2 ^ (2 * p + 2) :=
            Nat.le_mul_of_pos_left _ hpos
          omega
      _ = 2 ^ (3 * p) := h3
  exact h1.trans h2

end Kronecker

end IntegerMultBounds.NLogN
