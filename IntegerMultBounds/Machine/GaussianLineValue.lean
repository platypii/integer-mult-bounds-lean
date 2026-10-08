import IntegerMultBounds.Machine.GaussianLine
import IntegerMultBounds.Machine.FixedMulValue

/-! The accumulators of the Gaussian line hold the exact sums of the
truncated products: when every weight and input word has magnitude at most
`2^p`, the words are at least `p + 2` wide and the accumulators are wide
enough for `2m + 1` such terms, the signed value of the real accumulator
after `i` terms is the sum of the `i` truncated products `(w·a).tdiv 2^p`,
and likewise for the imaginary one. -/

namespace IntegerMultBounds.Machine.GaussianLine

open TwosComplement (signed addMod signed_addMod)
open FixedMul (result signed_result)

section Terms

theorem abs_tdiv_pow_le (x y : ℤ) (p : ℕ) (hx : |x| ≤ 2 ^ p) (hy : |y| ≤ 2 ^ p) :
    |(x * y).tdiv (2 ^ p)| ≤ 2 ^ p := by
  have hxy : |x * y| ≤ 2 ^ p * 2 ^ p := by
    rw [abs_mul]; exact mul_le_mul hx hy (abs_nonneg _) (by positivity)
  rw [Int.abs_eq_natAbs, Int.natAbs_tdiv]
  have hpow : ((2 : ℤ) ^ p).natAbs = 2 ^ p := by simp
  rw [hpow]
  have h1 : (x * y).natAbs ≤ 2 ^ p * 2 ^ p := by
    have : ((x * y).natAbs : ℤ) ≤ 2 ^ p * 2 ^ p := by rw [← Int.abs_eq_natAbs]; exact hxy
    exact_mod_cast this
  have h2 : (x * y).natAbs / 2 ^ p ≤ 2 ^ p := Nat.div_le_of_le_mul h1
  exact_mod_cast h2

end Terms

section Accumulators

variable (wtWords uWords : List (List Bool)) (s t m p w W : ℕ)
  (hw : p + 2 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
  (hwt : ∀ x ∈ wtWords, x.length = w) (hu : ∀ x ∈ uWords, x.length = w)
  (hwb : ∀ x ∈ wtWords, |signed x| ≤ 2 ^ p) (hub : ∀ x ∈ uWords, |signed x| ≤ 2 ^ p)
  (hwtl : wtWords.length = t * (2 * m + 1)) (hul : 2 * (s + 2 * m + 1) ≤ uWords.length)
  (hst : s < t) (hs : 0 < s)

/-- The real-part term of window `k`, index `j`. -/
def termR (k j : ℕ) : ℤ :=
  (signed (wtWords.getD (k * (2 * m + 1) + j) []) *
    signed (uWords.getD (2 * centre s t k + 2 * j) [])).tdiv (2 ^ p)

/-- The imaginary-part term of window `k`, index `j`. -/
def termI (k j : ℕ) : ℤ :=
  (signed (wtWords.getD (k * (2 * m + 1) + j) []) *
    signed (uWords.getD (2 * centre s t k + 2 * j + 1) [])).tdiv (2 ^ p)

include hwtl hst hs hul in
theorem index_bounds (k j : ℕ) (hk : k < t) (hj : j < 2 * m + 1) :
    k * (2 * m + 1) + j < wtWords.length ∧ 2 * centre s t k + 2 * j + 1 < uWords.length := by
  have hcen : centre s t k < s := by
    unfold centre; exact Nat.div_lt_of_lt_mul (by nlinarith)
  constructor
  · rw [hwtl]; nlinarith
  · omega

theorem getD_mem (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) : ws.getD i [] ∈ ws := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

include hw hwb hub hwtl hul hst hs in
theorem termR_bound (k j : ℕ) (hk : k < t) (hj : j < 2 * m + 1) :
    |termR wtWords uWords s t m p k j| ≤ 2 ^ p := by
  obtain ⟨h1, h2⟩ := index_bounds wtWords uWords s t m hwtl hul hst hs k j hk hj
  exact abs_tdiv_pow_le _ _ p (hwb _ (getD_mem _ _ h1))
    (hub _ (getD_mem uWords (2 * centre s t k + 2 * j) (by omega)))

include hw hwb hub hwtl hul hst hs in
theorem termI_bound (k j : ℕ) (hk : k < t) (hj : j < 2 * m + 1) :
    |termI wtWords uWords s t m p k j| ≤ 2 ^ p := by
  obtain ⟨h1, h2⟩ := index_bounds wtWords uWords s t m hwtl hul hst hs k j hk hj
  exact abs_tdiv_pow_le _ _ p (hwb _ (getD_mem _ _ h1)) (hub _ (getD_mem _ _ h2))

theorem signed_zero_word (W : ℕ) : signed (List.replicate W false) = 0 := by
  have hl : ∀ n, (List.replicate n false).getLastD false = false := by
    intro n
    induction n with
    | zero => rfl
    | succ n ih => rw [List.replicate_succ, List.getLastD_cons]; exact ih
  unfold signed
  rw [hl, TwosComplement.value_replicate_false]
  simp

theorem abs_sum_le (f : ℕ → ℤ) (n : ℕ) (B : ℤ) (h : ∀ j < n, |f j| ≤ B) :
    |∑ j ∈ Finset.range n, f j| ≤ n * B := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    calc |∑ j ∈ Finset.range n, f j + f n| ≤ |∑ j ∈ Finset.range n, f j| + |f n| := abs_add_le _ _
      _ ≤ n * B + B := add_le_add (ih fun j hj => h j (by omega)) (h n (by omega))
      _ = ((n + 1 : ℕ) : ℤ) * B := by push_cast; ring

include hw hwW hW hwt hu hwb hub hwtl hul hst hs in
/-- The real accumulator holds the exact partial sum. -/
theorem accR_signed (k : ℕ) (hk : k < t) (i : ℕ) (hi : i ≤ 2 * m + 1) :
    signed (accR wtWords uWords s t m p w W k i) = ∑ j ∈ Finset.range i, termR wtWords uWords s t m p k j := by
  induction i with
  | zero =>
    simp only [accR, Finset.range_zero, Finset.sum_empty]
    exact signed_zero_word W
  | succ i ih =>
    have hi' : i ≤ 2 * m + 1 := by omega
    obtain ⟨h1, h2⟩ := index_bounds wtWords uWords s t m hwtl hul hst hs k i hk (by omega)
    have hwl := getD_length wtWords w hwt _ h1
    have hul' := getD_length uWords w hu _ (by omega : 2 * centre s t k + 2 * i < uWords.length)
    have hres := signed_result (wtWords.getD (k * (2 * m + 1) + i) []) (uWords.getD (2 * centre s t k + 2 * i) [])
      p w hwl hul' hw (hwb _ (getD_mem _ _ h1)) (hub _ (getD_mem uWords (2 * centre s t k + 2 * i) (by omega)))
    have hacc := ih hi'
    have hsum : |∑ j ∈ Finset.range i, termR wtWords uWords s t m p k j| ≤ (i : ℤ) * 2 ^ p :=
      abs_sum_le _ _ _ fun j hj => termR_bound wtWords uWords s t m p w hw hwb hub hwtl hul hst hs k j hk (by omega)
    have hterm := termR_bound wtWords uWords s t m p w hw hwb hub hwtl hul hst hs k i hk (by omega)
    have hfit : (i : ℤ) * 2 ^ p + 2 ^ p ≤ ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p := by
      have : ((i : ℤ) + 1) ≤ ((2 * m + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : i + 1 ≤ 2 * m + 1)
      nlinarith [(by positivity : (0 : ℤ) < 2 ^ p)]
    have hlen : (accR wtWords uWords s t m p w W k i).length = W := accR_length _ _ _ _ _ _ _ _ _ hwW i
    have hne : accR wtWords uWords s t m p w W k i ≠ [] := by
      intro h0; rw [h0] at hlen; simp at hlen; omega
    rw [accR, signed_addMod _ _ (by rw [result_length, hlen]; exact hwW) hne (by
        rw [hlen, hres, hacc]
        have := abs_le.mp hsum; have := abs_le.mp hterm
        unfold termR at *; linarith)
      (by
        rw [hlen, hres, hacc]
        have := abs_le.mp hsum; have := abs_le.mp hterm
        unfold termR at *; linarith),
      hres, hacc, Finset.sum_range_succ]
    unfold termR; ring

include hw hwW hW hwt hu hwb hub hwtl hul hst hs in
/-- The imaginary accumulator holds the exact partial sum. -/
theorem accI_signed (k : ℕ) (hk : k < t) (i : ℕ) (hi : i ≤ 2 * m + 1) :
    signed (accI wtWords uWords s t m p w W k i) = ∑ j ∈ Finset.range i, termI wtWords uWords s t m p k j := by
  induction i with
  | zero =>
    simp only [accI, Finset.range_zero, Finset.sum_empty]
    exact signed_zero_word W
  | succ i ih =>
    have hi' : i ≤ 2 * m + 1 := by omega
    obtain ⟨h1, h2⟩ := index_bounds wtWords uWords s t m hwtl hul hst hs k i hk (by omega)
    have hwl := getD_length wtWords w hwt _ h1
    have hul' := getD_length uWords w hu _ h2
    have hres := signed_result (wtWords.getD (k * (2 * m + 1) + i) []) (uWords.getD (2 * centre s t k + 2 * i + 1) [])
      p w hwl hul' hw (hwb _ (getD_mem _ _ h1)) (hub _ (getD_mem _ _ h2))
    have hacc := ih hi'
    have hsum : |∑ j ∈ Finset.range i, termI wtWords uWords s t m p k j| ≤ (i : ℤ) * 2 ^ p :=
      abs_sum_le _ _ _ fun j hj => termI_bound wtWords uWords s t m p w hw hwb hub hwtl hul hst hs k j hk (by omega)
    have hterm := termI_bound wtWords uWords s t m p w hw hwb hub hwtl hul hst hs k i hk (by omega)
    have hfit : (i : ℤ) * 2 ^ p + 2 ^ p ≤ ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p := by
      have : ((i : ℤ) + 1) ≤ ((2 * m + 1 : ℕ) : ℤ) := by exact_mod_cast (by omega : i + 1 ≤ 2 * m + 1)
      nlinarith [(by positivity : (0 : ℤ) < 2 ^ p)]
    have hlen : (accI wtWords uWords s t m p w W k i).length = W := accI_length _ _ _ _ _ _ _ _ _ hwW i
    have hne : accI wtWords uWords s t m p w W k i ≠ [] := by
      intro h0; rw [h0] at hlen; simp at hlen; omega
    rw [accI, signed_addMod _ _ (by rw [result_length, hlen]; exact hwW) hne (by
        rw [hlen, hres, hacc]
        have := abs_le.mp hsum; have := abs_le.mp hterm
        unfold termI at *; linarith)
      (by
        rw [hlen, hres, hacc]
        have := abs_le.mp hsum; have := abs_le.mp hterm
        unfold termI at *; linarith),
      hres, hacc, Finset.sum_range_succ]
    unfold termI; ring

end Accumulators

end IntegerMultBounds.Machine.GaussianLine
