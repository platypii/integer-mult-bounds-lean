import IntegerMultBounds.NLogN.DFT
import IntegerMultBounds.NLogN.Multiplier

/-! Steps (1) and (3) of the recursive step of Harvey–van der Hoeven
(Proposition 5.4). Two `n`-bit integers cut into `k`-bit digits multiply as a
cyclic convolution of any length `S` with at least as many positions as the
acyclic product; the convolution digits are below `2 ^ (3 k)` once the digit
count is below `2 ^ k`. The same convolution appears as a `ZMod S`-indexed
complex vector, and the paper's normalised convolution `(u ∗ v) / S` of the
`2 ^ (-k)`-scaled digit vectors, rescaled by `2 ^ (2 k) S`, is the exact
integer convolution. Proved: any approximation of the normalised convolution
within `δ` in each entry, with `2 ^ (2 k) S δ < 1 / 2`, rounds to the exact
digits, also in the paper's `2 ^ p`-scaled error form, and those rounded
digits evaluate to the product of the inputs. Computing the approximation,
the middle step (2) of the proposition, and tape costs are not covered. -/

namespace IntegerMultBounds.NLogN

open Complex

/-! ### Step (1): chunks and the length of the convolution -/

/-- The digit count of an `n`-bit string is at most `⌈n / k⌉`. -/
theorem digitsOf_length_le_div {k : ℕ} (hk : 0 < k) (x : List Bool) :
    (digitsOf k x).length ≤ (x.length + k - 1) / k := by
  obtain ⟨k', rfl⟩ := Nat.exists_eq_succ_of_ne_zero hk.ne'
  simp only [digitsOf, List.length_map]
  have := chunks_length_le k' (x.reverse.map bitDigit)
  rw [show x.length + (k' + 1) - 1 = x.length + k' by omega]
  simpa using this

/-- Acyclic convolution digits are below `2 ^ (3 k)` when there are fewer
than `2 ^ k` digits. -/
theorem aconv_digits_lt {k : ℕ} (hk : 0 < k) {x y : List Bool}
    (hN : (digitsOf k x).length < 2 ^ k) :
    ∀ c ∈ aconv (digitsOf k x) (digitsOf k y), c < 2 ^ (3 * k) := by
  intro c hc
  have h := aconv_coeff_le (digitsOf_lt hk x) (digitsOf_lt hk y) c hc
  calc c ≤ (digitsOf k x).length * (2 ^ k) ^ 2 := h
    _ < 2 ^ k * (2 ^ k) ^ 2 := Nat.mul_lt_mul_of_pos_right hN (by positivity)
    _ = 2 ^ (3 * k) := by ring

/-- The length-`S` cyclic convolution of the digits evaluates to the product. -/
theorem reduce_to_cconv {k S : ℕ} (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ S + 1) :
    evalBase (2 ^ k) (cconvList S (digitsOf k x) (digitsOf k y)) =
      Machine.binaryValue x * Machine.binaryValue y := by
  rw [evalBase_cconvList _ hS, evalBase_digitsOf hk, evalBase_digitsOf hk]

/-! ### The `ZMod S` vector form -/

/-- The zero-padded complex vector of a digit list, indexed by `ZMod S`. -/
noncomputable def vecZ (S : ℕ) [NeZero S] (ds : List ℕ) : ZMod S → ℂ :=
  fun i => (ds.getD i.val 0 : ℂ)

/-- The `ZMod S` convolution of digit vectors is the list-level one. -/
theorem cconv_vecZ_eq {S : ℕ} [NeZero S] (a b : List ℕ) (k : ZMod S) :
    cconv (vecZ S a) (vecZ S b) k = ((cconvList S a b).getD k.val 0 : ℂ) := by
  obtain ⟨m, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (NeZero.ne S)
  exact cconvFin_eq_cconvList a b k

/-! ### Step (3): scaling and rounding recovery -/

/-- The paper's normalised convolution `(u ∗ v) / S` of the `2 ^ (-k)`-scaled
digit vectors. -/
noncomputable def scaledConv (S k : ℕ) [NeZero S] (dx dy : List ℕ) : ZMod S → ℂ :=
  fun i => cconv (fun j => vecZ S dx j / 2 ^ k) (fun j => vecZ S dy j / 2 ^ k) i / S

/-- Rescaling the normalised convolution by `2 ^ (2 k) S` gives the exact
integer convolution. -/
theorem scaledConv_eq {S k : ℕ} [NeZero S] (dx dy : List ℕ) (i : ZMod S) :
    ((2 : ℂ) ^ (2 * k) * S) * scaledConv S k dx dy i =
      ((cconvList S dx dy).getD i.val 0 : ℂ) := by
  rw [← cconv_vecZ_eq]
  have hS : (S : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (NeZero.ne S)
  have h2 : (2 : ℂ) ^ k ≠ 0 := pow_ne_zero _ two_ne_zero
  have hterm : ∀ j, vecZ S dx j / 2 ^ k * (vecZ S dy (i - j) / 2 ^ k) =
      vecZ S dx j * vecZ S dy (i - j) / 2 ^ (2 * k) := by
    intro j
    rw [two_mul, pow_add]
    field_simp
  simp only [scaledConv, cconv, hterm, ← Finset.sum_div]
  field_simp

/-- An approximation of the normalised convolution within `δ`, with
`2 ^ (2 k) S δ < 1 / 2`, rounds to the exact convolution digits. -/
theorem recover_cconv {S k : ℕ} [NeZero S] (dx dy : List ℕ) {w' : ZMod S → ℂ} {δ : ℝ}
    (hw : ∀ i, ‖w' i - scaledConv S k dx dy i‖ ≤ δ)
    (hδ : (2 : ℝ) ^ (2 * k) * S * δ < 1 / 2) :
    (fun i => round (((2 : ℂ) ^ (2 * k) * S) * w' i).re) =
      fun i => (((cconvList S dx dy).getD i.val 0 : ℕ) : ℤ) := by
  funext i
  apply round_exact
  rw [Int.cast_natCast, ← scaledConv_eq dx dy i, ← mul_sub, norm_mul]
  have hc : ‖(2 : ℂ) ^ (2 * k) * S‖ = (2 : ℝ) ^ (2 * k) * S := by
    rw [norm_mul, norm_pow, norm_natCast, Complex.norm_ofNat]
  rw [hc]
  calc (2 : ℝ) ^ (2 * k) * S * ‖w' i - scaledConv S k dx dy i‖
      ≤ (2 : ℝ) ^ (2 * k) * S * δ := by gcongr; exact hw i
    _ < 1 / 2 := hδ

/-- The same recovery in the paper's `2 ^ p`-scaled error form. -/
theorem recover_cconv_scaled {S k p : ℕ} [NeZero S] (dx dy : List ℕ)
    {w' : ZMod S → ℂ} {ε : ℝ}
    (hw : ∀ i, (2 : ℝ) ^ p * ‖w' i - scaledConv S k dx dy i‖ ≤ ε)
    (hε : (2 : ℝ) ^ (2 * k) * S * ε < 2 ^ p / 2) :
    (fun i => round (((2 : ℂ) ^ (2 * k) * S) * w' i).re) =
      fun i => (((cconvList S dx dy).getD i.val 0 : ℕ) : ℤ) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  refine recover_cconv dx dy (δ := ε / 2 ^ p) ?_ ?_
  · intro i
    rw [le_div_iff₀ hp, mul_comm]
    exact hw i
  · rw [← mul_div_assoc, div_lt_iff₀ hp]
    linarith

/-- Rounded, rescaled approximate convolution digits evaluate to the product
of the inputs. -/
theorem product_from_approx {k S : ℕ} [NeZero S] (hk : 0 < k) {x y : List Bool}
    (hS : (digitsOf k x).length + (digitsOf k y).length ≤ S + 1)
    {w' : ZMod S → ℂ} {δ : ℝ}
    (hw : ∀ i, ‖w' i - scaledConv S k (digitsOf k x) (digitsOf k y) i‖ ≤ δ)
    (hδ : (2 : ℝ) ^ (2 * k) * S * δ < 1 / 2) :
    evalBase (2 ^ k) (List.ofFn fun i : Fin S =>
      (round (((2 : ℂ) ^ (2 * k) * S) * w' (i.val : ZMod S)).re).toNat) =
      Machine.binaryValue x * Machine.binaryValue y := by
  have hr := recover_cconv (digitsOf k x) (digitsOf k y) hw hδ
  have hlist : (List.ofFn fun i : Fin S =>
      (round (((2 : ℂ) ^ (2 * k) * S) * w' (i.val : ZMod S)).re).toNat) =
      cconvList S (digitsOf k x) (digitsOf k y) := by
    apply List.ext_getElem
    · simp
    · intro i h₁ h₂
      rw [List.getElem_ofFn]
      have hi : i < S := by simpa using h₂
      have := congrFun hr (i : ZMod S)
      rw [this, Int.toNat_natCast, ← getD_eq_getElem h₂, ZMod.val_natCast,
        Nat.mod_eq_of_lt hi]
  rw [hlist, reduce_to_cconv hk hS]

end IntegerMultBounds.NLogN
