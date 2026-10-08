import Mathlib.Tactic
import IntegerMultBounds.NLogN.Kronecker

/-! Carry propagation: an unnormalised digit vector, such as the output of a
convolution, is rewritten as proper base-`B` digits, truncated to a fixed
width, and expanded into a most-significant-first bit string. Proved: the
normalisation preserves the value, produces digits below `B`, the fixed-width
form has exactly `L` digits and the same value whenever that value fits, and
the resulting `k * L` bits have the machine's `binaryValue` equal to the
digit vector's value. This is list-level arithmetic; no tape program or cost
bound is part of this file. -/

namespace IntegerMultBounds.NLogN

/-! ### Normalisation -/

/-- Propagate carries through a digit list; the final carry becomes trailing
base-`B` digits. -/
def normalize (B : ℕ) : List ℕ → ℕ → List ℕ
  | [], c => Nat.digits B c
  | d :: ds, c => ((d + c) % B) :: normalize B ds ((d + c) / B)

theorem evalBase_eq_ofDigits (B : ℕ) (ds : List ℕ) :
    evalBase B ds = Nat.ofDigits B ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih => simp [evalBase, Nat.ofDigits_cons, ih]

theorem evalBase_normalize (B : ℕ) (ds : List ℕ) (c : ℕ) :
    evalBase B (normalize B ds c) = evalBase B ds + c := by
  induction ds generalizing c with
  | nil => simp [normalize, evalBase, evalBase_eq_ofDigits, Nat.ofDigits_digits]
  | cons d ds ih =>
    simp only [normalize, evalBase, ih]
    have := Nat.mod_add_div (d + c) B
    nlinarith

theorem normalize_digits_lt {B : ℕ} (hB : 2 ≤ B) (ds : List ℕ) (c : ℕ) :
    ∀ x ∈ normalize B ds c, x < B := by
  induction ds generalizing c with
  | nil =>
    intro x hx
    exact Nat.digits_lt_base hB hx
  | cons d ds ih =>
    intro x hx
    simp only [normalize, List.mem_cons] at hx
    rcases hx with rfl | hx
    · exact Nat.mod_lt _ (by omega)
    · exact ih _ x hx

/-! ### Fixed width -/

/-- A digit list with value below `B ^ L` is zero beyond index `L`. -/
theorem evalBase_take_of_lt {B : ℕ} {ds : List ℕ} {L : ℕ} (hB : 2 ≤ B)
    (h : evalBase B ds < B ^ L) :
    evalBase B (ds.take L) = evalBase B ds := by
  by_cases hL : L ≤ ds.length
  · have hsplit := List.take_append_drop L ds
    have hlen : (ds.take L).length = L := by
      rw [List.length_take]; omega
    have hdrop : evalBase B (ds.drop L) = 0 := by
      by_contra hne
      have hpos : 1 ≤ evalBase B (ds.drop L) := Nat.one_le_iff_ne_zero.mpr hne
      have := evalBase_append B (ds.take L) (ds.drop L)
      rw [hsplit, hlen] at this
      have hBL : 0 < B ^ L := by positivity
      nlinarith
    conv_rhs => rw [← hsplit]
    rw [evalBase_append, hdrop]; ring
  · rw [List.take_of_length_le (by omega)]

/-- Exactly `L` proper base-`B` digits. -/
def fixWidth (B L : ℕ) (ds : List ℕ) : List ℕ :=
  (normalize B ds 0 ++ List.replicate L 0).take L

theorem fixWidth_length (B L : ℕ) (ds : List ℕ) : (fixWidth B L ds).length = L := by
  simp only [fixWidth, List.length_take, List.length_append, List.length_replicate]
  omega

theorem fixWidth_digits_lt {B : ℕ} (hB : 2 ≤ B) (L : ℕ) (ds : List ℕ) :
    ∀ x ∈ fixWidth B L ds, x < B := by
  intro x hx
  have hx' := List.mem_of_mem_take hx
  rcases List.mem_append.mp hx' with h | h
  · exact normalize_digits_lt hB ds 0 x h
  · rw [List.eq_of_mem_replicate h]; omega

theorem evalBase_fixWidth {B L : ℕ} (hB : 2 ≤ B) {ds : List ℕ}
    (h : evalBase B ds < B ^ L) : evalBase B (fixWidth B L ds) = evalBase B ds := by
  unfold fixWidth
  have hval : evalBase B (normalize B ds 0 ++ List.replicate L 0) = evalBase B ds := by
    rw [evalBase_append_replicate, evalBase_normalize]; ring
  rw [evalBase_take_of_lt hB (hval ▸ h), hval]

/-! ### Bits -/

/-- Exactly `k` bits of `d`, least significant first. -/
def bitsOfDigit : ℕ → ℕ → List Bool
  | 0, _ => []
  | k + 1, d => (d % 2 = 1) :: bitsOfDigit k (d / 2)

@[simp] theorem bitsOfDigit_length (k d : ℕ) : (bitsOfDigit k d).length = k := by
  induction k generalizing d with
  | zero => rfl
  | succ k ih => simp [bitsOfDigit, ih]

/-- The machine's bit-to-digit map. -/
def bitDigit (b : Bool) : ℕ := if b then 1 else 0

theorem evalBase_bitsOfDigit {k d : ℕ} (h : d < 2 ^ k) :
    evalBase 2 ((bitsOfDigit k d).map bitDigit) = d := by
  induction k generalizing d with
  | zero => simp [bitsOfDigit, evalBase] at *; omega
  | succ k ih =>
    have hd : d / 2 < 2 ^ k := by
      rw [pow_succ] at h; omega
    simp only [bitsOfDigit, List.map_cons, evalBase, ih hd]
    have := Nat.mod_add_div d 2
    have hmod : d % 2 < 2 := Nat.mod_lt _ (by omega)
    by_cases h1 : d % 2 = 1
    · simp [bitDigit, h1]; omega
    · simp [bitDigit, h1]; omega

theorem evalBase_flatMap_bits {k : ℕ} {ds : List ℕ} (hd : ∀ d ∈ ds, d < 2 ^ k) :
    evalBase 2 ((ds.flatMap (bitsOfDigit k)).map bitDigit) = evalBase (2 ^ k) ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    rw [List.flatMap_cons, List.map_append, evalBase_append, List.length_map,
      bitsOfDigit_length, evalBase_bitsOfDigit (hd d (by simp)),
      ih (fun x hx => hd x (List.mem_cons_of_mem d hx))]
    rfl

/-- Most-significant bit first, `k * L` bits. -/
def toBits (k L : ℕ) (ds : List ℕ) : List Bool :=
  ((fixWidth (2 ^ k) L ds).flatMap (bitsOfDigit k)).reverse

theorem toBits_length (k L : ℕ) (ds : List ℕ) : (toBits k L ds).length = k * L := by
  simp only [toBits, List.length_reverse, List.length_flatMap, bitsOfDigit_length]
  rw [List.map_const', List.sum_replicate, fixWidth_length, smul_eq_mul, mul_comm]

theorem binaryValue_toBits {k L : ℕ} (hk : 0 < k) {ds : List ℕ}
    (h : evalBase (2 ^ k) ds < (2 ^ k) ^ L) :
    Machine.binaryValue (toBits k L ds) = evalBase (2 ^ k) ds ∧
      (toBits k L ds).length = k * L := by
  refine ⟨?_, toBits_length k L ds⟩
  have hB : 2 ≤ 2 ^ k := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) hk
  rw [binaryValue_eq_evalBase, toBits, List.reverse_reverse]
  have hmap : (fun b : Bool => if b then 1 else 0) = bitDigit := rfl
  rw [hmap, evalBase_flatMap_bits (fixWidth_digits_lt hB L ds), evalBase_fixWidth hB h]

end IntegerMultBounds.NLogN
