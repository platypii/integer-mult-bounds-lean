import IntegerMultBounds.Machine.BinaryAdd

/-! Two's complement words, least significant bit first: the signed value is
the unsigned value minus `2^n` when the top bit is set. Sign extension,
modular addition of an extended word into a wider accumulator, and negation
are defined on words with their value identities; the machines realizing
them are in `SignExtendAdd` and `Negate`. -/

namespace IntegerMultBounds.Machine.TwosComplement

open Counter (value)
open BinaryAdd (sumBit carryBit digits overflow carryWord bitValue)

/-! ### Unsigned value identities -/

theorem value_append (xs ys : List Bool) : value (xs ++ ys) = value xs + 2 ^ xs.length * value ys := by
  induction xs with
  | nil => simp [value]
  | cons b bs ih => simp [value, ih, pow_succ]; ring

theorem value_replicate_false (n : ℕ) : value (List.replicate n false) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, ih]

theorem value_replicate_true (n : ℕ) : value (List.replicate n true) + 1 = 2 ^ n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [List.replicate_succ, value, pow_succ]; omega

theorem value_map_not (bs : List Bool) : value (bs.map not) + value bs + 1 = 2 ^ bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [value, pow_succ] <;> omega

/-- The value splits at the top bit. -/
theorem value_dropLast (bs : List Bool) (h : bs ≠ []) :
    value bs = value bs.dropLast + 2 ^ (bs.length - 1) * bitValue (bs.getLast h) := by
  conv_lhs => rw [← List.dropLast_append_getLast h]
  rw [value_append, List.length_dropLast]
  cases bs.getLast h <;> simp [value, bitValue]

theorem value_dropLast_lt (bs : List Bool) (_h : bs ≠ []) : value bs.dropLast < 2 ^ (bs.length - 1) := by
  have := Counter.value_lt bs.dropLast
  rwa [List.length_dropLast] at this

/-! ### Signed values -/

/-- The two's complement value. -/
def signed (bs : List Bool) : ℤ :=
  (value bs : ℤ) - if bs.getLastD false then 2 ^ bs.length else 0

theorem signed_nil : signed [] = 0 := by simp [signed, value]

theorem getLastD_eq (bs : List Bool) (h : bs ≠ []) (d : Bool) : bs.getLastD d = bs.getLast h := by
  induction bs generalizing d with
  | nil => exact absurd rfl h
  | cons b bs ih =>
    cases bs with
    | nil => rfl
    | cons c cs =>
      rw [List.getLastD_cons, List.getLast_cons (by simp)]
      exact ih (by simp) b

/-- A nonempty word's signed value lies in `[-2^(n-1), 2^(n-1))`. -/
theorem signed_bounds (bs : List Bool) (h : bs ≠ []) :
    -(2 : ℤ) ^ (bs.length - 1) ≤ signed bs ∧ signed bs < 2 ^ (bs.length - 1) := by
  have hv : (value bs : ℤ) = value bs.dropLast + 2 ^ (bs.length - 1) * bitValue (bs.getLast h) := by
    exact_mod_cast value_dropLast bs h
  have hlt : (value bs.dropLast : ℤ) < 2 ^ (bs.length - 1) := by exact_mod_cast value_dropLast_lt bs h
  have h0 : (0 : ℤ) ≤ value bs.dropLast := by positivity
  have hl : 1 ≤ bs.length := List.length_pos_of_ne_nil h
  have hpow : (2 : ℤ) ^ bs.length = 2 * 2 ^ (bs.length - 1) := by
    rw [← pow_succ']; congr 1; omega
  unfold signed
  rw [getLastD_eq bs h]
  generalize bs.getLast h = b at hv ⊢
  cases b <;> simp only [bitValue, ↓reduceIte, Bool.false_eq_true, Nat.cast_one, Nat.cast_zero,
    mul_one, mul_zero, add_zero, sub_zero] at hv ⊢ <;> constructor <;> linarith

/-- The signed value is the unsigned value modulo `2^n`. -/
theorem signed_emod (bs : List Bool) : signed bs % 2 ^ bs.length = value bs := by
  unfold signed
  split_ifs
  · rw [Int.sub_emod, Int.emod_self, sub_zero, Int.emod_emod_of_dvd _ dvd_rfl,
      Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Counter.value_lt bs)]
  · rw [sub_zero, Int.emod_eq_of_lt (by positivity) (by exact_mod_cast Counter.value_lt bs)]

/-- Two signed values of width `n` that agree modulo `2^n` are equal. -/
theorem signed_eq_of_emod {bs cs : List Bool} (hb : bs ≠ []) (hc : cs ≠ [])
    (hlen : bs.length = cs.length) (h : signed bs % 2 ^ bs.length = signed cs % 2 ^ bs.length) :
    signed bs = signed cs := by
  obtain ⟨hb1, hb2⟩ := signed_bounds bs hb
  obtain ⟨hc1, hc2⟩ := signed_bounds cs hc
  rw [← hlen] at hc1 hc2
  have hl : 1 ≤ bs.length := List.length_pos_of_ne_nil hb
  have hpow : (2 : ℤ) ^ bs.length = 2 * 2 ^ (bs.length - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hdvd : (2 : ℤ) ^ bs.length ∣ signed bs - signed cs := Int.ModEq.dvd h.symm
  have habs : |signed bs - signed cs| < 2 ^ bs.length := by
    rw [abs_lt]; constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/-- A word whose signed value is given: equality of words follows from equal
signed values and lengths. -/
theorem eq_of_signed {bs cs : List Bool} (hlen : bs.length = cs.length) (h : signed bs = signed cs) :
    value bs = value cs := by
  have h1 := signed_emod bs
  have h2 := signed_emod cs
  rw [← hlen] at h2
  rw [h] at h1
  exact_mod_cast h1.symm.trans h2

/-! ### Sign extension -/

/-- Extend to width `n` by repeating the top bit. -/
def extTo (xs : List Bool) (n : ℕ) : List Bool :=
  xs ++ List.replicate (n - xs.length) (xs.getLastD false)

theorem extTo_length (xs : List Bool) (n : ℕ) (h : xs.length ≤ n) : (extTo xs n).length = n := by
  simp [extTo]; omega

/-- The extended word has the signed value modulo `2^n`. -/
theorem extTo_value (xs : List Bool) (n : ℕ) (h : xs.length ≤ n) :
    (value (extTo xs n) : ℤ) = signed xs + if xs.getLastD false then 2 ^ n else 0 := by
  unfold extTo signed
  rw [value_append]
  cases hl : xs.getLastD false
  · simp [value_replicate_false]
  · have h1 := value_replicate_true (n - xs.length)
    have h2 : (2 : ℤ) ^ xs.length * 2 ^ (n - xs.length) = 2 ^ n := by
      rw [← pow_add]; congr 1; omega
    simp only [↓reduceIte]
    push_cast
    have : ((2 : ℕ) ^ (n - xs.length) : ℤ) = (2 : ℤ) ^ (n - xs.length) := by push_cast; rfl
    have h1' : (value (List.replicate (n - xs.length) true) : ℤ) + 1 = 2 ^ (n - xs.length) := by
      exact_mod_cast h1
    have h3 : (2 : ℤ) ^ xs.length * value (List.replicate (n - xs.length) true) =
        2 ^ n - 2 ^ xs.length := by
      rw [show (value (List.replicate (n - xs.length) true) : ℤ) = 2 ^ (n - xs.length) - 1 by linarith,
        mul_sub, h2, mul_one]
    linarith

/-! ### Modular addition -/

/-- The digits of an aligned addition carry the sum modulo `2^n`. -/
theorem digits_value (c : Bool) (xs ys : List Bool) (hlen : xs.length = ys.length) :
    value (digits c (xs.zip ys)) + 2 ^ xs.length * bitValue (overflow c (xs.zip ys)) =
      value xs + value ys + bitValue c := by
  have h := BinaryAdd.result_value c xs ys hlen
  rw [BinaryAdd.result, value_append, BinaryAdd.digits_length, List.length_zip, hlen, min_self] at h
  rw [← hlen] at h
  generalize overflow c (xs.zip ys) = ov at h ⊢
  cases ov <;> simp [carryWord, value, bitValue] at h ⊢ <;> omega

/-- Add the extended word into the accumulator, dropping the final carry. -/
def addMod (xs acc : List Bool) : List Bool := digits false ((extTo xs acc.length).zip acc)

theorem addMod_length (xs acc : List Bool) (h : xs.length ≤ acc.length) :
    (addMod xs acc).length = acc.length := by
  simp [addMod, extTo_length xs _ h]

/-- The sum modulo `2^n`. -/
theorem addMod_emod (xs acc : List Bool) (h : xs.length ≤ acc.length) :
    (value (addMod xs acc) : ℤ) % 2 ^ acc.length = (signed xs + signed acc) % 2 ^ acc.length := by
  have hd := digits_value false (extTo xs acc.length) acc (extTo_length xs _ h)
  rw [extTo_length xs _ h] at hd
  have he := extTo_value xs acc.length h
  have hs := signed_emod acc
  unfold addMod
  have hd' : (value (digits false ((extTo xs acc.length).zip acc)) : ℤ) =
      value (extTo xs acc.length) + value acc -
        2 ^ acc.length * bitValue (overflow false ((extTo xs acc.length).zip acc)) := by
    simp only [bitValue, Bool.false_eq_true, ↓reduceIte, add_zero] at hd
    have h' := congrArg (fun x : ℕ => (x : ℤ)) hd
    push_cast at h'
    simp only [bitValue]
    split_ifs at h' ⊢ <;> push_cast at h' ⊢ <;> linarith
  rw [hd', he, ← Int.emod_emod_of_dvd (signed xs + signed acc) (dvd_refl ((2 : ℤ) ^ acc.length)),
    Int.add_emod (signed xs), ← hs, ← Int.add_emod]
  cases xs.getLastD false <;> cases overflow false ((extTo xs acc.length).zip acc) <;>
    simp [bitValue, Int.sub_emod, Int.add_emod, Int.emod_self]

/-- Without overflow the accumulator holds the exact signed sum. -/
theorem signed_addMod (xs acc : List Bool) (h : xs.length ≤ acc.length) (hacc : acc ≠ [])
    (hlo : -(2 : ℤ) ^ (acc.length - 1) ≤ signed xs + signed acc)
    (hhi : signed xs + signed acc < 2 ^ (acc.length - 1)) :
    signed (addMod xs acc) = signed xs + signed acc := by
  have hne : addMod xs acc ≠ [] := by
    intro h0; have := addMod_length xs acc h; rw [h0] at this; simp at this
    exact hacc (List.length_eq_zero_iff.mp this.symm)
  obtain ⟨h1, h2⟩ := signed_bounds _ hne
  rw [addMod_length xs acc h] at h1 h2
  have hmod : signed (addMod xs acc) % 2 ^ acc.length = (signed xs + signed acc) % 2 ^ acc.length := by
    have hv : (value (addMod xs acc) : ℤ) < 2 ^ acc.length := by
      have := Counter.value_lt (addMod xs acc)
      rw [addMod_length xs acc h] at this
      exact_mod_cast this
    rw [← addMod_length xs acc h, signed_emod, addMod_length xs acc h,
      ← Int.emod_eq_of_lt (by positivity) hv]
    exact addMod_emod xs acc h
  have hl : 1 ≤ acc.length := List.length_pos_of_ne_nil hacc
  have hpow : (2 : ℤ) ^ acc.length = 2 * 2 ^ (acc.length - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hdvd : (2 : ℤ) ^ acc.length ∣ signed (addMod xs acc) - (signed xs + signed acc) :=
    Int.ModEq.dvd hmod.symm
  have habs : |signed (addMod xs acc) - (signed xs + signed acc)| < 2 ^ acc.length := by
    rw [abs_lt]; constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

/-! ### Negation -/

/-- Two's complement negation: copy up to and including the first one, then
complement. -/
def negWord : List Bool → List Bool
  | [] => []
  | false :: bs => false :: negWord bs
  | true :: bs => true :: bs.map not

theorem negWord_length (bs : List Bool) : (negWord bs).length = bs.length := by
  induction bs with
  | nil => rfl
  | cons b bs ih => cases b <;> simp [negWord, ih]

theorem negWord_value (bs : List Bool) : (value (negWord bs) + value bs) % 2 ^ bs.length = 0 := by
  induction bs with
  | nil => rfl
  | cons b bs ih =>
    cases b
    · simp only [negWord, value, Bool.false_eq_true, ↓reduceIte, zero_add, List.length_cons, pow_succ]
      rw [← mul_add, mul_comm (2 ^ bs.length) 2, Nat.mul_mod_mul_left, ih, mul_zero]
    · have := value_map_not bs
      simp only [negWord, value, ↓reduceIte, List.length_cons, pow_succ]
      rw [show 1 + 2 * value (bs.map not) + (1 + 2 * value bs) = 2 ^ bs.length * 2 by omega,
        Nat.mod_self]

/-- Negation of a value other than `-2^(n-1)` negates the signed value. -/
theorem signed_negWord (bs : List Bool) (hne : bs ≠ []) (h : signed bs ≠ -(2 : ℤ) ^ (bs.length - 1)) :
    signed (negWord bs) = -signed bs := by
  have hlen := negWord_length bs
  have hne' : negWord bs ≠ [] := by
    intro h0; rw [h0] at hlen; exact hne (List.length_eq_zero_iff.mp hlen.symm)
  obtain ⟨h1, h2⟩ := signed_bounds _ hne'
  obtain ⟨h3, h4⟩ := signed_bounds _ hne
  rw [hlen] at h1 h2
  have hv := negWord_value bs
  have hs1 := signed_emod (negWord bs)
  have hs2 := signed_emod bs
  rw [hlen] at hs1
  have hl : 1 ≤ bs.length := List.length_pos_of_ne_nil hne
  have hpow : (2 : ℤ) ^ bs.length = 2 * 2 ^ (bs.length - 1) := by
    rw [← pow_succ']; congr 1; omega
  have hv' : ((value (negWord bs) : ℤ) + value bs) % 2 ^ bs.length = 0 := by exact_mod_cast hv
  have hdvd : (2 : ℤ) ^ bs.length ∣ signed (negWord bs) + signed bs := by
    have : (signed (negWord bs) + signed bs) % 2 ^ bs.length = 0 := by
      rw [Int.add_emod, hs1, hs2]; exact hv'
    exact Int.dvd_of_emod_eq_zero this
  have h3' : -(2 : ℤ) ^ (bs.length - 1) < signed bs := lt_of_le_of_ne h3 (Ne.symm h)
  have habs : |signed (negWord bs) + signed bs| < 2 ^ bs.length := by
    rw [abs_lt]; constructor <;> linarith
  have := Int.eq_zero_of_abs_lt_dvd hdvd habs
  linarith

end IntegerMultBounds.Machine.TwosComplement
