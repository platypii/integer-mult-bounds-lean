import IntegerMultBounds.Machine.RadixDivisionData

/-! A finite signed-carry transducer for any fixed rational coefficient. Its
state interval depends only on the integer numerator and natural denominator,
not the radix-word width. Digit congruences make every carry division exact. -/

namespace IntegerMultBounds.Machine.RadixRationalData

open RadixDigits
variable {q d : ℕ} {a : ℤ} [Fact q.Prime]

abbrev State (a : ℤ) (d : ℕ) := Fin (2*a.natAbs+d+1)

def signed (c : State a d) : ℤ := (c.val : ℤ) - a.natAbs

def initial (a : ℤ) (d : ℕ) : State a d := ⟨a.natAbs,by omega⟩

@[simp] theorem initial_signed : signed (initial a d) = 0 := by simp [signed,initial]

theorem signed_bounds (c : State a d) :
    -(a.natAbs : ℤ) ≤ signed c ∧ signed c ≤ (a.natAbs : ℤ)+d := by
  have hc := c.isLt
  dsimp [signed]
  omega

/-- The selected digit solves d*y = a*x-c in the prime residue field. -/
def digit (c : State a d) (x : Fin q) : Fin q :=
  ⟨((d : ZMod q)⁻¹ * ((a : ZMod q)*(x.val : ZMod q)-(signed c : ZMod q))).val,ZMod.val_lt _⟩

def numerator (c : State a d) (x : Fin q) : ℤ :=
  (d : ℤ)*(digit c x).val + signed c - a*x.val

private theorem quotient_bounds (c : State a d) (x : Fin q) :
    -(a.natAbs : ℤ) ≤ numerator c x / q ∧
      numerator c x / q ≤ (a.natAbs : ℤ)+d := by
  have hq : (0 : ℤ) < q := by exact_mod_cast (Fact.out : q.Prime).pos
  have ha : -(a.natAbs : ℤ) ≤ a := by simpa [Int.natCast_natAbs] using neg_abs_le a
  have hb : a ≤ (a.natAbs : ℤ) := Int.le_natAbs
  have hx : (0 : ℤ) ≤ x.val := by positivity
  have hy : (0 : ℤ) ≤ (digit c x).val := by positivity
  have hxt : (x.val : ℤ) ≤ (q : ℤ)-1 := by
    have h : (x.val : ℤ) < q := by exact_mod_cast x.isLt
    omega
  have hyt : ((digit c x).val : ℤ) ≤ (q : ℤ)-1 := by
    have h : ((digit c x).val : ℤ) < q := by exact_mod_cast (digit c x).isLt
    omega
  have hab : (0 : ℤ) ≤ a.natAbs := by positivity
  have hd : (0 : ℤ) ≤ d := by positivity
  obtain ⟨hc₁,hc₂⟩ := signed_bounds c
  have hax₁ := mul_le_mul_of_nonneg_right ha hx
  have hax₂ := mul_le_mul_of_nonneg_right hb hx
  have hax₃ := mul_le_mul_of_nonneg_left hxt hab
  have hdy₁ := mul_nonneg hd hy
  have hdy₂ := mul_le_mul_of_nonneg_left hyt hd
  constructor
  · apply (Int.le_ediv_iff_mul_le hq).mpr
    dsimp only [numerator]
    nlinarith
  · apply Int.ediv_le_of_le_mul hq
    dsimp only [numerator]
    nlinarith

/-- Encode the next signed carry back into the same fixed finite interval. -/
def carry (c : State a d) (x : Fin q) : State a d :=
  ⟨(numerator c x / q + a.natAbs).toNat,by
    obtain ⟨hl,hu⟩ := quotient_bounds c x
    omega⟩

theorem signed_carry (c : State a d) (x : Fin q) :
    signed (carry c x) = numerator c x / q := by
  obtain ⟨hl,_hu⟩ := quotient_bounds c x
  simp only [signed,carry]
  rw [Int.toNat_of_nonneg (by omega)]
  omega

/-- The finite lookup makes the entire signed numerator divisible by the radix. -/
theorem numerator_dvd (hdpos : 0 < d) (hdq : d < q) (c : State a d) (x : Fin q) :
    (q : ℤ) ∣ numerator c x := by
  have hd : (d : ZMod q) ≠ 0 := by
    intro h
    have hh := (ZMod.natCast_eq_zero_iff d q).mp h
    have hle := Nat.le_of_dvd hdpos hh
    omega
  have hv : ((digit c x).val : ZMod q) =
      (d : ZMod q)⁻¹*((a : ZMod q)*(x.val : ZMod q)-(signed c : ZMod q)) :=
    ZMod.natCast_zmod_val _
  apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ q).mp
  simp only [numerator,Int.cast_sub,Int.cast_add,Int.cast_mul,Int.cast_natCast]
  rw [hv,← mul_assoc,mul_inv_cancel₀ hd,one_mul]
  ring

/-- Exact signed column arithmetic, without a truncation or bounded-register assumption. -/
theorem column (hdpos : 0 < d) (hdq : d < q) (c : State a d) (x : Fin q) :
    (d : ℤ)*(digit c x).val + signed c = a*x.val + (q : ℤ)*signed (carry c x) := by
  rw [signed_carry]
  have hh := Int.ediv_mul_cancel (numerator_dvd hdpos hdq c x)
  dsimp only [numerator] at hh ⊢
  nlinarith

def digits : State a d → List (Fin q) → List (Fin q)
  | _, [] => []
  | c, x :: xs => digit c x :: digits (carry c x) xs

def overflow : State a d → List (Fin q) → State a d
  | c, [] => c
  | c, x :: xs => overflow (carry c x) xs

@[simp] theorem digits_length (c : State a d) (xs : List (Fin q)) :
    (digits c xs).length = xs.length := by
  induction xs generalizing c with
  | nil => rfl
  | cons x xs ih => simp only [digits,List.length_cons,ih]

/-- Exact rational scaling identity for every width and every finite initial carry. -/
theorem digits_value (hdpos : 0 < d) (hdq : d < q) (c : State a d) (xs : List (Fin q)) :
    (d : ℤ)*(value (digits c xs) : ℤ) + signed c =
      a*(value xs : ℤ) + (q : ℤ)^xs.length * signed (overflow c xs) := by
  induction xs generalizing c with
  | nil => simp [digits,overflow,value]
  | cons x xs ih =>
    have hc := column hdpos hdq c x
    have hi := ih (carry c x)
    simp only [digits,overflow,value,List.length_cons,pow_succ,Nat.cast_add,Nat.cast_mul]
    nlinarith

/-- With zero initial carry, the discarded tail is an exact multiple of the
word modulus, even for a negative integer numerator. -/
theorem initial_value (hdpos : 0 < d) (hdq : d < q) (xs : List (Fin q)) :
    (d : ℤ)*(value (digits (initial a d) xs) : ℤ) =
      a*(value xs : ℤ) + (q : ℤ)^xs.length * signed (overflow (initial a d) xs) := by
  simpa only [initial_signed,add_zero] using digits_value hdpos hdq (initial a d) xs

end IntegerMultBounds.Machine.RadixRationalData
