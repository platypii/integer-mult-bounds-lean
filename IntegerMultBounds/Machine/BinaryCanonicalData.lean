import IntegerMultBounds.Machine.GrowingCounterData

/-! Canonical little-endian binary words are uniquely determined by value.
These lemmas identify physically emitted normalized descriptors with semantic
counter values without assuming a chosen binary representation as input. -/
namespace IntegerMultBounds.Machine.BinaryCanonicalData

theorem tail (b : Bool) (xs : List Bool) (hc : GrowingCounterData.Canonical (b::xs)) :
    GrowingCounterData.Canonical xs := by
  cases xs with
  | nil => exact Or.inl rfl
  | cons c cs =>
    rcases hc with he | he
    · cases he
    · exact Or.inr (by simpa using he)

theorem zero_nil (xs : List Bool) (hc : GrowingCounterData.Canonical xs)
    (hv : Counter.value xs = 0) : xs = [] := by
  have hw := GrowingCounterData.canonical_width xs hc
  rw [hv] at hw
  have hl : xs.length ≤ 1 := hw
  cases xs with
  | nil => rfl
  | cons b xs =>
    have ht : xs = [] := List.eq_nil_of_length_eq_zero (by simp only [List.length_cons] at hl; omega)
    subst xs
    cases b <;> simp [GrowingCounterData.Canonical,Counter.value] at hc hv

theorem value_injective (xs ys : List Bool) (hx : GrowingCounterData.Canonical xs)
    (hy : GrowingCounterData.Canonical ys) (hv : Counter.value xs = Counter.value ys) : xs = ys := by
  induction xs generalizing ys with
  | nil => exact (zero_nil ys hy hv.symm).symm
  | cons x xs ih =>
    cases ys with
    | nil => have he := zero_nil (x::xs) hx hv; cases he
    | cons y ys =>
      have hxt := tail x xs hx
      have hyt := tail y ys hy
      cases x <;> cases y <;> simp only [Counter.value,Bool.false_eq_true,ite_false,ite_true,zero_add] at hv
      · exact congrArg (List.cons false) (ih ys hxt hyt (by omega))
      · omega
      · omega
      · exact congrArg (List.cons true) (ih ys hxt hyt (by omega))

end IntegerMultBounds.Machine.BinaryCanonicalData
