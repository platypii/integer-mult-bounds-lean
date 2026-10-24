module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalData
public import Mathlib.Data.Nat.Log

/-! The length of canonical binary digits is the ceiling logarithm of one
more than their value, including the empty representation of zero. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

theorem canonicalBinary_length_clog (bs : List Bool) (hc : GrowingCounterData.Canonical bs) :
    bs.length = Nat.clog 2 (Counter.value bs + 1) := by
  apply Nat.le_antisymm
  · by_cases hv : Counter.value bs = 0
    · rcases hc with rfl | hlast
      · simp [Counter.value]
      · obtain ⟨xs, rfl⟩ := List.getLast?_eq_some_iff.mp hlast
        have hw := GrowingCounterData.canonical_width (xs ++ [true]) (Or.inr (by simp))
        rw [hv] at hw
        have hx : xs = [] := List.eq_nil_of_length_eq_zero (by simpa using hw)
        subst xs
        simp [Counter.value] at hv
    · have hw := GrowingCounterData.canonical_width bs hc
      have hp := Nat.log2_self_le hv
      have hl : (Counter.value bs).log2 < Nat.clog 2 (Counter.value bs + 1) :=
        (Nat.lt_clog_iff_pow_lt (by decide)).mpr (Nat.lt_succ_of_le hp)
      omega
  · exact Nat.clog_le_of_le_pow (Nat.succ_le_of_lt (Counter.value_lt bs))

end IntegerMultBounds.MathlibTM2.Routing
