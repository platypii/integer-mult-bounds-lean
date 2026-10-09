import IntegerMultBounds.Compact.KeyValue

/-! Selected original-source bits at rho+i*q. The complete source word remains
available; neither a supplied slice nor a fixed external control word is used. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsData

def selected (xs : List Bool) (q rho n : ℕ) : List Bool :=
  (List.range n).map (fun i => xs.getD (rho+i*q) false)
@[simp] theorem selected_length (xs : List Bool) (q rho n : ℕ) :
    (selected xs q rho n).length = n := by simp [selected]
@[simp] theorem selected_zero (xs : List Bool) (q rho : ℕ) : selected xs q rho 0 = [] := rfl

theorem selected_succ (xs : List Bool) (q rho n : ℕ) :
    selected xs q rho (n+1) = selected xs q rho n++[xs.getD (rho+n*q) false] := by
  simp [selected,List.range_succ]

theorem selected_testBit (xs : List Bool) (q rho n : ℕ) :
    selected xs q rho n = (List.range n).map (fun i => Nat.testBit (Counter.value xs) (rho+i*q)) := by
  simp only [selected,Compact.PowerTwo.testBit_value]

theorem selected_entry (xs : List Bool) (q rho n i : ℕ) (hi : i < n) :
    (selected xs q rho n)[i]'(by simp; omega) = Nat.testBit (Counter.value xs) (rho+i*q) := by
  simp [selected,Compact.PowerTwo.testBit_value]

theorem span_le (q rho n f : ℕ) (hn : n+1=f) (hr : rho ≤ q) : rho+n*q ≤ f*q := by
  subst f
  nlinarith

theorem selected_inside (xs : List Bool) (q rho n f i : ℕ)
    (hxs : xs.length=f*q) (hn : n+1=f) (hr : rho<q) (hi : i<n) : rho+i*q<xs.length := by
  have hspan := span_le q rho n f hn (by omega)
  have hprod : (i+1)*q ≤ n*q := Nat.mul_le_mul_right q (by omega)
  nlinarith

end IntegerMultBounds.Machine.SelectedSourceBitsData
