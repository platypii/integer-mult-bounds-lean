import IntegerMultBounds.Machine.SelectedSourceBitsData

/-! The selected control stream is computed from every literal full-source
row in order. Each row contributes n bits from positions rho+i*q. -/
namespace IntegerMultBounds.Machine.SelectedSourceBitsStreamData
open SelectedSourceBitsData

def selected (xs : List Bool) (q rho n f P : ℕ) : List Bool :=
  (List.range P).flatMap (fun r => SelectedSourceBitsData.selected xs q (r*(f*q)+rho) n)

@[simp] theorem selected_zero (xs : List Bool) (q rho n f : ℕ) : selected xs q rho n f 0 = [] := rfl

theorem selected_succ (xs : List Bool) (q rho n f P : ℕ) :
    selected xs q rho n f (P+1) = selected xs q rho n f P++
      SelectedSourceBitsData.selected xs q (P*(f*q)+rho) n := by
  simp [selected,List.range_succ]

@[simp] theorem selected_length (xs : List Bool) (q rho n f P : ℕ) :
    (selected xs q rho n f P).length = P*n := by
  induction P with
  | zero => simp
  | succ P ih => rw [selected_succ,List.length_append,ih,SelectedSourceBitsData.selected_length]; ring

theorem selected_testBit (xs : List Bool) (q rho n f P : ℕ) :
    selected xs q rho n f P = (List.range P).flatMap (fun r =>
      (List.range n).map (fun i => Nat.testBit (Counter.value xs) (r*(f*q)+rho+i*q))) := by
  simp only [selected,SelectedSourceBitsData.selected_testBit]

theorem selected_inside (xs : List Bool) (q rho n f P r i : ℕ)
    (hxs : xs.length=P*(f*q)) (hnf : n+1=f) (hrho : rho<q) (hr : r<P) (hi : i<n) :
    r*(f*q)+rho+i*q<xs.length := by
  have hs := SelectedSourceBitsData.span_le q rho n f hnf (by omega)
  have hprod : (i+1)*q≤n*q := Nat.mul_le_mul_right q (by omega)
  have hrow : (r+1)*(f*q)≤P*(f*q) := Nat.mul_le_mul_right (f*q) (by omega)
  nlinarith

end IntegerMultBounds.Machine.SelectedSourceBitsStreamData
