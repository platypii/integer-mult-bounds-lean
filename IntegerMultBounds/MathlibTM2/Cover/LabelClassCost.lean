module

public import IntegerMultBounds.MathlibTM2.Cover.LabelSelectors

/-! Sum record costs that depend only on the residue digits. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.LabelSelectors
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open IntegerMultBounds.Machine.RecursiveInterchangeLayout

private theorem sum_classes (H k : ℕ) (f : (Fin k → ZMod prime) → ℕ) :
    ((classes H k).map f).sum = H^k*((classes 1 k).map f).sum := by
  induction k with
  | zero => simp [classes]
  | succ k ih =>
    simp only [classes,List.map_flatMap,List.map_map,Function.comp_def]
    simp only [List.flatMap_def,List.sum_flatten,List.map_map,Function.comp_def]
    let row (a : Fin k → ZMod prime) := (((cycle 1).map fun b => f (Fin.cons b a))).sum
    have scale (a : Fin k → ZMod prime) :
        ((cycle H).map fun b => f (Fin.cons b a)).sum = H*row a := by
      simp [cycle,row,List.map_map,Function.comp_def]
    simp_rw [scale]
    rw [List.sum_map_mul_left,ih row,pow_succ]
    simp [row,Nat.mul_assoc,Nat.mul_comm]

theorem recordMap_sum (v : Descriptor) (m w B : ℕ) (shape : v.beforeH = B*prime^(m*((w+1)*m)))
    (f : (Fin (m*m) → ZMod prime) → ℕ) :
    (recordMap v m (w+1) f).sum = (v.beforeRows*v.rows*B)*(prime^w)^(m*m)*
      ((classes 1 (m*m)).map f).sum := by
  rw [recordMap_eq v m (w+1) B (by omega) shape]
  rw [Nat.add_one_sub_one,Nat.mul_assoc (v.beforeRows*v.rows*B),← sum_classes]
  simp

end IntegerMultBounds.MathlibTM2.Cover.LabelSelectors
