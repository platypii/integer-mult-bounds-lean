import IntegerMultBounds.Machine.CyclicRowNormalized
import Mathlib.Data.List.OfFn

/-! Serialization for the width-one recursive base case. Two cyclic splits
isolate the fixed radix digits; exchanging the fixed pair of stream indices
and applying the two inverse merges transposes the digits, preserving arbitrary
outer, middle and suffix fields. Physical composition is a separate step. -/
namespace IntegerMultBounds.Machine.DigitInterchangeRows
open CyclicRowSplit
variable {O q C E a : ℕ}

abbrev Array (O q C E a : ℕ) := Fin O → Fin q → Fin C → Fin q → Fin E → Fin (a+4)

def transpose (x : Array O q C E a) : Array O q C E a := fun o h c d e => x o d c h e

@[simp] theorem transpose_twice (x : Array O q C E a) : transpose (transpose x) = x := rfl

def outerRows (x : Array O q C E a) (o : Fin O) (h : Fin q) : List (Fin (a+4)) :=
  (List.ofFn fun c : Fin C => (List.ofFn fun d : Fin q => List.ofFn (x o h c d)).flatten).flatten

def innerRows (x : Array O q C E a) (h : Fin q) (oc : Fin (O*C)) (d : Fin q) : List (Fin (a+4)) :=
  let p := finProdFinEquiv.symm oc
  List.ofFn (x p.1 h p.2 d)

theorem inner_length (x : Array O q C E a) (h : Fin q) (oc : Fin (O*C)) (d : Fin q) :
    (innerRows x h oc d).length = E := by simp [innerRows]

theorem outer_length (x : Array O q C E a) (o : Fin O) (h : Fin q) :
    (outerRows x o h).length = C*(q*E) := by
  simp [outerRows,List.length_flatten,List.map_ofFn,Function.comp_def]

private theorem flatten_ofFn_product {α : Type*} {m n : ℕ} (f : Fin (m*n) → List α) :
    (List.ofFn f).flatten =
      (List.ofFn fun i : Fin m => (List.ofFn fun j : Fin n => f (finProdFinEquiv (i,j))).flatten).flatten := by
  rw [List.ofFn_mul f,List.flatten_flatten,List.map_ofFn]
  simp only [Function.comp_def,finProdFinEquiv,Equiv.coe_fn_mk,Nat.add_comm,Nat.mul_comm]

/-- The first split's literal role stream is already the second split's input;
there is no free array rearrangement between the two physical passes. -/
theorem outer_role_inner_source (x : Array O q C E a) (h : Fin q) :
    roleWord (outerRows x) h = sourceWord (innerRows x h) := by
  unfold roleWord sourceWord cycleWords
  rw [flatten_ofFn_product]
  unfold innerRows
  simp only [Equiv.symm_apply_apply,outerRows]

/-- Swapping the two fixed stream indices gives exactly the transpose leaves. -/
theorem inner_role_transpose (x : Array O q C E a) (h d : Fin q) :
    roleWord (innerRows (transpose x) h) d = roleWord (innerRows x d) h := rfl

end IntegerMultBounds.Machine.DigitInterchangeRows
