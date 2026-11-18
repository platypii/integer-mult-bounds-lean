module

public import IntegerMultBounds.MathlibTM2.Cover.FallbackConjugate

/-! Fixed division-free formulas for the determinants used in row conjugation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cover.Fallback
noncomputable section

inductive RingFormula (ι : Type)
  | input (i : ι)
  | zero
  | one
  | sub (x y : RingFormula ι)
  | mul (x y : RingFormula ι)

namespace RingFormula
variable {ι R : Type} [CommRing R]

def eval (read : ι → R) : RingFormula ι → R
  | .input i => read i
  | .zero => 0
  | .one => 1
  | .sub x y => eval read x - eval read y
  | .mul x y => eval read x * eval read y

def sum (terms : List (RingFormula ι)) := terms.foldr (fun x y => sub x (sub zero y)) zero
def product (terms : List (RingFormula ι)) := terms.foldr mul one

theorem eval_sum (read : ι → R) (terms : List (RingFormula ι)) :
    eval read (sum terms) = (terms.map (eval read)).sum := by
  induction terms with
  | nil => rfl
  | cons x xs ih => simp [sum,eval] at ih ⊢; rw [ih]

theorem eval_product (read : ι → R) (terms : List (RingFormula ι)) :
    eval read (product terms) = (terms.map (eval read)).prod := by
  induction terms with
  | nil => rfl
  | cons x xs ih => simp [product,eval] at ih ⊢; rw [ih]

variable {m : ℕ}

def determinant (entry : Fin m → Fin m → RingFormula ι) : RingFormula ι :=
  sum (Finset.univ.toList.map fun σ : Equiv.Perm (Fin m) =>
    let term := product (Finset.univ.toList.map fun i => entry (σ i) i)
    if Equiv.Perm.sign σ = 1 then term else sub zero term)

theorem eval_determinant (read : ι → R) (entry : Fin m → Fin m → RingFormula ι) :
    eval read (determinant entry) = (Matrix.of fun i j => eval read (entry i j)).det := by
  rw [determinant,eval_sum,List.map_map,Finset.sum_map_toList,Matrix.det_apply']
  apply Finset.sum_congr rfl
  intro σ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h | h <;>
    simp [Function.comp_def,h,eval,eval_product,List.map_map,Finset.prod_map_toList]

/-- Replace row j by row i of the product before expanding the numerator determinant. -/
def numerator (g P : Fin m → Fin m → RingFormula ι) (i j : Fin m) : RingFormula ι :=
  determinant (fun r c => if r = j then
    sum (Finset.univ.toList.map fun k => mul (g i k) (P k c)) else g r c)

theorem eval_numerator (read : ι → R) (g P : Fin m → Fin m → RingFormula ι) (i j : Fin m) :
    eval read (numerator g P i j) = conjugateNumerator (Matrix.of fun r c => eval read (g r c))
      (Matrix.of fun r c => eval read (P r c)) i j := by
  rw [numerator,eval_determinant,conjugateNumerator]
  congr 1
  ext r c
  by_cases h : r = j
  · subst r
    simp [eval_sum,List.map_map,Function.comp_def,eval,Finset.sum_map_toList,Matrix.mul_apply]
  · simp [h,Matrix.updateRow]
    exact (congrFun (Function.update_of_ne h _ (fun r c => eval read (g r c))) c).symm

end RingFormula
end
end IntegerMultBounds.MathlibTM2.Cover.Fallback
