module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicPackedAssembly

/-! Both physical recovery archives share one 56-tape normalization workspace.
The common output-width word is ordinary publication metadata on tape 906. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicPackedNormalizationPlacement
open IntegerMultBounds.MathlibTM2.Host

abbrev extend : Fin 850 → Fin 907 := Fin.castLE (by decide)

def source (right : Bool) : Fin 850 := if right then 849 else 848

def gather (right : Bool) : Fin 126 → Fin 850 :=
  CyclicPackedAssemblyPlacement.extend ∘
    (if right then CyclicSecondInteriorPlacement.right.plan.gather else CyclicSecondInteriorPlacement.left.plan.gather)

def borrowed (right : Bool) : Fin 8 → Fin 907 :=
  fun i => (if right then ([414,412,411,413,423,421,906,849] : List (Fin 907))
    else [114,112,111,113,123,121,906,848])[i.val]'(by cases right <;> simpa using i.isLt)

def placement (right : Bool) (i : Fin 64) : Fin 907 :=
  if hi : i.val < 8 then borrowed right ⟨i.val,hi⟩ else ⟨842+i.val,by omega⟩

theorem placement_injective (right : Bool) : Function.Injective (placement right) := by
  have h : ∀ right : Bool, Function.Injective (placement right) := by decide +kernel
  exact h right

theorem placement_old (right : Bool) :
    placement right 0 = extend (gather right 114) ∧
    placement right 1 = extend (gather right 112) ∧
    placement right 2 = extend (gather right 111) ∧
    placement right 3 = extend (gather right 113) ∧
    placement right 4 = extend (gather right 123) ∧
    placement right 5 = extend (gather right 121) ∧
    placement right 6 = 906 ∧ placement right 7 = extend (source right) := by
  cases right <;> decide +kernel

theorem placement_fresh (right : Bool) (i : Fin 64) (hi : 8 ≤ i.val) :
    850 ≤ (placement right i).val ∧ (placement right i).val < 906 := by
  simp only [placement,dif_neg (by omega : ¬i.val < 8)]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicPackedNormalizationPlacement
