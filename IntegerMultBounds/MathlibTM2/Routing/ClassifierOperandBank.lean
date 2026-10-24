module

public import IntegerMultBounds.MathlibTM2.Routing.ClassifierGenerate

/-! The complete sixteen-role classifier bank is read from six generated
operands and one restored blank source. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}
noncomputable section

def classifierOperandSource : Fin 16 → Fin 118 :=
  ![112,113,39,39,39,39,39,39,39,39,114,39,39,115,116,117]

theorem classifierOperandSource_scratch (i : Fin 16) :
    classifierOperandSource i ≠ 40 ∧ classifierOperandSource i ≠ 41 := by
  fin_cases i <;> decide

theorem classifierGeneratedBank_operands (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 118 → Fin T) (hrg : Function.Injective rg) (L W : ℕ) (p : Par)
    (hblank : R (rg 39) = []) :
    (fun i => classifierGeneratedBank R rg L W p (rg (classifierOperandSource i))) =
      canonicalClassifierOperands p (canonicalScalarWidth p.K) (canonicalScalarWidth p.n)
        (canonicalScalarWidth (p.ρ+1)) (canonicalScalarWidth p.m) := by
  have field (i : Fin 6) := classifierScalarInstalledBank_at (classifierWidthBank R rg L W p)
    rg hrg p i
  have hz := (classifierGeneratedBank_low R rg hrg L W p 39 (by decide)).trans hblank
  funext i
  fin_cases i <;> first
    | exact field 0 | exact field 1 | exact field 2 | exact field 3
    | exact field 4 | exact field 5 | exact hz

end
end IntegerMultBounds.MathlibTM2.Routing
