module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingRowStep

/-! Separate the retained source and outer row counter from row arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def cachedCouplingOuterReg (i : Fin 118) : Fin 145 :=
  ⟨if i.val < 117 then i.val else 144,by split <;> omega⟩

theorem cachedCouplingOuterReg_injective : Function.Injective cachedCouplingOuterReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 145 => k.val) he
  simp only [cachedCouplingOuterReg] at hv
  have hi := i.isLt
  have hj := j.isLt
  split at hv <;> split at hv <;> apply Fin.ext <;> omega

theorem cachedCouplingOuterReg_off (j : Fin 145) (hlo : 117 ≤ j.val) (hhi : j.val < 144)
    (i : Fin 118) : cachedCouplingOuterReg i ≠ j := by
  intro he
  have hv := congrArg (fun k : Fin 145 => k.val) he
  simp only [cachedCouplingOuterReg] at hv
  split at hv <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
