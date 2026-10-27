module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedCouplingRowStep

/-! Separate the retained source and outer row counter from row arithmetic. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def cachedCouplingOuterReg (i : Fin 118) : Fin 144 :=
  ⟨if i.val < 117 then i.val else 141,by split <;> omega⟩

theorem cachedCouplingOuterReg_injective : Function.Injective cachedCouplingOuterReg := by
  intro i j he
  have hv := congrArg (fun k : Fin 144 => k.val) he
  simp only [cachedCouplingOuterReg] at hv
  have hi := i.isLt
  have hj := j.isLt
  split at hv <;> split at hv <;> apply Fin.ext <;> omega

theorem cachedCouplingOuterReg_off (j : Fin 144) (hlo : 117 ≤ j.val) (hcache : j ≠ 141)
    (i : Fin 118) : cachedCouplingOuterReg i ≠ j := by
  intro he
  have hv := congrArg (fun k : Fin 144 => k.val) he
  simp only [cachedCouplingOuterReg] at hv
  have hj : j.val ≠ 141 := fun he => hcache (Fin.ext he)
  split at hv <;> omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
