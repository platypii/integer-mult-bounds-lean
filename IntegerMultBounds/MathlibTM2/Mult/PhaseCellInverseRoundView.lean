module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundVariables
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareInverseRound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyInverseCallerWorkspace

/-! Rounding shares the inverse scalar bank and uses released core ports. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2.Fast.TableVM

def inverseRoundScalarReg : TblR 8 → Fin 303 :=
  familyInverseScalarReg ∘ TblR.rename inverseRoundVariables

theorem inverseRoundScalarReg_injective : Function.Injective inverseRoundScalarReg :=
  familyInverseScalarReg_injective.comp (TblR.rename_injective inverseRoundVariables_injective)

def inverseRoundPorts (i : Fin 4) : Fin 303 := ⟨i.val,by omega⟩

theorem inverseRoundPorts_injective : Function.Injective inverseRoundPorts := by
  intro i j he
  exact Fin.ext (congrArg (fun k : Fin 303 => k.val) he)

theorem inverseRoundScalarReg_ports (i : Fin 4) (r : TblR 8) :
    inverseRoundScalarReg r ≠ inverseRoundPorts i := by
  have h := familyInverseScalarReg_core (r.rename inverseRoundVariables) (⟨i.val,by omega⟩ : Fin 263)
  simpa [inverseRoundScalarReg,inverseRoundPorts,familyInverseScalarReg,familyInverseCoreReg,show i.val < 224 by omega] using h

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
