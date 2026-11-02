module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringExposedGather

/-! Keep the numerical class in the original caller prefix, before the private
exposure and routing suffixes. Supplier ownership follows from this placement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open PackedTranspose
variable {T : ℕ}

def exposedClassBank (bank : ComputedClassBank → Fin T) : ComputedClassBank → Fin (T+175) :=
  fun k => Fin.castAdd 175 (bank k)

theorem exposedClassBank_injective (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank) :
    Function.Injective (exposedClassBank bank) := by
  intro i j he
  apply hinj
  apply Fin.ext
  have hv := congrArg (fun k : Fin (T+175) => k.val) he
  simpa only [exposedClassBank,Fin.val_castAdd] using hv

theorem exposedClassBank_off_exposure (bank : ComputedClassBank → Fin T) (k : ComputedClassBank)
    (i : Fin 175) : exposedClassBank bank k ≠ Fin.natAdd T i := by
  intro he
  have hv := congrArg (fun j : Fin (T+175) => j.val) he
  have hk := (bank k).isLt
  simp only [exposedClassBank,Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

@[simp] theorem exposedClassBank_source (bank : ComputedClassBank → Fin T) :
    control (extendedBank (exposedClassBank bank)) .source =
      exposureIntoRouting T (Fin.castAdd 175 (bank (.control .source))) := by
  simp only [control,extendedBank,exposedClassBank,exposureIntoRouting]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
