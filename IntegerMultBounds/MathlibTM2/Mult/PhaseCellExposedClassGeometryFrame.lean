module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClassGeometryFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExposedClassLayout

/-! Numerical geometry loading preserves the concrete exposure/routing inputs. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
open PackedTranspose
variable {T A : ℕ}

noncomputable def classCallerRegister (k : Fin T) : Fin ((T+175)+PackedTranspose.tapeCount) :=
  exposureIntoRouting T (Fin.castAdd 175 k)

noncomputable def fullExposedClassBank (bank : ComputedClassBank → Fin T) :
    ComputedClassBank → Fin ((T+175)+PackedTranspose.tapeCount) := extendedBank (exposedClassBank bank)

theorem classCallerRegister_injective : Function.Injective (classCallerRegister (T := T)) := by
  intro i j he
  apply Fin.ext
  have hv := congrArg (fun k : Fin ((T+175)+PackedTranspose.tapeCount) => k.val) he
  simpa only [classCallerRegister,exposureIntoRouting,Fin.val_castAdd] using hv

theorem fullExposedClassBank_injective (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank) :
    Function.Injective (fullExposedClassBank bank) :=
  extendedBank_injective _ (exposedClassBank_injective bank hinj)

@[simp] theorem fullExposedClassBank_apply (bank : ComputedClassBank → Fin T) (i : ComputedClassBank) :
    fullExposedClassBank bank i = classCallerRegister (bank i) := by
  simp only [fullExposedClassBank,extendedBank,exposedClassBank,classCallerRegister,exposureIntoRouting]

theorem loadedClassGeometry_caller (bank : ComputedClassBank → Fin T)
    (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (S : Stacks ((T+175)+PackedTranspose.tapeCount) A) (k : Fin T) (hoff : ∀ i, k ≠ bank i) :
    (loadedClassGeometry (fullExposedClassBank bank) src S).R (classCallerRegister k) = S.R (classCallerRegister k) := by
  apply loadedClassGeometry_external
  intro i he
  rw [fullExposedClassBank_apply] at he
  exact hoff i (classCallerRegister_injective he)

theorem loadedClassGeometry_exposure (bank : ComputedClassBank → Fin T)
    (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (S : Stacks ((T+175)+PackedTranspose.tapeCount) A) (i : Fin 175) :
    (loadedClassGeometry (fullExposedClassBank bank) src S).R (exposureIntoRouting T (Fin.natAdd T i)) =
      S.R (exposureIntoRouting T (Fin.natAdd T i)) := by
  apply loadedClassGeometry_external
  intro k he
  have hv := congrArg (fun j : Fin ((T+175)+PackedTranspose.tapeCount) => j.val) he
  have hk := (bank k).isLt
  simp only [exposureIntoRouting,fullExposedClassBank,extendedBank,exposedClassBank,
    Fin.val_castAdd,Fin.val_natAdd] at hv
  omega

theorem loadedClassGeometry_routing (bank : ComputedClassBank → Fin T)
    (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (S : Stacks ((T+175)+PackedTranspose.tapeCount) A) (i : Fin PackedTranspose.tapeCount) :
    (loadedClassGeometry (fullExposedClassBank bank) src S).R (Fin.natAdd (T+175) i) = S.R (Fin.natAdd (T+175) i) := by
  apply loadedClassGeometry_external
  intro k
  exact (prefix_ne_routing (exposedClassBank bank k) i).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.ComputedClassBanks
