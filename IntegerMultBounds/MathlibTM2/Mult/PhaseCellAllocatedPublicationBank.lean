module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTransposePlacement
public import IntegerMultBounds.MathlibTM2.Host.RedirectRegister

/-! Reuse the private fixed routing bank after numerical execution. Only the
numerical result and ambient destination are shared with the caller prefix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds.MathlibTM2.Host
open FixedStreamedBank
noncomputable section
variable {T : ℕ}

def numericalPort : Fin tapeCount := base (callerGenerator 95)
def ambientPort : Fin tapeCount := base (callerGenerator 96)

theorem numericalPort_ne_ambientPort : numericalPort ≠ ambientPort := by
  apply base_injective.ne
  exact (TransposeRegisterPlacement.generator_injective _).ne (by decide : (95 : Fin 117) ≠ 96)

def publicationPlacement (src dst : Fin T) : Fin tapeCount → Fin (T+tapeCount) :=
  redirectRegister (redirectRegister (Fin.natAdd T) numericalPort (Fin.castAdd tapeCount src))
    ambientPort (Fin.castAdd tapeCount dst)

@[simp] theorem publicationPlacement_numerical (src dst : Fin T) :
    publicationPlacement src dst numericalPort = Fin.castAdd tapeCount src := by
  simp [publicationPlacement,redirectRegister,numericalPort_ne_ambientPort]

@[simp] theorem publicationPlacement_ambient (src dst : Fin T) :
    publicationPlacement src dst ambientPort = Fin.castAdd tapeCount dst := redirectRegister_owned _ _ _

theorem publicationPlacement_private (src dst : Fin T) (i : Fin tapeCount)
    (hnum : i ≠ numericalPort) (hout : i ≠ ambientPort) :
    publicationPlacement src dst i = Fin.natAdd T i := by
  simp [publicationPlacement,redirectRegister,hnum,hout]

theorem publicationPlacement_injective (src dst : Fin T) (hne : src ≠ dst) :
    Function.Injective (publicationPlacement src dst) := by
  have hprivate (x : Fin T) : ∀ i : Fin tapeCount, Fin.natAdd T i ≠ Fin.castAdd tapeCount x := by
    intro i he
    have hv := congrArg (fun k : Fin (T+tapeCount) => k.val) he
    have hx := x.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  apply redirectRegister_injective
  · exact redirectRegister_injective _ (by intro i j h; exact Fin.ext (by
      have hv := congrArg (fun k : Fin (T+tapeCount) => k.val) h
      simp only [Fin.val_natAdd] at hv
      omega)) numericalPort _ (hprivate src)
  · intro i
    by_cases hi : i = numericalPort
    · subst i
      simpa only [redirectRegister_owned] using (Fin.castAdd_injective T tapeCount).ne hne
    · simpa only [redirectRegister_off _ _ _ _ hi] using hprivate dst i

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
