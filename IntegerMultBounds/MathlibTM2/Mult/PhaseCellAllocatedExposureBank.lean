module

public import IntegerMultBounds.MathlibTM2.Host.RedirectRegister
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealGatherExposureData

/-! A private ambient-exposure bank. Only the original line source and gathered
payload destination are shared with the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast
variable {T : ℕ}

def exposurePlacement (output : Fin T) : Fin 168 → Fin (T+175) :=
  redirectRegister (fun i => Fin.natAdd T (Fin.castAdd 7 i)) 108 (Fin.castAdd 175 output)

def exposureControl (input : Fin T) : Fin 7 → Fin (T+175) :=
  redirectRegister (fun j => Fin.natAdd T (Fin.natAdd 168 j)) 1 (Fin.castAdd 175 input)

@[simp] theorem exposurePlacement_output (output : Fin T) :
    exposurePlacement output 108 = Fin.castAdd 175 output := redirectRegister_owned _ _ _

@[simp] theorem exposureControl_input (input : Fin T) :
    exposureControl input 1 = Fin.castAdd 175 input := redirectRegister_owned _ _ _

theorem exposurePlacement_private (output : Fin T) (i : Fin 168) (hi : i ≠ 108) :
    exposurePlacement output i = Fin.natAdd T (Fin.castAdd 7 i) := redirectRegister_off _ _ _ _ hi

theorem exposureControl_private (input : Fin T) (j : Fin 7) (hj : j ≠ 1) :
    exposureControl input j = Fin.natAdd T (Fin.natAdd 168 j) := redirectRegister_off _ _ _ _ hj

theorem exposurePlacement_injective (output : Fin T) : Function.Injective (exposurePlacement output) := by
  apply redirectRegister_injective
  · intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro i he
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    have ho := output.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

theorem exposureControl_injective (input : Fin T) : Function.Injective (exposureControl input) := by
  apply redirectRegister_injective
  · intro i j he
    apply Fin.ext
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    simp only [Fin.val_natAdd] at hv
    omega
  · intro i he
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    have hi := input.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

theorem exposureControl_off_placement (input output : Fin T) (hne : input ≠ output)
    (j : Fin 7) (i : Fin 168) : exposureControl input j ≠ exposurePlacement output i := by
  unfold exposureControl exposurePlacement redirectRegister
  split_ifs with hj hi hi
  · intro he
    exact hne (Fin.ext (congrArg (fun k : Fin (T+175) => k.val) he))
  · intro he
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    have hinput := input.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro he
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    have houtput := output.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega
  · intro he
    have hv := congrArg (fun k : Fin (T+175) => k.val) he
    have hi := i.isLt
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hv
    omega

theorem exposureControls_nodup (input : Fin T) :
    [exposureControl input 0,exposureControl input 1,exposureControl input 2,
      exposureControl input 3,exposureControl input 4,exposureControl input 5,exposureControl input 6].Nodup := by
  simp only [List.nodup_cons,List.mem_cons,List.not_mem_nil,List.nodup_nil,
    (exposureControl_injective input).eq_iff]
  decide

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
