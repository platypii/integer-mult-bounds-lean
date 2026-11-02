module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringTransposeCaller
public import IntegerMultBounds.MathlibTM2.Host.RedirectRegister

/-! Two bit planes share one private worker. The second static register map
redirects only its owned payload to the separate imaginary-plane register. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host
namespace PackedTranspose
noncomputable section

abbrev kernelT : ℕ := FixedStreamedBank.tapeCount+117
abbrev tapeCount : ℕ := kernelT+7

def base (i : Fin kernelT) : Fin tapeCount := ⟨i.val,by change i.val < kernelT+7; have := i.isLt; omega⟩
def extra (j : Fin 7) : Fin tapeCount := ⟨kernelT+j.val,by change kernelT+j.val < kernelT+7; have := j.isLt; omega⟩
def owned : Fin kernelT := FixedStreamedBank.callerWorker (FixedStreamedBank.workerReg (reg FixedStreamedBank.pay))

theorem base_injective : Function.Injective base := by
  intro i j h
  have hh := congrArg (fun x : Fin tapeCount => x.val) h
  exact Fin.ext hh

theorem base_extra (i : Fin kernelT) (j : Fin 7) : base i ≠ extra j := by
  have hi := i.isLt
  simp [base,extra,Fin.ext_iff]
  omega

def planeReg (imaginary : Bool) : Fin tapeCount := if imaginary then extra 0 else base owned

def placement (imaginary : Bool) : Fin kernelT → Fin tapeCount :=
  if imaginary then redirectRegister base owned (extra 0) else base

theorem placement_injective (imaginary : Bool) : Function.Injective (placement imaginary) := by
  cases imaginary
  · exact base_injective
  · exact redirectRegister_injective base base_injective owned (extra 0) (fun i => base_extra i 0)

@[simp] theorem placement_owned (imaginary : Bool) : placement imaginary owned = planeReg imaginary := by
  cases imaginary <;> simp [placement,planeReg]

theorem placement_off (imaginary : Bool) (i : Fin kernelT) (hi : i ≠ owned) :
    placement imaginary i = base i := by
  cases imaginary <;> simp [placement,redirectRegister,hi]

@[simp] theorem placement_generator (imaginary : Bool) (j : Fin 117) :
    placement imaginary (FixedStreamedBank.callerGenerator j) = base (FixedStreamedBank.callerGenerator j) :=
  placement_off imaginary _ (FixedStreamedBank.payload_off_generator j)

theorem planeReg_ne : planeReg false ≠ planeReg true := base_extra owned 0

end
end PackedTranspose
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
