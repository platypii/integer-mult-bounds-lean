module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellStreamedChunkBank

/-! One concrete streamed worker: five interchange header tapes and a payload,
followed by the existing swap machine's private bank and nineteen controls. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Host

namespace FixedStreamedBank
noncomputable section

def hd (k : Fin 5) : Fin 6 := ⟨k.val,by omega⟩
def pay : Fin 6 := 5

theorem hd_injective : Function.Injective hd := by
  intro i j h
  have hh := congrArg (fun x : Fin 6 => x.val) h
  exact Fin.ext hh

def tapeCount : ℕ := swapT 6+19
noncomputable def stateCount : ℕ := swapStates hd pay hd_injective

def workerReg (j : Fin (swapT 6)) : Fin tapeCount := ⟨j.val,by have := j.isLt; unfold tapeCount; omega⟩
def control (i : Fin 19) : Fin tapeCount := ⟨swapT 6+i.val,by have := i.isLt; unfold tapeCount; omega⟩

theorem workerReg_injective : Function.Injective workerReg := by
  intro i j h
  have hh := congrArg (fun x : Fin tapeCount => x.val) h
  exact Fin.ext hh

theorem control_injective : Function.Injective control := by
  intro i j h
  apply Fin.ext
  have hh := congrArg Fin.val h
  change swapT 6+i.val = swapT 6+j.val at hh
  omega

theorem hd_pay (k : Fin 5) : hd k ≠ pay := by
  have hk := k.isLt
  intro h
  have hh := congrArg (fun x : Fin 6 => x.val) h
  change k.val = 5 at hh
  omega

theorem dims_workerReg (k : Fin 5) (j : Fin (swapT 6)) :
    control ⟨k.val,by omega⟩ ≠ workerReg j := by
  have hk := k.isLt
  have hj := j.isLt
  simp [control,workerReg,Fin.ext_iff]
  omega

noncomputable def bank {Q : ℕ} (hstates : stateCount ≤ Q) : StreamedChunkBank 6 tapeCount Q where
  hd := hd
  pay := pay
  hi := hd_injective
  hpay := hd_pay
  hQ := hstates
  ι := workerReg
  hι := workerReg_injective
  hT := by unfold tapeCount; omega
  dims := fun k => control ⟨k.val,by omega⟩
  hdims := by
    intro i j h
    exact Fin.ext (congrArg (fun x : Fin 19 => x.val) (control_injective h))
  width := control 5
  zero := control 6
  queue := control 7
  binary := control 8
  duplicate := control 9
  readerWork := control 10
  saved := control 11
  tmp := control 12
  a := control 13
  half := control 14
  par := control 15
  bits := control 16
  cnt := control 17
  work := control 18
  hreader := by
    intro k
    have hk := k.isLt
    simp [List.nodup_cons,
      control,Fin.ext_iff]
    omega
  hgen := by
    intro k
    have hk := k.isLt
    have hp := (reg (hd k)).isLt
    simp [List.nodup_cons,
      control,workerReg,Fin.ext_iff]
    omega
  hdimOff := dims_workerReg
  hqueueOff := by
    intro j
    have hj := j.isLt
    simp [control,workerReg,Fin.ext_iff]
    omega
  hqueueControls := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp [control,Fin.ext_iff]
  hprotected := by
    have hpay : 5 < swapT 6 := (reg pay).isLt
    intro i hi
    simp only [List.mem_append,List.mem_cons,List.not_mem_nil,or_false,List.mem_ofFn] at hi
    rcases hi with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) | ⟨k,rfl⟩
    all_goals simp [control,workerReg,reg_val,pay,Fin.ext_iff]
    all_goals omega

end
end FixedStreamedBank
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
