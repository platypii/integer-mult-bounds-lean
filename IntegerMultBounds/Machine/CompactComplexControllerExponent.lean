import IntegerMultBounds.Machine.CompactComplexControllerNativeFrame
import IntegerMultBounds.Machine.CompactComplexExponentStep

/-! Physical recursive exponent bookkeeping on root controller1, with the
two work tapes taken from its already blank arithmetic workspace28/29.
Native66 and all persistent appended storage remain literally unchanged. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerExponent
noncomputable section
open ActiveRepairRankHeadersCommands (State bank put)
open CompactComplexControllerNativeFrame (tapes controllerSlot)
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)
variable {a s : ℕ}

def focus : Fin 3 → Fin (tapes s) := fun i => controllerSlot (![1,28,29] i)
theorem focus_injective : Function.Injective (focus (s := s)) := by
  intro i j h
  have hv := congrArg Fin.val h
  simp only [focus,controllerSlot,Fin.val_castAdd] at hv
  fin_cases i <;> fin_cases j <;> simp_all

def placement := InjectivePlacement.placement (focus (s := s)) focus_injective
  (by unfold tapes; omega : 3+(tapes s-3)=tapes s)
def program := Placement.placed (CompactComplexExponentStep.program (a := a)) (placement (s := s))
def ascendProgram := CompactComplexExponentStep.ascendProgram (a := a) (controllerSlot (s := s) 1)

def input (st : State) (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :=
  CompactComplexControllerNativeFrame.bank (bank st) queue native storage

private theorem active_input (st : State) (e : ℕ) (h1 : st 1=some e)
    (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :
    Placement.active placement (input st queue native storage)=CompactComplexExponentStep.bank e := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp only [placement,InjectivePlacement.active_slot,focus,controllerSlot,input,
    CompactComplexControllerNativeFrame.bank,Tapes.append,Fin.addCases_left]
  all_goals fin_cases i
  all_goals simp [bank,CleanSubbank.bank,ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases,
    SharedBank.empty,h1,BinaryDescriptorStackRoundtrip.descriptor_encoded]

private theorem updated (st : State) (value : ℕ) (queue : Tapes 1 a) (native : Tapes 66 a)
    (storage : Tapes s a) :
    setTape (input st queue native storage) (controllerSlot 1) (BinaryDescriptorStack.descriptor (bits value)) 1=
      input (put st 1 value) queue native storage := by
  unfold input CompactComplexControllerNativeFrame.bank controllerSlot
  rw [SharedPlacementAlphabet.setTape_append_left,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  unfold bank CleanSubbank.bank
  change (setTape ((ActiveRepairRankHeadersCommands.caller st).append (SharedBank.empty 15 a))
    (Fin.castAdd 15 (1 : Fin 28)) (RadixZeroFill.encodedBinary (bits value)) 1).append _= _
  rw [SharedPlacementAlphabet.setTape_append_left,← ActiveRepairRankHeadersCommands.put_caller]

theorem descend (st : State) (e : ℕ) (he : 0<e) (h1 : st 1=some e)
    (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :
    HoareTime program (fun v => v=input st queue native storage)
      (fun v => v=input (put st 1 (e-1)) queue native storage) (20*(e+1)+100) := by
  have h := CompactComplexExponentStep.runs_at placement (input st queue native storage) e he
    (active_input st e h1 queue native storage)
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  simp only [placement,InjectivePlacement.active_slot,focus]
  exact updated st (e-1) queue native storage

theorem ascend (st : State) (e : ℕ) (he : 0<e) (h1 : st 1=some (e-1))
    (queue : Tapes 1 a) (native : Tapes 66 a) (storage : Tapes s a) :
    HoareTime ascendProgram (fun v => v=input st queue native storage)
      (fun v => v=input (put st 1 e) queue native storage) (2*(e+1)) := by
  have h := CompactComplexExponentStep.ascend_parent (controllerSlot 1) (input st queue native storage) e he
    (by simpa [input,CompactComplexControllerNativeFrame.bank,controllerSlot,bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases,h1] using
      (BinaryDescriptorStackRoundtrip.descriptor_encoded (a := a) (bits (e-1))).symm)
    (by simp [input,CompactComplexControllerNativeFrame.bank,controllerSlot,bank,CleanSubbank.bank,
      ActiveRepairRankHeadersCommands.caller,Tapes.append,Fin.addCases,h1])
  apply h.consequence (fun _ h => h) _ le_rfl
  intro v hv
  rw [hv]
  exact updated st e queue native storage

end
end IntegerMultBounds.Machine.CompactComplexControllerExponent
