import IntegerMultBounds.Machine.CompactComplexControllerChildPrefix
import IntegerMultBounds.Machine.CompactComplexChildHeaderFrames

/-! Concrete internal-child return continuation: physically erase child
headers, pop the saved parent descriptors from appended storage and increment
the retained controller exponent. The child's computed payload is retained. -/
namespace IntegerMultBounds.Machine.CompactComplexControllerChildReturn
noncomputable section
open CompactComplexControllerNativeFrame (tapes)
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open ActiveRepairRankHeadersCommands (State put)
open ActivePrefixStageHeadersData (initial)
open CompactComplexControllerChildPrefix (native data)
open SharedPlacementAlphabet (setTape)
variable {a s : ℕ}

def program (headerStack : Fin s) : Σ q, Program (tapes s) q a :=
  ⟨_,seq (seq CompactComplexControllerHeaderReturn.clearProgram
    (CompactComplexControllerHeaderStack.restoreProgram headerStack)) CompactComplexControllerExponent.ascendProgram⟩

private theorem clear_native {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ)
    (tail : Tapes 23 a) : CompactComplexControllerHeaderReturn.clear (native v rows tail)=
      (ActiveRepairRankHeadersCommands.bank (CompactComplexChildHeaderFrames.cleared (initial v rows))).append tail := by
  unfold CompactComplexControllerHeaderReturn.clear native
  change setTape (setTape (setTape ((ActiveRepairRankHeadersCommands.bank (initial v rows)).append tail)
    (Fin.castAdd 23 (Fin.castAdd 15 (7 : Fin 28))) (fun _ => blank) 0)
      (Fin.castAdd 23 (Fin.castAdd 15 (8 : Fin 28))) (fun _ => blank) 0)
        (Fin.castAdd 23 (Fin.castAdd 15 (9 : Fin 28))) (fun _ => blank) 0=_
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left]
  unfold ActiveRepairRankHeadersCommands.bank CleanSubbank.bank
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left,
    SharedPlacementAlphabet.setTape_append_left,← ActiveRepairRankHeadersCommands.erase_caller,
    ← ActiveRepairRankHeadersCommands.erase_caller,← ActiveRepairRankHeadersCommands.erase_caller]
  rfl

private theorem descriptor_tape {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ)
    (tail : Tapes 23 a) :
    ∀ i, (native v rows tail).tape (![7,8,9] i)=BinaryDescriptorStack.descriptor (data v i) := by
  intro i
  fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
    ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,
    Tapes.append,Fin.addCases,data,BinaryDescriptorStackRoundtrip.descriptor_encoded]

private theorem descriptor_head {sh : Shape} (v : ActivePrefixStageParameters.Stage sh) (rows : ℕ)
    (tail : Tapes 23 a) : ∀ i, (native v rows tail).head (![7,8,9] i)=1 := by
  intro i
  fin_cases i <;> simp [native,ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,
    ActiveRepairRankHeadersCommands.caller,initial,ActivePrefixStageHeadersData.originalValues,Tapes.append,Fin.addCases]

/-- The true child's payload result remains, while all parent descriptors,
controller exponent and descriptor-stack cells/head return exactly. -/
theorem runs {sh : Shape} (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left (k+2)) (hactive : sh.active≤sh.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (slot : Fin arity) (rows : ℕ)
    (headerStack : Fin s) (st : State) (h1 : st 1=some (k+2))
    (queue : Tapes 1 a) (tail : Tapes 23 a) (storage : Tapes s a)
    (hb : ∀ z, storage.head headerStack≤z → storage.tape headerStack z=blank) :
    HoareTime (program headerStack).2
      (fun v => v=CompactComplexControllerNativeFrame.bank
        (ActiveRepairRankHeadersCommands.bank (put st 1 (k+1))) queue
        (native (CompactComplexChildHeadersData.child rho visit hactive pair slot) rows tail)
        (CompactComplexControllerHeaderStack.saved storage headerStack
          (data (CompactComplexChildHeadersData.parent rho visit hactive pair))))
      (fun v => v=CompactComplexControllerNativeFrame.bank (ActiveRepairRankHeadersCommands.bank st) queue
        (native (CompactComplexChildHeadersData.parent rho visit hactive pair) rows tail) storage)
      (2*((data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 0).length+
        (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 1).length+
        (data (CompactComplexChildHeadersData.child rho visit hactive pair slot) 2).length)+
          CompactChildHeadersStack.cost (data (CompactComplexChildHeadersData.parent rho visit hactive pair))+
            2*(k+3)+16) := by
  let parent := CompactComplexChildHeadersData.parent rho visit hactive pair
  let child := CompactComplexChildHeadersData.child rho visit hactive pair slot
  let control := ActiveRepairRankHeadersCommands.bank (put st 1 (k+1)) (a := a)
  let saved := CompactComplexControllerHeaderStack.saved storage headerStack (data parent)
  have hc := CompactComplexControllerHeaderReturn.cleanup control queue (native child rows tail) saved (data child)
    (descriptor_tape child rows tail) (descriptor_head child rows tail)
  have hr := CompactComplexControllerHeaderReturn.restore_parent headerStack control queue (native parent rows tail)
    storage (data parent) (descriptor_tape parent rows tail) (descriptor_head parent rows tail) hb
  have hclear : CompactComplexControllerHeaderReturn.clear (native child rows tail)=
      CompactComplexControllerHeaderReturn.clear (native parent rows tail) := by
    rw [clear_native,clear_native]
    have he := CompactComplexChildHeaderFrames.cleared_initial_eq parent child rows rfl rfl rfl rfl
    rw [he]
  rw [hclear] at hc
  have ha := CompactComplexControllerExponent.ascend (put st 1 (k+1)) (k+2) (by omega)
    (by simp [put]) queue (native parent rows tail) storage
  have hs : put (put st 1 (k+1)) 1 (k+2)=st := by
    funext i
    by_cases hi : i=1
    · subst i; simp [put,h1]
    · simp [put,Function.update,hi]
  rw [hs] at ha
  have h := (hc.seq hr).seq ha
  apply h.consequence (fun _ h => h) (fun _ h => h)
  dsimp only [parent,child]
  omega

end
end IntegerMultBounds.Machine.CompactComplexControllerChildReturn
