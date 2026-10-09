import IntegerMultBounds.Machine.ActivePrefixControlOffsetRun
import IntegerMultBounds.Machine.ActivePrefixOffsetStreamsCleanup
import IntegerMultBounds.Machine.ActivePrefixOffsetHeadersCleanup

/-! Generated source/temp/control streams and all five derived descriptors
are actually erased. Only the original eight words and generated offsets
remain, with every head restored and shared workspace blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixControlOffsetCleanup
noncomputable section
open ActivePrefixControlOffsetBank
open ActivePrefixControlOffsetRun (bank)
open SharedPlacementAlphabet (setTape)
variable {a : ℕ}

def focus : Fin 4 → Fin 17 := ![13,14,15,16]
theorem focus_injective : Function.Injective focus := by decide
def streamProgram := extend (ActivePrefixOffsetStreamsCleanup.program (a := a) focus (by decide)) 24
def headerProgram := extend (ActivePrefixOffsetHeadersCleanup.program (a := a)
  (ActivePrefixOffsetHeadersData.outputFocus headerFocus)) 24
def streamResult (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetStreamsCleanup.result (gathered (a := a) s hs) focus (offsetWord s)
def result (s : Shape) (hs : Fin 8 → List Bool) :=
  ActivePrefixOffsetHeadersCleanup.cleared (streamResult (a := a) s hs)
    (ActivePrefixOffsetHeadersData.outputFocus headerFocus)

def streamCost (s : Shape) := (tempWord s).length+(controlWord s).length+
  2*(sourceWord s).length+(offsetWord s).length+12
def cost (s : Shape) := streamCost s+1+ActivePrefixOffsetHeadersCleanup.cost
  (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)
def program := seq (streamProgram (a := a)) headerProgram

theorem stream_conditions (s : Shape) (hs : Fin 8 → List Bool) :
    (gathered (a := a) s hs).tape (focus 0)=ActivePrefixOffsetStreamsCleanup.word (tempWord s) ∧
    (gathered (a := a) s hs).tape (focus 1)=ActivePrefixOffsetStreamsCleanup.word (sourceWord s) ∧
    (gathered (a := a) s hs).tape (focus 2)=ActivePrefixOffsetStreamsCleanup.word (controlWord s) ∧
    (gathered (a := a) s hs).tape (focus 3)=ActivePrefixOffsetStreamsCleanup.word (offsetWord s) ∧
    (gathered (a := a) s hs).head (focus 0)=(tempWord s).length ∧
    (gathered (a := a) s hs).head (focus 1)=0 ∧
    (gathered (a := a) s hs).head (focus 2)=(controlWord s).length ∧
    (gathered (a := a) s hs).head (focus 3)=(offsetWord s).length := by
  rw [gathered_eq]
  refine ⟨rfl,rfl,rfl,rfl,?_,rfl,?_,?_⟩
  · change (0 : ℤ)+(controlWord s).length=(tempWord s).length
    simp only [controlWord,tempWord,SelectedSourceBitsStreamData.selected_length,BinaryPrefixFieldTableData.word_length]
    push_cast
    ring
  · change (0 : ℤ)+(controlWord s).length=(controlWord s).length
    omega
  · change (0 : ℤ)+(controlWord s).length*s.q=(offsetWord s).length
    simp only [controlWord,offsetWord,SelectedSourceBitsStreamData.selected_length,ActivePrefixControlOffsetData.offsets_length]
    push_cast
    ring

theorem stream_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (streamProgram (a := a)) (fun v => v=bank (gathered s hs))
      (fun v => v=bank (streamResult s hs)) (streamCost s) := by
  obtain ⟨hT,hX,hZ,hO,pT,pX,pZ,pO⟩ := stream_conditions (a := a) s hs
  exact hoare_extend_eq (ActivePrefixOffsetStreamsCleanup.runs (gathered s hs) focus focus_injective (by decide)
    (tempWord s) (sourceWord s) (controlWord s) (offsetWord s) hT hX hZ hO pT pX pZ pO)
    (SharedBank.empty 24 a)

theorem retained_headers (s : Shape) (hs : Fin 8 → List Bool) :
    (∀ i, (streamResult (a := a) s hs).tape (ActivePrefixOffsetHeadersData.outputFocus headerFocus i)=
      RadixZeroFill.encodedBinary (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f i)) ∧
    (∀ i, (streamResult (a := a) s hs).head (ActivePrefixOffsetHeadersData.outputFocus headerFocus i)=1) := by
  unfold streamResult
  rw [gathered_eq]
  constructor <;> intro i <;> fin_cases i <;> rfl

theorem header_runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (headerProgram (a := a)) (fun v => v=bank (streamResult s hs))
      (fun v => v=bank (result s hs)) (ActivePrefixOffsetHeadersCleanup.cost
        (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)) := by
  exact hoare_extend_eq (ActivePrefixOffsetHeadersCleanup.cleans (streamResult s hs)
    (ActivePrefixOffsetHeadersData.outputFocus headerFocus)
    (ActivePrefixOffsetHeadersData.output_injective headerFocus header_injective)
    (ActivePrefixOffsetHeadersData.words s.W s.q s.b s.n s.f)
    (retained_headers s hs).1 (retained_headers s hs).2) (SharedBank.empty 24 a)

theorem runs (s : Shape) (hs : Fin 8 → List Bool) :
    HoareTime (program (a := a)) (fun v => v=bank (gathered s hs))
      (fun v => v=bank (result s hs)) (cost s) :=
  (stream_runs s hs).seq (header_runs s hs)

theorem result_eq (s : Shape) (hs : Fin 8 → List Bool) :
    result (a := a) s hs=setTape (base hs) 16 (ActivePrefixOffsetStreamsCleanup.word (offsetWord s)) 0 := by
  unfold result streamResult
  rw [gathered_eq]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

end
end IntegerMultBounds.Machine.ActivePrefixControlOffsetCleanup
