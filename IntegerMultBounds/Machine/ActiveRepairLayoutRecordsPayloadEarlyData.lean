import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsOriginalEarlyAlphabet
import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPlaced
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsEarly

/-! Literal shared prime-alphabet caller for early payload then repair.
Twenty-two original words and one original raw array are the only inputs. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open Networks.Shared50ModularControl (prime)
open ActiveRepairLayoutRecordsData (Array)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def focus : Fin 23 → Fin 243 :=
  ![235,236,237,238,239,240,241,242,0,1,2,3,4,5,6,7,8,9,10,11,12,13,228]
theorem focus_injective : Function.Injective focus := by decide

def rawBank {m : ℕ} (x : Fin m → Bool) : Tapes 1 prime :=
  ⟨fun _ => 0,fun _ => ActiveTargetRotation.word x⟩
def native (d : Inputs s p offset rows) (x : Array s rows) : Tapes 235 prime :=
  (((ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d).append
    (SharedBank.empty 185 prime)).append (rawBank x)).append (SharedBank.empty 6 prime)
def controls (d : Inputs s p offset rows) : Tapes 8 prime :=
  (FixedHeaderBankCopy.headerBank d.gs).append
    (FixedHeaderBankCopy.headerBank (fun _ : Fin 1 => d.bw))
def input (d : Inputs s p offset rows) (x : Array s rows) := (native d x).append (controls d)
def repairedInput (d : Inputs s p offset rows) (x : Array s rows) :=
  (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.input d
    (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.chunks d x)).append (controls d)
def output (d : Inputs s p offset rows) (x : Array s rows) :=
  (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.output d
    (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.chunks d x)).append (controls d)

theorem sources (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (input d x) focus=
      ActivePrefixEarlySequenceOriginalPlaced.sources d.gs d.bw d.hs x := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_set (d : Inputs s p offset rows) (x y : Array s rows) :
    SharedPlacementAlphabet.setTape (input d x) 228 (ActiveTargetRotation.word y) 0=input d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem low_output (d : Inputs s p offset rows) (x : Array s rows)
    (hfit : offset+p.f*p.q≤p.before) :
    ActivePrefixEarlySequenceOriginalPlaced.result (input d x) focus
      (ActivePrefixEarlySequenceData.result s p offset hfit rows x)=repairedInput d x := by
  rw [ActivePrefixEarlySequenceOriginalPlaced.result]
  change SharedPlacementAlphabet.setTape (input d x) 228
    (ActiveTargetRotation.word (ActivePrefixEarlySequenceData.result s p offset hfit rows x)) 0=_
  rw [input_set]
  unfold input native repairedInput
  rw [ActiveRepairLayoutRecordsOriginalEarlyAlphabet.input_literal]
  apply congrArg (fun v : Tapes 1 prime =>
    ((((ActiveRepairLayoutRecordsHeadersRun.originalInput (a:=prime) d).append
      (SharedBank.empty 185 prime)).append v).append (SharedBank.empty 6 prime)).append (controls d))
  apply congrArg₂ Tapes.mk
  · rfl
  · funext i
    have h := ActiveRepairLayoutRecordsOriginalEarlyAlphabet.input_array d x
    rw [ActiveRepairLayoutRecordsOriginalEarlyAlphabet.input_literal] at h
    change (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.rawBank
      (ActiveRepairLayoutRecordsOriginalEarlyAlphabet.chunks d x)).tape i=_ at h
    rw [ActiveRepairLayoutRecordsEarly.result_move s p offset rows hfit x]
    simpa only [rawBank,ActiveRepairLayoutRecordsOriginalEarlyAlphabet.rawBank,ActiveTargetRotation.word,List.map_ofFn,Function.comp_def] using h.symm

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadEarlyData
