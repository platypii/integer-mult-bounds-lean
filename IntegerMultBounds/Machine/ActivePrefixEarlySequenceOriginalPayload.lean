import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalInputs

/-! The actual four-load machine selects its twenty-eight inputs from the
physically constructed forty-three-tape caller. The unused duplicate row word
and all original (layout d) words are framed. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPayload
noncomputable section
open ActivePrefixEarlySequenceOriginalData ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixEarlySequenceData (Array)
open ActivePrefixLayoutShapes
open CompactGadgetReservationShape (Shape)
open Networks.Shared50ModularControl (prime)

abbrev count := ActivePrefixEarlySequenceRun.count
theorem common_le : 28≤count := by unfold count ActivePrefixEarlySequenceRun.count; omega
def ports : Fin 28 → Fin count := Fin.castLE common_le
theorem ports_injective : Function.Injective ports := Fin.castLE_injective _
def program := Placement.placed ActivePrefixEarlySequenceRun.program
  (CleanSubbank.placement ports sequenceFocus sequence_injective)

variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem runs (hfit : offset+p.f*p.q≤p.before) (d : Inputs s p offset rows) (x : Array s rows) :
    HoareTime program (fun v => v=CleanSubbank.bank (s := count) (ready d.gs d.bw d.hs x (layout d)))
      (fun v => v=CleanSubbank.bank (s := count)
        (ready d.gs d.bw d.hs (ActivePrefixEarlySequenceData.result s p offset hfit rows x) (layout d)))
      (ActivePrefixEarlySequenceRun.cost s p rows) := by
  refine CleanSubbank.realizes _ ports sequenceFocus ports_injective sequence_injective
    (ready d.gs d.bw d.hs x (layout d))
    (ready d.gs d.bw d.hs (ActivePrefixEarlySequenceData.result s p offset hfit rows x) (layout d))
    _ _ _ ?_ ?_ ?_ ?_ (sequence_frame d.gs d.bw d.hs x (layout d) _)
    (ActivePrefixEarlySequenceRun.runs (prepared hfit d) x)
  · rw [SharedBankRawCompose.payload_raw _ ports (fun _ => rfl),sequence_sources]
    rfl
  · rw [SharedBankRawCompose.payload_raw _ ports (fun _ => rfl),sequence_sources]
    rfl
  · exact SharedBankRawCompose.strip_raw _ _ (fun _ => rfl)
  · exact SharedBankRawCompose.strip_raw _ _ (fun _ => rfl)

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPayload
