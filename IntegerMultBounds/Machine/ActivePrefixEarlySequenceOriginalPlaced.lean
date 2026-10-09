import IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalRun

/-! The complete original-input four-load block on arbitrary caller tapes.
Only twenty-two original numeric words and the array are ports. Generated
headers, duplicate row words and all private storage start and return blank. -/
namespace IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPlaced
noncomputable section
open ActivePrefixEarlySequenceOriginalData ActivePrefixEarlySequenceOriginalInputs
open ActivePrefixEarlySequenceData (Array)
open ActivePrefixEarlySequenceOriginalRun (count)
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}


def sources {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :=
  SharedBank.payload (base gs bw hs x) (Fin.castAdd 20 : Fin 23 → Fin 43)
theorem common_le : 23≤count := by unfold count; omega
def ports : Fin 23 → Fin count := Fin.castLE common_le
theorem ports_injective : Function.Injective ports := Fin.castLE_injective _

def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed ActivePrefixEarlySequenceOriginalRun.program (CleanSubbank.placement ports focus hf)
def result {m : ℕ} (caller : Tapes t prime) (focus : Fin 23 → Fin t) (x : Fin m → Bool) :=
  setTape caller (focus 22) (ActiveTargetRotation.word x) 0

theorem base_raw {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    base gs bw hs x=SharedBankStageInput.raw (sources gs bw hs x) 43 := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem raw_twice {k n r : ℕ} (v : Tapes k prime) (hk : k≤n) :
    SharedBankStageInput.raw (SharedBankStageInput.raw v n) r=SharedBankStageInput.raw v r := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i.val<k
  all_goals by_cases hj : i.val<n
  all_goals first | (exfalso; omega) | simp [SharedBankStageInput.raw,hi,hj]

theorem native_raw {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBankStageInput.raw (base gs bw hs x) count=SharedBankStageInput.raw (sources gs bw hs x) count := by
  rw [base_raw,raw_twice _ (by decide : 23≤43)]

theorem native_payload {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBank.payload (SharedBankStageInput.raw (base gs bw hs x) count) ports=sources gs bw hs x := by
  rw [native_raw]
  exact SharedBankRawCompose.payload_raw _ ports (fun _ => rfl)

theorem native_clean {m : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool) (x : Fin m → Bool) :
    SharedBank.strip (SharedBankStageInput.raw (base gs bw hs x) count) ports=SharedBank.empty count prime := by
  rw [native_raw]
  exact SharedBankRawCompose.strip_raw _ ports (fun _ => rfl)

theorem raw_set {k n : ℕ} (hk : k≤n) (v : Tapes k prime) (i : Fin k)
    (f : ℤ → Fin (prime+4)) (pos : ℤ) :
    SharedBankStageInput.raw (setTape v i f pos) n=
      setTape (SharedBankStageInput.raw v n) (Fin.castLE hk i) f pos := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j.val<k
  all_goals by_cases he : j.val=i.val
  all_goals simp [SharedBankStageInput.raw,setTape,Function.update_apply,Fin.ext_iff,hj,he]

theorem native_output {m n : ℕ} (gs : Fin 7 → List Bool) (bw : List Bool) (hs : Fin 14 → List Bool)
    (x : Fin m → Bool) (y : Fin n → Bool) :
    SharedBankStageInput.raw (base gs bw hs y) count=setTape
      (SharedBankStageInput.raw (base gs bw hs x) count) (ports 22) (ActiveTargetRotation.word y) 0 := by
  rw [native_raw,native_raw]
  have h : sources gs bw hs y=setTape (sources gs bw hs x) 22 (ActiveTargetRotation.word y) 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [h,raw_set common_le]
  rfl

theorem runs (caller : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    {s : Shape} {p : Parameters s} {offset rows : ℕ} (hfit : offset+p.f*p.q≤p.before)
    (d : Inputs s p offset rows) (x : Array s rows)
    (hsrc : SharedBank.payload caller focus=sources d.gs d.bw d.hs x) :
    HoareTime (program focus hf) (fun v => v=CleanSubbank.bank (s := count) caller)
      (fun v => v=CleanSubbank.bank (s := count)
        (result caller focus (ActivePrefixEarlySequenceData.result s p offset hfit rows x)))
      (ActivePrefixEarlySequenceOriginalRun.cost s p rows) := by
  refine CleanSubbank.realizes _ ports focus ports_injective hf caller (result caller focus _)
    _ _ _ ?_ ?_ (native_clean d.gs d.bw d.hs x) (native_clean d.gs d.bw d.hs _) ?_
    (ActivePrefixEarlySequenceOriginalRun.runs hfit d x)
  · rw [native_payload,hsrc]
  · rw [native_output d.gs d.bw d.hs x]
    simp only [result,CompactGadgetReservationPlacement.payload_set _ _ ports_injective,
      CompactGadgetReservationPlacement.payload_set _ _ hf,native_payload,hsrc]
  · simp only [result,CompactGadgetReservationPlacement.strip_set]

theorem frame {m : ℕ} (caller : Tapes t prime) (focus : Fin 23 → Fin t) (x : Fin m → Bool)
    (i : Fin t) (hi : i≠focus 22) :
    (result caller focus x).head i=caller.head i ∧ (result caller focus x).tape i=caller.tape i := by
  simp [result,setTape,hi]

end
end IntegerMultBounds.Machine.ActivePrefixEarlySequenceOriginalPlaced
