import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsPayloadLateBudget
import IntegerMultBounds.Machine.ActiveTargetHighestLayoutOriginalGlobal

/-! Original-input common caller for the complete later low/high action.
The highest stage shares the genuine raw array and all fourteen original
layout words; no highest geometry or derived descriptor is an input. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateData
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open Networks.Shared50ModularControl (prime)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

def focus : Fin 15 → Fin 252 := ![0,1,2,3,4,5,6,7,8,9,10,11,12,13,237]
theorem focus_injective : Function.Injective focus := by decide

theorem sources (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (ActiveRepairLayoutRecordsPayloadLateData.caller d x) focus=
      ActiveTargetHighestLayoutOriginalPlaced.sources d.hs x := by
  unfold ActiveRepairLayoutRecordsPayloadLateData.caller
  rw [ActiveRepairLayoutRecordsOriginalLateAlphabet.input_literal]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem input_set (d : Inputs s p offset rows) (x y : Array s rows) :
    SharedPlacementAlphabet.setTape (ActiveRepairLayoutRecordsPayloadLateData.caller d x)
      (focus 14) (ActiveTargetRotation.word y) 0=ActiveRepairLayoutRecordsPayloadLateData.caller d y :=
  ActiveRepairLayoutRecordsPayloadLateData.caller_set d x y

def result (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (x : Array s rows) :=
  ActiveTargetHighestLayoutGlobal.lateAction s p offset rows hfit hbefore hH d.hr (by have := d.hrecord; omega)
    (ActiveRepairLayoutRecordsPayloadLateData.ideal d x)

def destination (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (x : Address s p rows) :=
  ActiveTargetHighestLayoutLateCoordinates.destination s p offset rows hfit hbefore
    (ActiveRepairLayoutPermutation.lateIdeal s p.q p.b p.n p.before p.after rows p.rho offset
      (p.f*p.q) .after (ActiveRepairLayoutKeysLate.positive (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d)) x)

theorem entry (d : Inputs s p offset rows) (hfit : offset+p.f*p.q≤p.after)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (array : Array s rows) (x : Address s p rows) :
    result d hfit hbefore hH array
      (ActivePrefixDirtyControlGlobalSwap.index s p (destination d hfit hbefore x))=
      array (ActivePrefixDirtyControlGlobalSwap.index s p x) := by
  unfold result destination
  rw [ActiveTargetHighestLayoutGlobal.late_entry]
  exact ActiveRepairLayoutRecordsMove.move_entry s (p.n*p.b) (p.n*p.q) p.before p.after rows
    p.compactFits p.activeSize _ array x


theorem raw_payload {n : ℕ} (hn : 252≤n) (v : Tapes 252 prime) :
    SharedBank.payload (SharedBankStageInput.raw v n)
      (fun i => Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus i))=
        SharedBank.payload v ActiveRepairLayoutRecordsPayloadLateData.focus := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals simp [SharedBankStageInput.raw,(ActiveRepairLayoutRecordsPayloadLateData.focus i).isLt]

theorem raw_private {n : ℕ} (hn : 252≤n) (v : Tapes 252 prime)
    (hclean : SharedBank.strip v ActiveRepairLayoutRecordsPayloadLateData.focus=SharedBank.empty 252 prime) :
    SharedBank.strip (SharedBankStageInput.raw v n)
      (fun i => Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus i))=SharedBank.empty n prime := by
  have hh (i : Fin n) :
      (SharedBank.strip (SharedBankStageInput.raw v n)
        (fun j => Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus j))).head i=0 ∧
      (SharedBank.strip (SharedBankStageInput.raw v n)
        (fun j => Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus j))).tape i=(fun _ => blank) := by
    by_cases h252 : i.val<252
    · have he : (∃j,Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus j)=i) ↔
          ∃j,ActiveRepairLayoutRecordsPayloadLateData.focus j=⟨i.val,h252⟩ := by
        constructor
        · rintro ⟨j,hj⟩; exact ⟨j,Fin.ext (congrArg (fun z : Fin n => z.val) hj)⟩
        · rintro ⟨j,hj⟩; exact ⟨j,Fin.ext (congrArg (fun z : Fin 252 => z.val) hj)⟩
      have hhead := congrFun (congrArg Tapes.head hclean) ⟨i.val,h252⟩
      have htape := congrFun (congrArg Tapes.tape hclean) ⟨i.val,h252⟩
      exact ⟨by simpa [SharedBank.strip,SharedBankStageInput.raw,h252,he,SharedBank.empty] using hhead,
        by simpa [SharedBank.strip,SharedBankStageInput.raw,h252,he,SharedBank.empty] using htape⟩
    · have hi : ¬∃j,Fin.castLE hn (ActiveRepairLayoutRecordsPayloadLateData.focus j)=i := by
        rintro ⟨j,hj⟩
        have hx := congrArg Fin.val hj
        exact h252 (hx ▸ (ActiveRepairLayoutRecordsPayloadLateData.focus j).isLt)
      simp [SharedBank.strip,SharedBankStageInput.raw,h252,hi]
  apply congrArg₂ Tapes.mk
  · funext i; exact (hh i).1
  · funext i; exact (hh i).2

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateData
