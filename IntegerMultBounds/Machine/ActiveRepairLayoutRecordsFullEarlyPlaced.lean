import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlySelected
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullPlacedCommon

/-! Complete early low/high action placed on arbitrary original twenty-three
ports. Original numeric words and all unselected caller tapes are retained;
only the genuine raw array changes and every private tape is blank again. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyPlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveRepairLayoutRecordsFullEarlyRun (count)
open ActiveTargetHighestPairLayoutGeometry (sourceHigh)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {p : Parameters s} {offset rows t : ℕ}

def common (d : Inputs s p offset rows) (x : Array s rows) :=
  ActivePrefixEarlySequenceOriginalPlaced.sources d.gs d.bw d.hs x

def ports (i : Fin 23) : Fin count :=
  Fin.castLE ActiveRepairLayoutRecordsFullEarlyRun.permanent_le (ActiveRepairLayoutRecordsPayloadEarlyData.focus i)
theorem ports_injective : Function.Injective ports :=
  (Fin.castLE_injective _).comp ActiveRepairLayoutRecordsPayloadEarlyData.focus_injective

def programFor (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairLayoutRecordsFullEarlyRun.programFor m)
    (CleanSubbank.placement ports focus hf)
def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) := programFor .pure focus hf

theorem common_set (d : Inputs s p offset rows) (x y : Array s rows) :
    setTape (common d x) 22 (ActiveTargetRotation.word y) 0=common d y := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem caller_private (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.strip (ActiveRepairLayoutRecordsPayloadEarlyData.input d x)
      ActiveRepairLayoutRecordsPayloadEarlyData.focus=SharedBank.empty 243 prime := by
  apply congrArg₂ Tapes.mk <;> funext i <;> by_cases hi : ∃j,ActiveRepairLayoutRecordsPayloadEarlyData.focus j=i
  all_goals simp only [hi,ite_true,ite_false]
  all_goals fin_cases i
  all_goals first | rfl | exact (hi (by decide)).elim

theorem native_payload (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (ActiveRepairLayoutRecordsFullEarlyRun.bank d x) ports=common d x :=
  (ActiveRepairLayoutRecordsFullPlacedCommon.raw_payload
    ActiveRepairLayoutRecordsFullEarlyRun.permanent_le _ _).trans
      (ActiveRepairLayoutRecordsPayloadEarlyData.sources d x)

theorem native_clean (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.strip (ActiveRepairLayoutRecordsFullEarlyRun.bank d x) ports=SharedBank.empty count prime :=
  ActiveRepairLayoutRecordsFullPlacedCommon.raw_private
    ActiveRepairLayoutRecordsFullEarlyRun.permanent_le _ _ (caller_private d x)

theorem realizes {q budget : ℕ} (M : Program count q prime)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x y : Array s rows) (hsrc : SharedBank.payload v focus=common d x)
    (h : HoareTime M (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank d x)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank d y) budget) :
    HoareTime (Placement.placed M (CleanSubbank.placement ports focus hf))
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count)
        (setTape v (focus 22) (ActiveTargetRotation.word y) 0)) budget := by
  refine CleanSubbank.realizes M ports focus ports_injective hf v _ _ _ _ ?_ ?_
    (native_clean d x) (native_clean d y) ?_ h
  · exact (native_payload d x).trans hsrc.symm
  · rw [native_payload]
    simp only [CompactGadgetReservationPlacement.payload_set _ _ hf,hsrc,common_set]
  · simp only [CompactGadgetReservationPlacement.strip_set]

theorem runs_for (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x y : Array s rows) (B : ℕ)
    (hsrc : SharedBank.payload v focus=common d x)
    (h : HoareTime (ActiveRepairLayoutRecordsFullEarlyRun.programFor m)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank d x)
      (fun w => w=ActiveRepairLayoutRecordsFullEarlyRun.bank d y) B) :
    HoareTime (programFor m focus hf)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count)
        (setTape v (focus 22) (ActiveTargetRotation.word y) 0)) B :=
  realizes (ActiveRepairLayoutRecordsFullEarlyRun.programFor m) v focus hf d x y hsrc h

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=common d x)
    (hfit : offset+p.f*p.q≤p.before) (hsource : 0<sourceHigh s p offset) (hH : 1≤s.H)
    (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsHeadersData.repair d).geom.addressBits+1)≤D) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullEarlyData.result d hfit hsource hH x)) 0))
      (ActiveRepairLayoutRecordsFullEarlyRun.cost D s p offset rows hfit hsource hH d.hr
        (by have := d.hrecord; omega)) :=
  runs_for .pure v focus hf d x _ _ hsrc
    (ActiveRepairLayoutRecordsFullEarlyRun.runs d x hfit hsource hH hq3 hR D hdensity)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullEarlyPlaced
