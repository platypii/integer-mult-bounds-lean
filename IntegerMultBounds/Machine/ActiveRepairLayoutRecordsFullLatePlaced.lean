import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLateSelected
import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullPlacedCommon

/-! Complete later low/high action placed on arbitrary original twenty-three
ports. Original numeric words and all unselected caller tapes are retained;
only the genuine raw array changes and every private tape is blank again. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLatePlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsData (Array)
open ActiveRepairLayoutRecordsFullLateRun (count)
open ActivePrefixDirtyControlConjugationData (Kind)
open Networks.Shared50ModularControl (prime)
open SharedPlacementAlphabet (setTape)
variable {s : Shape} {p : Parameters s} {offset rows t : ℕ}

def common (d : Inputs s p offset rows) (x : Array s rows) :=
  ActiveRepairLayoutRecordsPayloadLatePlaced.common d x

abbrev ports := ActiveRepairLayoutRecordsFullLateRun.slots
theorem ports_injective : Function.Injective ports := ActiveRepairLayoutRecordsFullLateRun.slots_injective

def programFor (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  Placement.placed (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e m)
    (CleanSubbank.placement ports focus hf)
def program (focus : Fin 23 → Fin t) (hf : Function.Injective focus) :=
  programFor .tPure .tNegative .uPure .uNegative .pure focus hf

theorem common_set (d : Inputs s p offset rows) (x y : Array s rows) :
    setTape (common d x) 22 (ActiveTargetRotation.word y) 0=common d y :=
  ActiveRepairLayoutRecordsPayloadLatePlaced.common_set d x y

theorem native_payload (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.payload (ActiveRepairLayoutRecordsFullLateRun.bank d x) ports=common d x :=
  ActiveRepairLayoutRecordsFullLateRun.bank_payload d x

theorem native_clean (d : Inputs s p offset rows) (x : Array s rows) :
    SharedBank.strip (ActiveRepairLayoutRecordsFullLateRun.bank d x) ports=SharedBank.empty count prime :=
  ActiveRepairLayoutRecordsFullLateRun.all_private_blank d x

theorem realizes {q budget : ℕ} (M : Program count q prime)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x y : Array s rows) (hsrc : SharedBank.payload v focus=common d x)
    (h : HoareTime M (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank d x)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank d y) budget) :
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

theorem placed_runs (a b c e : Kind) (m : ActivePrefixDirtyControlLoadProducer.Mode)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (d : Inputs s p offset rows) (x y : Array s rows) (B : ℕ)
    (hsrc : SharedBank.payload v focus=common d x)
    (h : HoareTime (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e m)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank d x)
      (fun w => w=ActiveRepairLayoutRecordsFullLateRun.bank d y) B) :
    HoareTime (programFor a b c e m focus hf)
      (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count)
        (setTape v (focus 22) (ActiveTargetRotation.word y) 0)) B :=
  realizes (ActiveRepairLayoutRecordsFullLateRun.programFor a b c e m) v focus hf d x y hsrc h

theorem runs_for (a b c e : Kind) (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=common d x)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hactual : ActivePrefixDirtyControlSequenceRun.laterFor a b c e
      (ActivePrefixDirtyControlSequenceOriginalInputs.geometry hfit hn hb d) x=
        ActiveRepairLayoutRecordsPayloadLateData.actual d x)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (programFor a b c e .pure focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x)) 0))
      (ActiveRepairLayoutRecordsFullLateRun.costFor a b c e D hfit hn hb d hbefore hH) :=
  placed_runs a b c e .pure v focus hf d x _ _ hsrc
    (ActiveRepairLayoutRecordsFullLateRun.runs_for a b c e d x hfit hn hb hactual hbefore hH hq3 hR D hdensity)

theorem runs (d : Inputs s p offset rows) (x : Array s rows)
    (v : Tapes t prime) (focus : Fin 23 → Fin t) (hf : Function.Injective focus)
    (hsrc : SharedBank.payload v focus=common d x)
    (hfit : offset+p.f*p.q≤p.after) (hn : 0<p.n) (hb : 2≤p.b)
    (hbefore : 1≤p.before) (hH : 1≤s.H) (hq3 : p.b+3≤p.q)
    (hR : (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload) (D : ℕ)
    (hdensity : VaryingControlRepairDensity.lateDensity p.q p.b p.n*
      ((ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1)≤D) :
    HoareTime (program focus hf) (fun w => w=CleanSubbank.bank (s:=count) v)
      (fun w => w=CleanSubbank.bank (s:=count) (setTape v (focus 22)
        (ActiveTargetRotation.word (ActiveRepairLayoutRecordsFullLateData.result d hfit hbefore hH x)) 0))
      (ActiveRepairLayoutRecordsFullLateRun.cost D hfit hn hb d hbefore hH) :=
  runs_for .tPure .tNegative .uPure .uNegative d x v focus hf hsrc hfit hn hb
    (ActiveRepairLayoutRecordsPayloadLateRun.actual_result hfit hn hb d x)
    hbefore hH hq3 hR D hdensity

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsFullLatePlaced
