import IntegerMultBounds.Machine.ActivePrefixStageDispatchData

/-! Physical comparison and clean original-input branches share a separate
runtime flag; all other caller words and every private tape are framed. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageDispatchPlaced
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs original)
open ActivePrefixStageDispatchData
open ActiveRepairLayoutRecordsData (Array)
open Networks.Shared50ModularControl (prime)
variable {s : Shape}

def commonSlots : Fin 66 → Fin 67 := Fin.castAdd 1
theorem commonSlots_injective : Function.Injective commonSlots := Fin.castAdd_injective _ _

def stage {w q : ℕ} (M : Program (66+w) q prime) :=
  Placement.placed M (CleanSubbank.placement (Fin.castAdd w) commonSlots commonSlots_injective)

theorem stage_runs {w q B : ℕ} (M : Program (66+w) q prime)
    (d : Inputs s) (x y : Array s d.rows)
    (h : HoareTime M (fun v => v=CleanSubbank.bank (s:=w) (original d x))
      (fun v => v=CleanSubbank.bank (s:=w) (original d y)) B) :
    HoareTime (stage M) (fun v => v=CleanSubbank.bank (s:=66+w) (flagged d x))
      (fun v => v=CleanSubbank.bank (s:=66+w) (flagged d y)) B := by
  refine CleanSubbank.realizes M (Fin.castAdd w) commonSlots (Fin.castAdd_injective _ _) commonSlots_injective
    (flagged d x) (flagged d y) _ _ B ?_ ?_
    (CleanSubbank.strip_bank _) (CleanSubbank.strip_bank _) ?_ h
  · rw [CleanSubbank.payload_bank]
    exact (flagged_payload _ _).symm
  · rw [CleanSubbank.payload_bank]
    exact (flagged_payload _ _).symm
  · rw [←flagged_set d x y]
    exact (CompactGadgetReservationPlacement.strip_set _ commonSlots (65:Fin 66) _ _).symm

def comparator := Placement.placed (ActivePrefixStageOrderCompare.program (a:=prime))
  (CleanSubbank.placement id compareSlots compareSlots_injective)
def cleanup := Placement.placed (ActivePrefixStageOrderCompare.cleanup (a:=prime))
  (CleanSubbank.placement id compareSlots compareSlots_injective)

theorem compare_runs (d : Inputs s) (x : Array s d.rows) :
    HoareTime comparator (fun v => v=CleanSubbank.bank (s:=3) (caller d x))
      (fun v => v=CleanSubbank.bank (s:=3) (flagged d x)) (ActivePrefixStageOrderCompare.cost d.stage) := by
  refine CleanSubbank.realizes _ id compareSlots Function.injective_id compareSlots_injective
    (caller d x) (flagged d x) (ActivePrefixStageOrderCompare.input d.stage)
    (ActivePrefixStageOrderCompare.output d.stage) _ ?_ ?_
    (SharedBankFrames.strip_identity _) (SharedBankFrames.strip_identity _) ?_
    (ActivePrefixStageOrderCompare.runs d.stage)
  · exact (caller_compare d x).symm
  · exact (flagged_compare d x).symm
  · unfold flagged
    exact (CompactGadgetReservationPlacement.strip_set _ compareSlots (2:Fin 3) _ _).symm

theorem cleanup_runs (d : Inputs s) (x : Array s d.rows) :
    HoareTime cleanup (fun v => v=CleanSubbank.bank (s:=3) (flagged d x))
      (fun v => v=CleanSubbank.bank (s:=3) (caller d x)) 1 := by
  refine CleanSubbank.realizes _ id compareSlots Function.injective_id compareSlots_injective
    (flagged d x) (caller d x) (ActivePrefixStageOrderCompare.output d.stage)
    (ActivePrefixStageOrderCompare.input d.stage) _ ?_ ?_
    (SharedBankFrames.strip_identity _) (SharedBankFrames.strip_identity _) ?_
    (ActivePrefixStageOrderCompare.cleans d.stage)
  · exact (flagged_compare d x).symm
  · exact (caller_compare d x).symm
  · unfold flagged
    exact CompactGadgetReservationPlacement.strip_set _ compareSlots (2:Fin 3) _ _

end
end IntegerMultBounds.Machine.ActivePrefixStageDispatchPlaced
