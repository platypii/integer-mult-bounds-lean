import IntegerMultBounds.Machine.ActivePrefixStageRuntimeEndpoint
import IntegerMultBounds.Machine.ActivePrefixStageSingletonSelected

/-! The single runtime stage has an exact entrywise selected-address endpoint
for every positive width, including the physically highest-only singleton. -/
namespace IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageFullData (Inputs)
open ActivePrefixStageFullSelected (geometry Address)
open ActivePrefixStageRuntimeData
open ActivePrefixStageParameters ActivePrefixStageGeometry
open ActiveRepairLayoutRecordsData (Array)
open ActivePrefixDirtyControlGlobalSwap (index)
open ActiveRepairLayoutPermutationFiber (controlWord sourceWord)
open ActiveTargetHighestLayoutWords
open ActiveTargetHighestLayoutCompose (targetWord)
variable {s : Shape}

def singletonEarly (d : ActivePrefixStageSingletonData.Inputs s)
    (h : d.stage.source.val<d.stage.target.val) (i : Address d.toInputs) : Address d.toInputs :=
  ActivePrefixStageSingletonSelected.earlyDestination d h i

def singletonLate (d : ActivePrefixStageSingletonData.Inputs s)
    (h : d.stage.target.val<d.stage.source.val) (i : Address d.toInputs) : Address d.toInputs :=
  ActivePrefixStageSingletonSelected.lateDestination d h i

def singletonDestination (d : ActivePrefixStageSingletonData.Inputs s) (i : Address d.toInputs) : Address d.toInputs :=
  if h : d.stage.source.val<d.stage.target.val then singletonEarly d h i
  else singletonLate d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) i

def destination (d : Inputs s) (i : Address d) : Address d :=
  if h : 1<d.stage.f then ActivePrefixStageDispatchSelected.destination d i
  else singletonDestination (singleton d h) i

theorem singleton_entry (d : ActivePrefixStageSingletonData.Inputs s) (x : Array s d.rows) (i : Address d.toInputs) :
    ActivePrefixStageSingletonDispatch.result d x (index s (geometry d.toInputs) (singletonDestination d i))=
      x (index s (geometry d.toInputs) i) := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [ActivePrefixStageSingletonDispatch.result,singletonDestination,dite_eq_left h]
    exact ActivePrefixStageSingletonSelected.early_entry d h x i
  · simp only [ActivePrefixStageSingletonDispatch.result,singletonDestination,dite_eq_right h]
    exact ActivePrefixStageSingletonSelected.late_entry d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) x i

theorem entry (d : Inputs s) (x : Array s d.rows) (i : Address d) :
    result d x (index s (geometry d) (destination d i))=x (index s (geometry d) i) := by
  by_cases h : 1<d.stage.f
  · simp only [result,destination,dite_eq_left h]
    exact ActivePrefixStageDispatchSelected.entry d x i
  · simp only [result,destination,dite_eq_right h]
    exact singleton_entry (singleton d h) x i

def lowControl (d : Inputs s) (i : Address d) :=
  if d.stage.source.val<d.stage.target.val then
    controlWord (geometry d).before (geometry d).after (geometry d).q (geometry d).rho (geometry d).n
      (earlyOffset d.stage) ((geometry d).f*(geometry d).q) .before (i.activeBefore,i.activeAfter)
  else controlWord (geometry d).before (geometry d).after (geometry d).q (geometry d).rho (geometry d).n
      (lateOffset d.stage) ((geometry d).f*(geometry d).q) .after (i.activeBefore,i.activeAfter)

def highControl (d : Inputs s) (i : Address d) :=
  if d.stage.source.val<d.stage.target.val then earlyControl s (geometry d) (earlyOffset d.stage) d.rows i
  else lateControl s (geometry d) (lateOffset d.stage) d.rows i

def source (d : Inputs s) (i : Address d) :=
  if d.stage.source.val<d.stage.target.val then
    sourceWord (geometry d).before (geometry d).after (earlyOffset d.stage) ((geometry d).f*(geometry d).q)
      .before (i.activeBefore,i.activeAfter)
  else sourceWord (geometry d).before (geometry d).after (lateOffset d.stage) ((geometry d).f*(geometry d).q)
      .after (i.activeBefore,i.activeAfter)

/-- The control mask is exactly the original full source-slot selection. -/
theorem selected (d : Inputs s) (i : Address d) :
    SelectedSourceBitsData.selected (source d i) s.chunk d.stage.rho d.stage.f=
      lowControl d i++[highControl d i] := by
  have hf : d.stage.f=(geometry d).n+1 := by have := d.stage.positiveWidth; change d.stage.f=d.stage.f-1+1; omega
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [source,lowControl,highControl,ite_eq_left h]
    rw [hf]
    exact ActiveTargetHighestLayoutWords.early_selected s (geometry d) (earlyOffset d.stage) d.rows i
  · simp only [source,lowControl,highControl,ite_eq_right h]
    rw [hf]
    exact ActiveTargetHighestLayoutWords.late_selected s (geometry d) (lateOffset d.stage) d.rows i

theorem singleton_low (d : ActivePrefixStageSingletonData.Inputs s) (i : Address d.toInputs) :
    lowControl d.toInputs i=[] := by
  have hn : (geometry d.toInputs).n=0 := ActivePrefixStageSingletonData.zero_low d
  unfold lowControl
  split_ifs <;> simp only [controlWord,hn,SelectedSourceBitsData.selected_zero]

theorem packed_target_word (d : Inputs s) (i : Address d) (lo : List Bool) :
    targetWord s (geometry d) d.rows lo (ActivePrefixStageDispatchSelected.destination d i)=
      List.zipWith xor (targetWord s (geometry d) d.rows lo i)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask s.chunk (lowControl d i)++
          (highControl d i::List.replicate ((geometry d).before-1) false)) := by
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_left h,lowControl,highControl,ite_eq_left h]
    exact ActiveTargetHighestLayoutFullSelected.early_target_word s (geometry d) (earlyOffset d.stage) d.rows
      (early_fits d.stage h) (early_high_positive d.stage h) i lo
  · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_right h,lowControl,highControl,ite_eq_right h]
    exact ActiveTargetHighestLayoutFullSelected.late_target_word s (geometry d) (lateOffset d.stage) d.rows
      (late_fits d.stage (ActivePrefixStageOrderCompare.late_of_not_early d.stage h)) (positive_before d.stage) i lo

theorem singleton_target_word (d : ActivePrefixStageSingletonData.Inputs s) (i : Address d.toInputs) (lo : List Bool) :
    targetWord s (geometry d.toInputs) d.rows lo (singletonDestination d i)=
      List.zipWith xor (targetWord s (geometry d.toInputs) d.rows lo i)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask s.chunk (lowControl d.toInputs i)++
          (highControl d.toInputs i::List.replicate ((geometry d.toInputs).before-1) false)) := by
  rw [singleton_low]
  simp only [Compact.PowerTwo.toggleMask,List.map_nil,List.flatten_nil,List.append_nil]
  by_cases h : d.stage.source.val<d.stage.target.val
  · simp only [singletonDestination,dite_eq_left h,highControl,ite_eq_left h]
    exact ActivePrefixStageSingletonSelected.early_target_word d h i lo
  · simp only [singletonDestination,dite_eq_right h,highControl,ite_eq_right h]
    exact ActivePrefixStageSingletonSelected.late_target_word d (ActivePrefixStageOrderCompare.late_of_not_early d.stage h) i lo

/-- Exact selected XOR on the entire target word, including unselected bits. -/
theorem target_word (d : Inputs s) (i : Address d) (lo : List Bool) :
    targetWord s (geometry d) d.rows lo (destination d i)=
      List.zipWith xor (targetWord s (geometry d) d.rows lo i)
        (List.replicate lo.length false++Compact.PowerTwo.toggleMask s.chunk (lowControl d i)++
          (highControl d i::List.replicate ((geometry d).before-1) false)) := by
  by_cases h : 1<d.stage.f
  · rw [destination,dite_eq_left h]
    exact packed_target_word d i lo
  · rw [destination,dite_eq_right h]
    exact singleton_target_word (singleton d h) i lo

/-- All compact fields, row and payload positions are retained; only target
and its highest active bit may change. -/
theorem fields (d : Inputs s) (i : Address d) :
    destination d i={i with target:=(destination d i).target,activeBefore:=(destination d i).activeBefore} := by
  by_cases hw : 1<d.stage.f
  · simp only [destination,dite_eq_left hw]
    by_cases ho : d.stage.source.val<d.stage.target.val
    · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_left ho]
      have h := ActiveTargetHighestLayoutFullSelected.early_fields s (geometry d) (earlyOffset d.stage) d.rows
        (early_fits d.stage ho) (early_high_positive d.stage ho) i
      rw [ActivePrefixStageFullSelected.earlyDestination,h]
    · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_right ho]
      have h := ActiveTargetHighestLayoutFullSelected.late_fields s (geometry d) (lateOffset d.stage) d.rows
        (late_fits d.stage (ActivePrefixStageOrderCompare.late_of_not_early d.stage ho)) (positive_before d.stage) i
      rw [ActivePrefixStageFullSelected.lateDestination,h]
  · simp only [destination,dite_eq_right hw]
    by_cases ho : d.stage.source.val<d.stage.target.val
    · simp only [singletonDestination,dite_eq_left ho]
      rfl
    · simp only [singletonDestination,dite_eq_right ho]
      rfl

/-- The entire original source slot survives the selected XOR. -/
theorem source_preserved (d : Inputs s) (i : Address d) : source d (destination d i)=source d i := by
  by_cases hw : 1<d.stage.f
  · simp only [destination,dite_eq_left hw]
    by_cases ho : d.stage.source.val<d.stage.target.val
    · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_left ho,source,ite_eq_left ho,sourceWord]
      exact ActivePrefixStageFullSelected.early_source d ho i
    · simp only [ActivePrefixStageDispatchSelected.destination,dite_eq_right ho,source,ite_eq_right ho,sourceWord]
      rw [ActivePrefixStageFullSelected.late_source]
  · simp only [destination,dite_eq_right hw]
    by_cases ho : d.stage.source.val<d.stage.target.val
    · simp only [singletonDestination,dite_eq_left ho,source,ite_eq_left ho,sourceWord]
      exact ActivePrefixStageSingletonSelected.early_source (singleton d hw) ho i
    · simp only [singletonDestination,dite_eq_right ho,source,ite_eq_right ho,sourceWord]
      rfl

end
end IntegerMultBounds.Machine.ActivePrefixStageRuntimeSelected
