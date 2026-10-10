import IntegerMultBounds.Machine.CompactComplexParentLiveStack
import IntegerMultBounds.Machine.CompactComplexChildAlignmentBudget

/-! Actual parent-event live save and normalized-child denominator handoff have
uniform native/fallback-volume costs. The two literal descriptor lengths are
bounded by their genuine parent/child dependency Paths and true live ledgers;
no independent header allowance or desired aggregate runtime is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexParentLiveStackBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexChildAlignmentBudget (Progress)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

/-- The saved parent word and actual normalized child target each fit the
native volume, using separate real dependency Paths and true live ledgers. -/
theorem parent_child_volume (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows) :
    before≤volume rows sh ell metadataP ∧ target≤volume rows sh ell metadataP := by
  have hp := CompactComplexDenominatorCapacity.target_volume progress.parentPath
    progress.R progress.baseline (metadataP-2*sh.bits) progress.parentUsed before before rows ell
    progress.base progress.parentUsed_le progress.room progress.before_live (Nat.le_add_right _ _) hr
  have hc := CompactComplexDenominatorCapacity.target_volume progress.childPath
    progress.R progress.baseline (metadataP-2*sh.bits) progress.childUsed completed target rows ell
    progress.base progress.childUsed_le progress.room progress.completed_live
    (progress.contract.trans (Nat.le_add_right _ _)) hr
  have hv := CompactComplexSpectatorVolumeHeaders.volume_semantic sh 1 rows ell metadataP false progress.metadata
  change streamVolume sh 1 rows ell metadataP false=ButterflySpectatorGeometry.Size rows sh.bits (2^ell)*
    (2*(CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)+2)) at hv
  rw [←hv] at hp hc
  constructor
  all_goals
    first
    | simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
        volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
        CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using hp
    | simpa only [streamVolume,CompactComplexSpectatorVolumeHeaders.roleRows,Bool.false_eq_true,ite_false,
        volume,CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner,
        CompactNativeRoleHeaders.recordWidth,Nat.mul_assoc] using hc

def saveConstant : ℕ := 11
def restoreConstant : ℕ := 30
def lifecycleConstant : ℕ := 42

/-- Both concrete binary word lengths follow from actual denominator values,
which were just derived from the Paths, not from a supplied size certificate. -/
theorem header_lengths (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows) :
    (bits before).length≤volume rows sh ell metadataP+1 ∧
    (bits target).length≤volume rows sh ell metadataP+1 := by
  have h := parent_child_volume sh rows ell metadataP before completed target progress hr
  exact ⟨(ActiveRepairRankHeadersCommands.bits_length before).trans (Nat.add_le_add_right h.1 1),
    (ActiveRepairRankHeadersCommands.bits_length target).trans (Nat.add_le_add_right h.2 1)⟩

theorem save_cost_linear (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows) :
    2*(bits before).length+7≤saveConstant*volume rows sh ell metadataP := by
  have h := (header_lengths sh rows ell metadataP before completed target progress hr).1
  have hv : 0<volume rows sh ell metadataP := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos _ _ _)
  unfold saveConstant
  omega

theorem restore_cost_linear (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows) :
    4*(bits target).length+2*(bits before).length+18≤restoreConstant*volume rows sh ell metadataP := by
  have h := header_lengths sh rows ell metadataP before completed target progress hr
  have hv : 0<volume rows sh ell metadataP := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos _ _ _)
  unfold restoreConstant
  omega

/-- Charge the actual two programmes and their one connecting join. This is
local descriptor traffic only; child execution remains its separate real cost. -/
theorem lifecycle_cost_linear (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows) :
    (2*(bits before).length+7)+1+(4*(bits target).length+2*(bits before).length+18)≤
      lifecycleConstant*volume rows sh ell metadataP := by
  have h := header_lengths sh rows ell metadataP before completed target progress hr
  have hv : 0<volume rows sh ell metadataP := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos _ _ _)
  unfold lifecycleConstant
  omega

/-- Bound attached directly to the actual physical inherited-live push. -/
theorem save_linear (j : Fin s) (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows)
    (v : Tapes (CompactComplexParentLiveStack.tapes s c) 2)
    (ht : v.tape CompactComplexParentLiveStack.current=BinaryDescriptorStack.descriptor (bits before))
    (hh : v.head CompactComplexParentLiveStack.current=1) :
    HoareTime (CompactComplexParentLiveStack.saveProgram j) (fun z => z=v)
      (fun z => z=CompactComplexParentLiveStack.saved j v before)
      (saveConstant*volume rows sh ell metadataP) :=
  (CompactComplexParentLiveStack.save j v before ht hh).consequence (fun _ h => h) (fun _ h => h)
    (save_cost_linear sh rows ell metadataP before completed target progress hr)

/-- Bound attached to the real child-target copy, old-live restoration and
full cleanup, with the stored parent word supplied by the genuine saved frame. -/
theorem restore_after_child_linear (j : Fin s) (sh : Shape) (rows ell metadataP before completed target : ℕ)
    (progress : Progress sh metadataP before completed target) (hr : 0<rows)
    (v u : Tapes (CompactComplexParentLiveStack.tapes s c) 2)
    (hstack : u.tape (CompactComplexParentLiveStack.liveStack j)=
      (CompactComplexParentLiveStack.saved j v before).tape (CompactComplexParentLiveStack.liveStack j))
    (hstackHead : u.head (CompactComplexParentLiveStack.liveStack j)=
      (CompactComplexParentLiveStack.saved j v before).head (CompactComplexParentLiveStack.liveStack j))
    (hcurrent : u.tape CompactComplexParentLiveStack.current=BinaryDescriptorStack.descriptor (bits target))
    (hcurrentHead : u.head CompactComplexParentLiveStack.current=1)
    (htarget : u.tape CompactComplexParentLiveStack.target=(fun _ => blank))
    (htargetHead : u.head CompactComplexParentLiveStack.target=0)
    (hfree : ∀ z,v.head (CompactComplexParentLiveStack.liveStack j)≤z →
      z<v.head (CompactComplexParentLiveStack.liveStack j)+1+(bits before).length →
      v.tape (CompactComplexParentLiveStack.liveStack j) z=blank) :
    HoareTime (CompactComplexParentLiveStack.restoreWithTargetProgram j) (fun z => z=u)
      (fun z => z=CompactComplexParentLiveStack.restoredWithTarget j u
        (v.tape (CompactComplexParentLiveStack.liveStack j)) (v.head (CompactComplexParentLiveStack.liveStack j)) before target)
      (restoreConstant*volume rows sh ell metadataP) :=
  (CompactComplexParentLiveStack.restore_after_child j v u before target hstack hstackHead hcurrent hcurrentHead
    htarget htargetHead hfree).consequence (fun _ h => h) (fun _ h => h)
    (restore_cost_linear sh rows ell metadataP before completed target progress hr)

/-- Actual padded descendants cost at most twice the original fallback stream;
all three literal parent-live stack cost expressions inherit that same bound. -/
theorem costs_original (c m d D G K0 ell q level before completed target : ℕ)
    (progress : Progress (CompactReservationNativeRows.shape c m d D G K0)
      (CompactNativeRoleReservedBridge.precision c m d D K0 q) before completed target)
    (hc : 0<c) (hK : 0<K0) (hlevel : level≤CompactGlobalRowPadding.depth m d)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D) :
    2*(bits before).length+7≤(2*saveConstant)*CompactFallbackAxisRun.volume D K0 ell q ∧
    4*(bits target).length+2*(bits before).length+18≤(2*restoreConstant)*CompactFallbackAxisRun.volume D K0 ell q ∧
    (2*(bits before).length+7)+1+(4*(bits target).length+2*(bits before).length+18)≤
      (2*lifecycleConstant)*CompactFallbackAxisRun.volume D K0 ell q := by
  have hr := CompactGlobalRowPadding.rowsAt_positive c m d K0 level hc hK hlevel
  have hv := CompactComplexControllerExactReturnBudget.original_volume c m d D G K0 ell q level hc hK hD
  have h0 := save_cost_linear _ _ ell _ before completed target progress hr
  have h1 := restore_cost_linear _ _ ell _ before completed target progress hr
  have h2 := lifecycle_cost_linear _ _ ell _ before completed target progress hr
  have h0' := h0.trans (Nat.mul_le_mul_left saveConstant hv)
  have h1' := h1.trans (Nat.mul_le_mul_left restoreConstant hv)
  have h2' := h2.trans (Nat.mul_le_mul_left lifecycleConstant hv)
  simpa only [Nat.mul_left_comm,Nat.mul_assoc] using And.intro h0' (And.intro h1' h2')

/-- The true original input geometry pays the actual parent-live push in
unpadded fallback volume, with no externally proposed time allowance. -/
theorem save_original (j : Fin s) (c m d D G K0 ell q level before completed target : ℕ)
    (progress : Progress (CompactReservationNativeRows.shape c m d D G K0)
      (CompactNativeRoleReservedBridge.precision c m d D K0 q) before completed target)
    (hc : 0<c) (hK : 0<K0) (hlevel : level≤CompactGlobalRowPadding.depth m d)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (v : Tapes (CompactComplexParentLiveStack.tapes s c) 2)
    (ht : v.tape CompactComplexParentLiveStack.current=BinaryDescriptorStack.descriptor (bits before))
    (hh : v.head CompactComplexParentLiveStack.current=1) :
    HoareTime (CompactComplexParentLiveStack.saveProgram j) (fun z => z=v)
      (fun z => z=CompactComplexParentLiveStack.saved j v before)
      ((2*saveConstant)*CompactFallbackAxisRun.volume D K0 ell q) :=
  (CompactComplexParentLiveStack.save j v before ht hh).consequence (fun _ h => h) (fun _ h => h)
    (costs_original c m d D G K0 ell q level before completed target progress hc hK hlevel hD).1

/-- Actual post-child target capture and parent-live pop also have the original
fallback-volume bound. The saved frame remains a literal tape equality. -/
theorem restore_after_child_original (j : Fin s) (c m d D G K0 ell q level before completed target : ℕ)
    (progress : Progress (CompactReservationNativeRows.shape c m d D G K0)
      (CompactNativeRoleReservedBridge.precision c m d D K0 q) before completed target)
    (hc : 0<c) (hK : 0<K0) (hlevel : level≤CompactGlobalRowPadding.depth m d)
    (hD : CompactGlobalReservation.reservedAxes c m d G K0≤D)
    (v u : Tapes (CompactComplexParentLiveStack.tapes s c) 2)
    (hstack : u.tape (CompactComplexParentLiveStack.liveStack j)=
      (CompactComplexParentLiveStack.saved j v before).tape (CompactComplexParentLiveStack.liveStack j))
    (hstackHead : u.head (CompactComplexParentLiveStack.liveStack j)=
      (CompactComplexParentLiveStack.saved j v before).head (CompactComplexParentLiveStack.liveStack j))
    (hcurrent : u.tape CompactComplexParentLiveStack.current=BinaryDescriptorStack.descriptor (bits target))
    (hcurrentHead : u.head CompactComplexParentLiveStack.current=1)
    (htarget : u.tape CompactComplexParentLiveStack.target=(fun _ => blank))
    (htargetHead : u.head CompactComplexParentLiveStack.target=0)
    (hfree : ∀ z,v.head (CompactComplexParentLiveStack.liveStack j)≤z →
      z<v.head (CompactComplexParentLiveStack.liveStack j)+1+(bits before).length →
      v.tape (CompactComplexParentLiveStack.liveStack j) z=blank) :
    HoareTime (CompactComplexParentLiveStack.restoreWithTargetProgram j) (fun z => z=u)
      (fun z => z=CompactComplexParentLiveStack.restoredWithTarget j u
        (v.tape (CompactComplexParentLiveStack.liveStack j)) (v.head (CompactComplexParentLiveStack.liveStack j)) before target)
      ((2*restoreConstant)*CompactFallbackAxisRun.volume D K0 ell q) :=
  (CompactComplexParentLiveStack.restore_after_child j v u before target hstack hstackHead hcurrent hcurrentHead
    htarget htargetHead hfree).consequence (fun _ h => h) (fun _ h => h)
    (costs_original c m d D G K0 ell q level before completed target progress hc hK hlevel hD).2.1

end
end IntegerMultBounds.Machine.CompactComplexParentLiveStackBudget
