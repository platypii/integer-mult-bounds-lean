import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturn
import IntegerMultBounds.Machine.CompactComplexNonleafRoleEntryBudget

/-! Both generated-count recovery lifecycles have a uniform native-volume
runtime bound, paying selected-result recovery, spectator pops, master-source
restoration, metadata cleanup and every assembly join. Recursive child
execution, reverse child merge and controller handoff remain separate. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNonleafRoleEntry
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open CompactNativeRoleTransferBudget (volume)
open ButterflyAxisHeadersArithmetic (scheduleCost)
variable {s c : ℕ}

open CompactComplexNonleafRoleEntryBudget (inactive_length_le stream_native)

def constant (c : ℕ) := 2*CompactComplexSpectatorVolumeBudget.constant c+92*(c+2)+5

theorem cost_linear (selected : Fin c) (sh : Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell metadataP rho left count slots right src dst≤
      constant c*volume rows sh ell metadataP := by
  have hm := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    rho left count slots right src dst false hr hA hG hK
  have hs := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    rho left count slots right src dst true hr hA hG hK
  have hv : 0<volume rows sh ell metadataP :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hmaster := Nat.mul_le_mul_left 92 (stream_native sh c rows ell metadataP false)
  have hlen := inactive_length_le (s:=s) selected
  have hroles := Nat.mul_le_mul (by omega :
      92*(inactive (s:=s) selected).length+88≤92*(c+1))
    (stream_native sh c rows ell metadataP true)
  unfold CompactComplexNonleafRoleReturn.cost constant
  nlinarith

/-- The bound is attached to the actual returned-result machine, without
assuming the child computes the original unmodified payload. -/
theorem runs_linear (selected : Fin c) (sh : Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2) (returned : ℤ → Fin 6)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (streamVolume sh c rows ell metadataP true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (streamVolume sh c rows ell metadataP false) (streamVolume sh c rows ell metadataP true) v)
    (hreturned : RoleArrayStack.Supported returned (streamVolume sh c rows ell metadataP true)) :
    HoareTime (CompactComplexNonleafRoleReturn.program selected)
      (fun z => z=SharedPlacementAlphabet.setTape
        (output selected sh rows ell metadataP rho left count slots right src dst v) source returned 0)
      (fun z => z=SharedPlacementAlphabet.setTape v (roleTape selected) returned 0)
      (constant c*volume rows sh ell metadataP) := by
  have h := CompactComplexNonleafRoleReturn.runs_result selected sh rows ell metadataP rho left count slots right src dst v returned
    hc hr hgroup hG hA hK hraw hclock hsource hroles hfree hreturned
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh)
    (cost_linear (s:=s) selected sh rows ell metadataP rho left count slots right src dst hr hA hG hK)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnBudget
