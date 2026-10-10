import IntegerMultBounds.Machine.CompactComplexNonleafRoleEntry

/-! The two physical parking lifecycles have one uniform native-volume bound.
The retained master and the selected role have different generated lengths;
both header lifecycles, spectator parking and every assembly join are paid.
This accounts for entry only, not child splitting or recursive execution. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleEntryBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNonleafRoleEntry
open CompactComplexSpectatorVolumeHeaders (streamVolume)
open CompactNativeRoleTransferBudget (volume)
open ButterflyAxisHeadersArithmetic (scheduleCost)
variable {s c : ℕ}

def cost (selected : Fin c) (sh : Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ) :=
  scheduleCost (CompactNativeRoleHeaders.schedule c false)
    (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
    88*streamVolume sh c rows ell metadataP false+
    scheduleCost CompactNativeRoleHeaders.cleanup
      (CompactNativeRoleHeaders.prepared c false sh rows ell metadataP rho left count slots right src dst)+2+
    (scheduleCost (CompactNativeRoleHeaders.schedule c true)
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst)+
      (88*(inactive (s:=s) selected).length+88)*streamVolume sh c rows ell metadataP true+
      scheduleCost CompactNativeRoleHeaders.cleanup
        (CompactNativeRoleHeaders.prepared c true sh rows ell metadataP rho left count slots right src dst)+2)+1

def constant (c : ℕ) := 2*CompactComplexSpectatorVolumeBudget.constant c+88*(c+2)+5

theorem inactive_length_le (selected : Fin c) :
    (inactive (s:=s) selected).length≤c := by
  exact (List.length_filter_le _ _).trans_eq List.length_ofFn

theorem stream_native (sh : Shape) (c rows ell metadataP : ℕ) (merge : Bool) :
    streamVolume sh c rows ell metadataP merge≤volume rows sh ell metadataP := by
  have h : CompactComplexSpectatorVolumeHeaders.roleRows c rows merge≤rows := by
    cases merge
    · exact le_rfl
    · exact Nat.div_le_self _ _
  simpa only [streamVolume,volume,CompactNativeRoleOriginal.symbols,
    CompactNativeRoleOriginal.inner,Nat.mul_assoc] using
    Nat.mul_le_mul_right (CompactNativeRoleOriginal.symbols sh ell metadataP) h

theorem cost_linear (selected : Fin c) (sh : Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    cost (s:=s) selected sh rows ell metadataP rho left count slots right src dst≤
      constant c*volume rows sh ell metadataP := by
  have hm := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    rho left count slots right src dst false hr hA hG hK
  have hs := CompactComplexSpectatorVolumeBudget.setup_cleanup_native sh c rows ell metadataP
    rho left count slots right src dst true hr hA hG hK
  have hv : 0<volume rows sh ell metadataP :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell metadataP)
  have hmaster := Nat.mul_le_mul_left 88 (stream_native sh c rows ell metadataP false)
  have hlen := inactive_length_le (s:=s) selected
  have hroles := Nat.mul_le_mul (by omega :
      88*(inactive (s:=s) selected).length+88≤88*(c+1))
    (stream_native sh c rows ell metadataP true)
  unfold cost constant
  nlinarith

/-- The uniform bound belongs to the actual fixed entry machine, rather than
an uninstantiated arithmetic ledger. -/
theorem runs_linear (selected : Fin c) (sh : Shape)
    (rows ell metadataP rho left count slots right src dst : ℕ)
    (v : Tapes (tapes s c) 2)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (streamVolume sh c rows ell metadataP false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (streamVolume sh c rows ell metadataP true)) :
    HoareTime (program selected) (fun z => z=v)
      (fun z => z=output selected sh rows ell metadataP rho left count slots right src dst v)
      (constant c*volume rows sh ell metadataP) := by
  have h := runs selected sh rows ell metadataP rho left count slots right src dst v
    hc hr hgroup hG hA hK hraw hclock hsource hroles
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh)
    (cost_linear (s:=s) selected sh rows ell metadataP rho left count slots right src dst hr hA hG hK)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleEntryBudget
