import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturn
import IntegerMultBounds.Machine.CompactComplexNonleafRoleTransferBudget
import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnBudget

/-! Complete physical merge-and-parent-recovery costs are linear in the
parent native volume. The bound belongs to the actual composed tape program;
recursive child computation and common-grid alignment remain separate. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturnBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNonleafRoleEntry
open CompactComplexNonleafRoleMergeReturn (childBank)
open CompactSpectatorLeafSetup (raw)
open SharedPlacementAlphabet (setTape)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

def constant (c : ℕ) := CompactComplexNonleafRoleTransferBudget.constant c+
  CompactComplexNonleafRoleReturnBudget.constant c+1

theorem cost_linear (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    CompactComplexNonleafRoleMergeReturn.cost (s:=s) selected sh rows ell p rho left count slots right src dst≤
      constant c*volume rows sh ell p := by
  have hrows : 0<rows := lt_of_lt_of_le hr (Nat.div_le_self rows c)
  have hV : 0<volume rows sh ell p := Nat.mul_pos hrows (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hm := CompactComplexNonleafRoleTransferBudget.transfer_linear true c sh rows ell p
    rho left count slots right src dst hc hr hd hparent hA hG hK
  have hr := CompactComplexNonleafRoleReturnBudget.cost_linear (s:=s) selected sh rows ell p
    rho left count slots right src dst hrows hA hG hK
  simp only [ite_true] at hm
  unfold CompactComplexNonleafRoleMergeReturn.cost constant
  nlinarith

/-- Literal parent recovery retains an arbitrary computed result and updated
controller header, with all scratch clean and the complete local cost paid. -/
theorem runs_linear (selected : Fin c) (sh : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,(f j).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f j).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (v : Tapes (tapes s c) 2) (i : Fin (tapes s c)) (advanced : ℤ → Fin 6) (head : ℤ)
    (hi : ∀ j,i≠numeric j) (hs : i≠stack) (hsourceSlot : i≠source)
    (hrslot : ∀ j,i≠roleTape j) (hclockSlot : i≠clock)
    (hc : 0<c) (hr : 0<rows/c) (hd : c ∣ rows/c) (hparent : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (raw sh rows ell p rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true) v) :
    HoareTime (CompactComplexNonleafRoleMergeReturn.program (s:=s) selected)
      (fun z => z=childBank selected sh rows ell p rho left count slots right src dst hd f v i advanced head)
      (fun z => z=(setTape (setTape v (roleTape selected)
        (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) 0) i advanced head).append (SharedBank.empty 7 2))
      (constant c*volume rows sh ell p) := by
  have h := CompactComplexNonleafRoleMergeReturn.runs selected sh rows ell p rho left count slots right src dst
    f hw v i advanced head hi hs hsourceSlot hrslot hclockSlot hc hr hd hparent hG hA hK
    hraw hclock hsource hroles hfree
  exact h.consequence (fun _ hh => hh) (fun _ hh => hh)
    (cost_linear (s:=s) selected sh rows ell p rho left count slots right src dst hc hr hd hparent hA hG hK)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturnBudget
