import IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturn
import IntegerMultBounds.Machine.CompactComplexNonleafRoleReturnBudget
import IntegerMultBounds.Machine.CompactComplexNonleafRoleMergeReturn

/-! Complete generated-count payload recovery has a uniform native-volume
bound on the actual shared bank. Returned source support follows from literal
native coefficient widths, while arbitrary controller and private frames remain. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturnBudget
noncomputable section
open CompactComplexNonleafRoleEntry
open CompactComplexNonleafRoleSourceReturn (base entry_clock)
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

abbrev constant := CompactComplexNonleafRoleReturnBudget.constant

theorem cost_linear (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hK : 0<sh.chunk) :
    CompactComplexNonleafRoleReturn.cost (s:=s) selected sh rows ell p rho left count slots right src dst ≤
      constant c*volume rows sh ell p :=
  CompactComplexNonleafRoleReturnBudget.cost_linear selected sh rows ell p rho left count slots right src dst hr hA hG hK

/-- Literal arbitrary child-result words supply their own support proof;
readiness is checked only on protected actual endpoints. -/
theorem runs_linear (selected : Fin c) (sh : Shape)
    (rows ell p rho left count slots right src dst : ℕ)
    (v : Tapes (CompactComplexNonleafRoleEntry.tapes s c) 2)
    (u : Tapes (CompactComplexNonleafRoleSourceReturn.tapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array sh (rows/c) ell)
    (hw : ∀ j,(f j).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f j).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (hraw : Placement.active headerPlacement v=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hclock : v.head clock=0 ∧ v.tape clock=(fun _ => blank))
    (hsource : v.head source=0 ∧ RoleArrayStack.Supported (v.tape source)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false))
    (hroles : ∀ j,v.head (roleTape j)=0 ∧ RoleArrayStack.Supported (v.tape (roleTape j))
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true))
    (hfree : CompactComplexNonleafRoleReturn.Free selected
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p false)
      (CompactComplexSpectatorVolumeHeaders.streamVolume sh c rows ell p true) v)
    (hheaders : Placement.active headerPlacement (base u)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst))
    (hresult : (base u).head source=0 ∧ (base u).tape source=(NativeZeroPadding.word (NativeZeroPaddingArray.word f)))
    (hblank : ∀ j,(base u).head (roleTape j)=0 ∧ (base u).tape (roleTape j)=(fun _ => blank))
    (hstack : (base u).head stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head stack ∧
      (base u).tape stack=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape stack)
    (hclockActual : (base u).head clock=0 ∧ (base u).tape clock=(fun _ => blank)) :
    HoareTime (CompactComplexNonleafRoleSourceReturn.program selected) (fun z => z=u)
      (fun z => z=CompactComplexNonleafRoleSourceReturn.output selected v u (NativeZeroPadding.word (NativeZeroPaddingArray.word f)))
      (constant c*volume rows sh ell p) := by
  have hreturned := CompactComplexNonleafRoleMergeReturn.returned_supported sh rows ell p f hw
  have he := entry_clock selected sh rows ell p rho left count slots right src dst v
  have hclockFrame : (base u).head clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).head clock ∧
      (base u).tape clock=(CompactComplexNonleafRoleEntry.output selected sh rows ell p rho left count slots right src dst v).tape clock :=
    ⟨hclockActual.1.trans (he.1.trans hclock.1).symm,
      hclockActual.2.trans (he.2.trans hclock.2).symm⟩
  have h := CompactComplexNonleafRoleSourceReturn.runs selected sh rows ell p rho left count slots right src dst
    v u (NativeZeroPadding.word (NativeZeroPaddingArray.word f)) hc hr hgroup hG hA hK
    hraw hclock hsource hroles hfree hreturned hheaders hresult hblank hstack hclockFrame
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz)
    (cost_linear (s:=s) selected sh rows ell p rho left count slots right src dst hr hA hG hK)

end
end IntegerMultBounds.Machine.CompactComplexNonleafRoleSourceReturnBudget
