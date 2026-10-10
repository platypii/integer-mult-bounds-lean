import IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
import IntegerMultBounds.Machine.CompactComplexCorrectedChildGridSemantics

/-! Corrected child tensor semantics supplies the original parent return grid
and ledger, while the literal promotion/live commit/target restoration retains
its genuine physical cost. Child tensor correctness remains an induction premise. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedChildReturnPrefix
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactSpectatorVisitGeometry (Array)
open CompactSpectatorInheritedGrid
open CompactComplexNonleafEventProgress (aligned)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexNonleafSpectatorPlacement (full)
open CompactComplexNonleafSpectatorTargetRestore (program constant restoredStorage)
open CompactComplexStoppedGridHandoff (payload)
open CompactComplexNonleafSpectatorHandoff (returnedPayload)
open ActiveRepairRankHeadersCommands (State)
open RecursiveChildQuotientsConstant (bits)
variable {s c left : ℕ}

/-- Genuine corrected recursive tensor action derives the selected call's
completed prefix, untouched spectators and actual advanced live ledger. -/
theorem completed_prefix (sh : Shape) (rows ell precision n completed k : ℕ)
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (progress : CompactComplexChildAlignmentBudget.Progress sh precision n completed (n+2*arity^(k+1)))
    (before : Fin CompactComplexRolePhaseSite.roleCount → CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (result : CompactSpectatorVisitGeometry.Array sh (rows/CompactComplexRolePhaseSite.roleCount) ell)
    (hw : ∀ j,Width sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (before j))
    (g baselineP C axes : ℕ) (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤precision)
    (haxes : axes+2*arity^(k+1)≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role))
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows/CompactComplexRolePhaseSite.roleCount)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2))
    (hsem : ∀ i,decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits)
      (n+2*arity^(k+1)) result i=
      CompactComplexCorrectedChildGridSemantics.tensor call
        (fun wire address => decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n
          (before (CompactComplexRolePhaseSite.role call.site))
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd rho
            (CompactComplexNonleafChildAddress.childVisit visit call) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/CompactComplexRolePhaseSite.roleCount) ell hd rho
          (CompactComplexNonleafChildAddress.childVisit visit call) i)) :
    (∀ role,Grid sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (CompactComplexNonleafEventProgress.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell k
        (CompactComplexRolePhaseSite.role call.site) before result role)) ∧
    (∀ role,role≠CompactComplexRolePhaseSite.role call.site → decoded sh (rows/CompactComplexRolePhaseSite.roleCount)
      ell (precision-2*sh.bits) (n+2*arity^(k+1))
      (CompactComplexNonleafEventProgress.aligned sh (rows/CompactComplexRolePhaseSite.roleCount) ell k
        (CompactComplexRolePhaseSite.role call.site) before result role)=
      decoded sh (rows/CompactComplexRolePhaseSite.roleCount) ell (precision-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have h := CompactComplexCorrectedChildGridSemantics.corrected_prefix_grid_from_path
    sh (rows/CompactComplexRolePhaseSite.roleCount) ell precision n k g baselineP C progress.parentLevels
    progress.parentFrames progress.parentReturned axes (CompactComplexRolePhaseSite.role call.site)
    before result hd rho visit call progress.parentPath ha hp haxes hC hroom hw hg hsem
  refine ⟨h.1,h.2,?_⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega


/-- The real promotion, shared-live installation and saved-target pop
compose with the corrected recursive tensor grid and returned-volume ledger.
The machine and paid runtime are derived, rather than supplied as a callback. -/
theorem prefix_runs (sh : Shape) (rows ell metadataP n completed k : ℕ)
    (v : ActivePrefixStageParameters.Stage sh) (selected : Fin c)
    (progress : CompactComplexChildAlignmentBudget.Progress sh metadataP n completed (n+2*arity^(k+1)))
    (hc : 0<c) (hr : 0<rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk)
    (before : Fin c → Array sh (rows/c) ell) (child : Array sh (rows/c) ell)
    (hw : ∀ j,Width sh (rows/c) ell (metadataP-2*sh.bits) (before j))
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (source : ℤ → Fin 6) (head : ℤ)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits n))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))))
    (frame : Tapes 9 2)
    (f : ℤ → Fin 6) (p : ℤ) (ledgerN parentTarget ledgerLeft ledgerExponent : ℕ)
    (ledger : CompactComplexNonleafRoleChildBankBudget.Ledger sh metadataP ledgerN parentTarget ledgerLeft ledgerExponent)
    (hstack : storage.tape ⟨9,by omega⟩=BinaryDescriptorStack.frame f p (bits parentTarget))
    (hstackHead : storage.head ⟨9,by omega⟩=p+1+(bits parentTarget).length)
    (hf : ∀ z,p≤z → z<p+1+(bits parentTarget).length → f z=blank)
    (g baselineP C axes : ℕ) (ha : 0<sh.active) (hp : baselineP+2*sh.bits≤metadataP)
    (haxes : axes+2*arity^(k+1)≤sh.bits) (hC : CompactFramedScalarGrid.growthConstant≤C)
    (hroom : dependencyCoefficient C+Nat.clog 2 (C+1)+CompactComplexScalarIntegerRows.guardBits≤sh.chunk)
    (hg : ∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*progress.parentReturned+axes))) (before role))
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows/c)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (hsem : ∀ i,decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      CompactComplexCorrectedChildGridSemantics.tensor call
        (fun wire address => decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before selected)
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/c) ell hd rho
            (CompactComplexNonleafChildAddress.childVisit visit call) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/c) ell hd i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/c) ell hd rho
          (CompactComplexNonleafChildAddress.childVisit visit call) i)) :
    HoareTime (program (s:=s) selected)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)) frame)
      (fun z => z=full
        (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (restoredStorage storage (n+2*arity^(k+1)) f p parentTarget)
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))) frame)
      (constant c*CompactNativeRoleTransferBudget.volume rows sh ell metadataP) ∧
    (∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (aligned sh (rows/c) ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (aligned sh (rows/c) ell k selected before child role)=
      decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed ∧
    (restoredStorage storage (n+2*arity^(k+1)) f p parentTarget).head ⟨7,by omega⟩=1 ∧
    (restoredStorage storage (n+2*arity^(k+1)) f p parentTarget).tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (bits (n+2*arity^(k+1))) := by
  have hphysical := CompactComplexNonleafSpectatorTargetRestore.runs_linear sh rows ell metadataP n completed k
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage source head
    hcurrent htarget frame f p ledgerN parentTarget ledgerLeft ledgerExponent ledger hstack hstackHead hf
  have hsemantic := CompactComplexCorrectedChildGridSemantics.corrected_prefix_grid_from_path
    sh (rows/c) ell metadataP n k g baselineP C progress.parentLevels progress.parentFrames
    progress.parentReturned axes selected before child hd rho visit call progress.parentPath
    ha hp haxes hC hroom hw hg hsem
  have hports := CompactComplexNonleafSpectatorTargetRestore.restoredStorage_ports storage
    (n+2*arity^(k+1)) f p parentTarget
  refine ⟨hphysical,hsemantic.1,hsemantic.2,?_,hports.1,hports.2.1⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega

end
end IntegerMultBounds.Machine.CompactComplexCorrectedChildReturnPrefix
