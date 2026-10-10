import IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetRestore
import IntegerMultBounds.Machine.CompactComplexNonleafChildAddress
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! The paid nonleaf continuation returns the literal next raw caller bank,
its named scalar prefix and true live ledger. Concrete child address maps retain
every spectator; actual child execution is the explicit induction premise. -/
namespace IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetPrefix
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

/-- Promotion on the actual original caller Path preserves all untouched roles
and pays the normalized child numerator growth with the returned-volume ledger. -/
theorem prefix_grid (sh : Shape) (rows ell q n k g baselineP C levels frames returned axes : ℕ)
    (selected : Fin c) (before : Fin c → Array sh rows ell) (child : Array sh rows ell)
    (hd : CompactComplexNonleafChildAddress.roles ∣ rows)
    (rho : Fin sh.chunk) (visit : Visit sh.active left (k+2)) (call : Networks.ComplexRecursiveCallSchema.Call)
    (hw : ∀ role,Width sh rows ell q (before role))
    (hg : ∀ role,Grid sh rows ell q n
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*returned+axes))) (before role))
    (hcompleted : ∀ i,decoded sh rows ell q (n+2*arity^(k+1)) child i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded sh rows ell q n (before selected)
          (CompactComplexNonleafChildAddress.inputIndex sh rows ell hd rho
            (CompactComplexNonleafChildAddress.childVisit visit call) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh rows ell hd i)
        (CompactComplexNonleafChildAddress.outputAddress sh rows ell hd rho
          (CompactComplexNonleafChildAddress.childVisit visit call) i))
    (hcapacity : 2*arity^(k+1)≤half sh q+1)
    (hguard : CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
      (frames+2*returned+axes))*2^(2*arity^(k+1))<2^(half sh q)) :
    (∀ role,Grid sh rows ell q (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C levels
        (frames+2*(returned+arity^(k+1))+axes))) (aligned sh rows ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh rows ell q (n+2*arity^(k+1))
      (aligned sh rows ell k selected before child role)=decoded sh rows ell q n (before role)) := by
  have hc := CompactComplexNonleafChildAddress.selected_grid sh rows ell q n _ hd rho
    (CompactComplexNonleafChildAddress.childVisit visit call) (before selected) child (hg selected) hcompleted
  have hs := CompactComplexChildGridAlignment.shared_grid sh rows ell q n _ (2*arity^(k+1)) selected before
    (aligned sh rows ell k selected before child) hg (by simpa only [aligned,ite_true] using hc)
    (fun role hr i => by
      simp only [aligned,ite_eq_right hr]
      exact CompactComplexChildGridPromoted.promotes sh rows ell q n _ _ (before role)
        (hw role) (hg role) hcapacity hguard i)
  refine ⟨?_,hs.2⟩
  intro role
  rw [←CompactComplexNonleafEventProgress.prefix_bound g baselineP C levels frames returned axes (arity^(k+1))]
  exact hs.1 role

/-- Complete actual promotion, shared-live commit and saved-target pop yield
the literal next raw caller endpoint with its named prefix and true ledger.
No runtime, grid certificate or child address family is supplied separately. -/
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
    (hcompleted : ∀ i,decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
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
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have hphysical := CompactComplexNonleafSpectatorTargetRestore.runs_linear sh rows ell metadataP n completed k
    v selected progress hc hr hgroup hG hA hK before child hw control queue scalar tail storage source head
    hcurrent htarget frame f p ledgerN parentTarget ledgerLeft ledgerExponent ledger hstack hstackHead hf
  have hguard := CompactComplexNonleafEventProgress.promotion_from_path progress.parentPath
    g baselineP C axes k metadataP ha hp haxes hC hroom
  have hsemantic := prefix_grid sh (rows/c) ell (metadataP-2*sh.bits) n k g baselineP C progress.parentLevels
    progress.parentFrames progress.parentReturned axes selected before child hd rho visit call hw hg
    hcompleted hguard.1 hguard.2
  refine ⟨hphysical,hsemantic.1,hsemantic.2,?_⟩
  have hb := progress.before_live
  unfold CompactComplexDenominatorCapacity.ledger at *
  omega

/-- A table whose actual decoded return block is this concrete continuation
reaches its unique next original event, carrying the exact caller prefix.
Only machine identity connects the existing table; no local execution or time
bound is supplied as an external contract. -/
theorem table_return_path (sh : Shape) (rows ell metadataP n completed k : ℕ)
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
    (hcompleted : ∀ i,decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1)) child i=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (arity^k))
        (fun wire address => decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before selected)
          (CompactComplexNonleafChildAddress.inputIndex sh (rows/c) ell hd rho
            (CompactComplexNonleafChildAddress.childVisit visit call) i wire address))
        (CompactComplexNonleafChildAddress.outputWire sh (rows/c) ell hd i)
        (CompactComplexNonleafChildAddress.outputAddress sh (rows/c) ell hd rho
          (CompactComplexNonleafChildAddress.childVisit visit call) i))
    (ht : 0<CompactComplexNonleafSpectatorPlacement.nodeTapes s c)
    (pcStack : Fin (CompactComplexNonleafSpectatorPlacement.nodeTapes s c))
    (childReturn : Networks.ComplexRecursiveCallSchema.Call →
      Σ q,Program (CompactComplexNonleafSpectatorPlacement.nodeTapes s c) q 2)
    (controls : Fin 4 → Σ q,Program (CompactComplexNonleafSpectatorPlacement.nodeTapes s c) q 2)
    (event : CompactComplexCompletedLiveLower.Event →
      Σ q,Program (CompactComplexNonleafSpectatorPlacement.nodeTapes s c) q 2)
    (isStopped : Fin (controls 0).1 → Bool)
    (hblock : childReturn call=⟨_,program (s:=s) selected⟩) :
    (∃ steps≤constant c*CompactNativeRoleTransferBudget.volume rows sh ell metadataP+1,
      CompactComplexFixedNodePaths.nodePath ht pcStack childReturn controls event isStopped
        (CompactComplexScheduledPCDecode.savedPC call)
        (full (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail storage
          (returnedPayload sh (rows/c) ell selected source head before child)) frame)
        steps (CompactComplexScheduledPCLayout.callNextPC call)
        (full (bank control queue scalar (CompactComplexNativeCodec.raw v rows ell metadataP) tail
          (restoredStorage storage (n+2*arity^(k+1)) f p parentTarget)
          (payload sh (rows/c) ell source head (aligned sh (rows/c) ell k selected before child))) frame)) ∧
    (∀ role,Grid sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (CompactFramedScalarGrid.bound g (CompactRecursiveGridBudget.bound baselineP C progress.parentLevels
        (progress.parentFrames+2*(progress.parentReturned+arity^(k+1))+axes)))
      (aligned sh (rows/c) ell k selected before child role)) ∧
    (∀ role,role≠selected → decoded sh (rows/c) ell (metadataP-2*sh.bits) (n+2*arity^(k+1))
      (aligned sh (rows/c) ell k selected before child role)=
      decoded sh (rows/c) ell (metadataP-2*sh.bits) n (before role)) ∧
    n+2*arity^(k+1)≤CompactComplexDenominatorCapacity.ledger progress.R progress.baseline
      progress.parentLevels progress.parentFrames (progress.parentReturned+arity^(k+1)) progress.parentUsed := by
  have h := prefix_runs sh rows ell metadataP n completed k v selected progress hc hr hgroup hG hA hK
    before child hw control queue scalar tail storage source head hcurrent htarget frame f p
    ledgerN parentTarget ledgerLeft ledgerExponent ledger hstack hstackHead hf
    g baselineP C axes ha hp haxes hC hroom hg hd rho visit call hcompleted
  refine ⟨?_,h.2⟩
  apply CompactComplexFixedNodePaths.decoded_return_path ht pcStack childReturn controls event isStopped
    call _ _ (constant c*CompactNativeRoleTransferBudget.volume rows sh ell metadataP)
  rw [hblock]
  exact h.1

end
end IntegerMultBounds.Machine.CompactComplexNonleafSpectatorTargetPrefix
