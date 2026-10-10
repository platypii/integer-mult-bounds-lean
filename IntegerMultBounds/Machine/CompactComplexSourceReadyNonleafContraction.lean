import IntegerMultBounds.Machine.CompactComplexControllerExactReturnBudget
import IntegerMultBounds.Machine.CompactComplexSourceReadyChildReturnPath
import IntegerMultBounds.Machine.CompactComplexSourceReadyFullNodeControls

/-! Physical all-role contraction borrows the existing node work10 while
retaining the nine Entry/frame tapes, the leaf bank and scalar scratch. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSourceReadyWorkspace (publicTapes)
open CompactComplexControllerExactReturn (returned committed)
open CompactComplexSpectatorVolumeHeaders (roleRows)
open CompactNativeRoleTransferBudget (volume)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactGadgetReservationShape (Shape)
open RecursiveChildQuotientsConstant (bits)
open NativeSignedGapReturn (word)
variable {s c q B : ℕ}
attribute [local irreducible] CompactComplexExactReturnFamily.compile
  CompactComplexControllerExactReturn.program

private theorem work_public_slot (i : Fin (permanentTapes (10+s) c+9)) :
    CompactComplexSourceReadyChildReturnPath.workEquiv s c (Fin.castAdd 10 i)=
      Fin.castAdd 10 ((CompactComplexNonleafSpectatorTargetRestore.entryEquiv s c).symm i) := by
  simp [CompactComplexSourceReadyChildReturnPath.workEquiv]
private theorem work_work_slot (i : Fin 10) :
    CompactComplexSourceReadyChildReturnPath.workEquiv s c (Fin.natAdd (permanentTapes (10+s) c+9) i)=Fin.natAdd (CompactComplexNonleafRoleChildBank.tapes s c) i := by
  simp [CompactComplexSourceReadyChildReturnPath.workEquiv]

private theorem full_reindex (v : Tapes (permanentTapes (10+s) c) 2) (fr : Tapes 9 2)
    (work : Tapes 10 2) :
    ((v.append fr).append work).reindex (CompactComplexSourceReadyChildReturnPath.workEquiv s c)=
      (CompactComplexNonleafSpectatorTargetRestore.entry v fr).append work := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals obtain ⟨i,rfl⟩ := (CompactComplexSourceReadyChildReturnPath.workEquiv s c).surjective i
  all_goals simp only [Equiv.symm_apply_apply]
  all_goals induction i using Fin.addCases with
  | left i => simp only [work_public_slot,Tapes.append,Fin.addCases_left,
      CompactComplexNonleafSpectatorTargetRestore.entry,Tapes.reindex,Equiv.symm_symm,
      Equiv.apply_symm_apply]
  | right i => simp only [work_work_slot,Tapes.append,Fin.addCases_right]

def placed (M : Program (permanentTapes (10+s) c+10) q 2) :=
  CompactComplexSourceReadyWorkspace.spectatorProgram
    (reindex (Placement.placed M (CompactComplexNonleafSpectatorPlacement.placement (permanentTapes (10+s) c)))
      (CompactComplexSourceReadyChildReturnPath.workEquiv s c))

def ready (v : Tapes (permanentTapes (10+s) c) 2) (frame : Tapes 9 2)
    (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :=
  CompactComplexSourceReadyWorkspace.bank (CompactComplexNonleafSpectatorTargetRestore.entry v frame)
    leaf (SharedBank.empty 10 2)

theorem placed_runs {M : Program (permanentTapes (10+s) c+10) q 2}
    {v w : Tapes (permanentTapes (10+s) c) 2}
    (h : HoareTime M (fun z => z=v.append (SharedBank.empty 10 2))
      (fun z => z=w.append (SharedBank.empty 10 2)) B)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2) :
    HoareTime (placed M) (fun z => z=ready v frame leaf)
      (fun z => z=ready w frame leaf) B := by
  have hh := CompactComplexNonleafSpectatorPlacement.lift_runs h frame
  have hr := hoare_reindex_eq hh (CompactComplexSourceReadyChildReturnPath.workEquiv s c)
  simp only [CompactComplexNonleafSpectatorPlacement.full,full_reindex] at hr
  exact CompactComplexSourceReadyWorkspace.spectator_runs hr leaf

def program (headerCount : ℕ) (merge : Bool) :
    Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2 :=
  ⟨_,placed (CompactComplexControllerExactReturn.program (s:=s) (c:=c) headerCount merge).2⟩

theorem raw_runs_native_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current target : ℕ) (hle : target≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits target))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    HoareTime (program (s:=s) (c:=c) headerCount merge).2
      (fun z => z=ready (bank control queue scalar old tail storage payload) frame leaf)
      (fun z => z=ready (bank control queue scalar old tail (committed storage target)
        (CompactComplexControllerExactReturn.returned ws current target payload)) frame leaf)
      (CompactComplexControllerExactReturnBudget.nativeConstant headerCount c*volume rows sh ell metadataP) := by
  have h := CompactComplexControllerExactReturnBudget.raw_runs_native_linear sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current target hle hc ht hs path R base usedRows hb hu hroom hlive
  exact placed_runs (M:=(CompactComplexControllerExactReturn.program (s:=s) (c:=c) headerCount merge).2) h frame leaf

open ButterflySigned (signedValue complexValue)
open Networks.GaussianPrecision (BoundedGrid)
theorem nonleaf_runs_native_linear (sh : Shape) (headerCount rows ell metadataP : ℕ) (merge : Bool)
    (hcount : 0<headerCount) (hr : 0<rows) (hgroup : 0<rows/headerCount)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hmetadata : 2*sh.bits≤metadataP)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : Fin c → CompactSpectatorVisitGeometry.Array sh (roleRows headerCount rows merge) ell)
    (hw : ∀ j,CompactSpectatorInheritedGrid.Width sh (roleRows headerCount rows merge) ell
      (metadataP-2*sh.bits) (f j))
    (current n k M : ℕ)
    (hledger : CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤current)
    (hc : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=RadixZeroFill.encodedBinary (bits current))
    (ht : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=RadixZeroFill.encodedBinary (bits (CompactComplexDenominatorPolicy.networkTarget n k)))
    (hs : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧
      payload.tape (Fin.natAdd 1 j)=word (CompactComplexStoppedGridHandoff.words (f j)))
    (roles : Fin c → Networks.ComplexFramedExecution.Wire)
    (addresses : Fin (ButterflySpectatorGeometry.Size (roleRows headerCount rows merge) sh.bits (2^ell)) →
      Networks.BinaryColumns.Address (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (original : Networks.ComplexFramedExecution.Wire →
      Networks.BinaryColumns.Arrays (25^3) (CompactComplexRecursiveGeometry.arity^k))
    (hg : ∀ wire address,BoundedGrid n M (original wire address))
    (hcompleted : ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits)) (f j i).2) current=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤metadataP-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 9 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell metadataP rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (f j)
    HoareTime (program (s:=s) (c:=c) headerCount merge).2
      (fun z => z=ready (bank control queue scalar old tail storage payload) frame leaf)
      (fun z => z=ready (bank control queue scalar old tail
        (committed storage (CompactComplexDenominatorPolicy.networkTarget n k))
        (CompactComplexControllerExactReturn.returned ws current (CompactComplexDenominatorPolicy.networkTarget n k) payload)) frame leaf)
      (CompactComplexControllerExactReturnBudget.nativeConstant headerCount c*volume rows sh ell metadataP) ∧
    ∀ j i,complexValue
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (CompactComplexControllerExactReturn.contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).1)
      (signedValue (CompactSpectatorInheritedGrid.half sh (metadataP-2*sh.bits))
        (CompactComplexControllerExactReturn.contracted (current-CompactComplexDenominatorPolicy.networkTarget n k) (f j) i).2)
      (CompactComplexDenominatorPolicy.networkTarget n k)=
      Networks.FramedCircuit.run (Networks.ComplexFramedExecution.network (CompactComplexRecursiveGeometry.arity^k))
        original (roles j) (addresses i) := by
  obtain ⟨hrun,hexact⟩ := CompactComplexControllerExactReturnBudget.nonleaf_runs_native_linear sh headerCount rows ell metadataP merge
    hcount hr hgroup hG hA hK hmetadata rho left count slots right src dst control queue scalar tail storage payload
    f hw current n k M hledger hc ht hs roles addresses original hg hcompleted path R base usedRows hb hu hroom hlive
  exact ⟨placed_runs (M:=(CompactComplexControllerExactReturn.program (s:=s) (c:=c) headerCount merge).2) hrun frame leaf,hexact⟩

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction
