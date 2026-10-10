import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafContraction
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalGeometry
import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalBank

/-! Actual current-node all-role contraction and same-row cyclic merge on the
fixed source-ready bank. All local machine specifications are derived internally. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath
noncomputable section
open CompactComplexNativeCodecFrame (bank permanentTapes)
open CompactComplexSourceReadyNonleafFinalGeometry
open CompactComplexControllerExactReturn (contracted committed)
open CompactGadgetReservationShape (Shape)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexNonleafRoleMergeCurrent.program

def mergeProgram : Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2 :=
  ⟨_,CompactComplexSourceReadyWorkspace.publicProgram (CompactComplexNonleafRoleMergeCurrent.program (10+s) c)⟩
def program : Σ q,Program (CompactComplexSourceReadyWorkspace.tapes s c) q 2 :=
  ⟨_,seq (CompactComplexSourceReadyNonleafContraction.program c true).2 (mergeProgram (s:=s) (c:=c)).2⟩
def constant (c : ℕ) := CompactComplexControllerExactReturnBudget.nativeConstant c c+
  CompactComplexNonleafRoleMergeCurrentBudget.constant c+1

theorem raw_runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (payload : Tapes (1+c) 2)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    (hsource : payload.head 0=0 ∧ payload.tape 0=fun _ => blank)
    (hroles : ∀ j,payload.head (Fin.natAdd 1 j)=0 ∧ payload.tape (Fin.natAdd 1 j)=
      NativeSignedGapReturn.word (CompactComplexStoppedGridHandoff.words
        (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    HoareTime (program (s:=s) (c:=c)).2
      (fun z => z=CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf)
      (fun z => z=CompactComplexSourceReadyWorkspace.bank
        ((CompactComplexNonleafRoleMergeCurrent.bank sh rows ell p rho left count slots right src dst
          (contracted (current-target) f) (v.append frame)).append (SharedBank.empty 7 2))
        leaf (SharedBank.empty 10 2))
      (constant c*volume rows sh ell p) := by
  let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
  let roles := fun j => CompactNativeRoleReservedBridge.role sh rows c ell hd f j
  let ws := fun j => CompactComplexStoppedGridHandoff.words (roles j)
  let ret := CompactComplexControllerExactReturn.returned ws current target payload
  let v := bank control queue scalar old tail (committed storage target) ret
  have hp : ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)=p := by
    unfold ButterflyIndependentGuardHeaders.reservation
    omega
  have hwidth : ∀ j,CompactSpectatorInheritedGrid.Width sh
      (CompactComplexSpectatorVolumeHeaders.roleRows c rows true) ell (p-2*sh.bits) (roles j) := by
    intro j i
    simpa only [CompactSpectatorInheritedGrid.Width,ButterflySpectatorSemantics.Width,
      ButterflySpectatorGeometry.Width,hp,roles,CompactNativeRoleReservedBridge.role,
      CompactNativeRoleGeometry.role,CompactNativeRoleHeaders.recordWidth] using
        (CompactNativeRoleReservedBridge.grouped_width sh rows c ell _ hd f hw _)
  have hcon := CompactComplexSourceReadyNonleafContraction.raw_runs_native_linear sh c rows ell p true
    hc hr hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage payload
    roles hwidth current target hle hcurrent htarget hroles path R base usedRows hb hu hroom
    (frame.append (SharedBank.empty 7 2)) leaf hlive
  have hsret := CompactComplexControllerExactReturn.returned_source ws current target payload
  have hs : (v.append frame).head CompactComplexNonleafRoleEntry.source=0 ∧
      (v.append frame).tape CompactComplexNonleafRoleEntry.source=fun _ => blank := by
    have h := CompactComplexSourceReadyNonleafFinalBank.source control queue scalar old tail
      (committed storage target) ret frame
    exact ⟨h.1.trans (hsret.1.trans hsource.1),h.2.trans (hsret.2.trans hsource.2)⟩
  have hrs : ∀ j,(v.append frame).head (CompactComplexNonleafRoleEntry.roleTape j)=0 ∧
      (v.append frame).tape (CompactComplexNonleafRoleEntry.roleTape j)=
        NativeZeroPadding.word (NativeZeroPaddingArray.word
          (CompactNativeRoleReservedBridge.role sh rows c ell hd (contracted (current-target) f) j)) := by
    intro j
    have h := CompactComplexSourceReadyNonleafFinalBank.role control queue scalar old tail
      (committed storage target) ret frame j
    have hr := CompactComplexControllerExactReturn.returned_role roles current target payload j
    refine ⟨h.1.trans hr.1,?_⟩
    rw [h.2,hr.2,words_tape]
    change NativeZeroPadding.word (NativeZeroPaddingArray.word
      (contracted (current-target) (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)))=_
    rw [contracted_role]
  have hm := CompactComplexNonleafRoleMergeCurrentBudget.runs_linear sh rows ell p rho left count slots right src dst
    hc hr hd hG hA hK (contracted (current-target) f) (contracted_width _ f hw) (v.append frame)
    (CompactComplexSourceReadyNonleafFinalBank.headers control queue scalar old tail (committed storage target) ret frame)
    hs hrs
  have hmerge := CompactComplexSourceReadyWorkspace.public_runs hm leaf (SharedBank.empty 10 2)
  have hcon' := hcon
  simp only [CompactComplexSourceReadyNonleafContraction.ready,entry_append] at hcon'
  have hseq := hcon'.seq hmerge
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact hseq.consequence
    (fun _ h => by simpa only [CompactComplexSourceReadyNonleafContraction.ready,entry_append] using h)
    (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPath
