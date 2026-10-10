import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRoleRejoin

/-! Actual root tag3 contracts and rejoins the role payload, then physically
selects identity from the retained empty return stack. Child saved-PC contracts
are not substituted for the root case. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafRootFinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

open CompactComplexSourceReadyNonleafOrientedFinal (program)

theorem runs_native_linear (sh : Shape) (rows ell p : ℕ)
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
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      (contracted (current-target) f) (v.append frame) leaf
    HoareTime (program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p+4) := by
  let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
  let ws := fun j => CompactComplexStoppedGridHandoff.words (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
  let ret := CompactComplexControllerExactReturn.returned ws current target payload
  let v := bank control queue scalar old tail (committed storage target) ret
  let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
    (contracted (current-target) f) (v.append frame) leaf
  have hrun := CompactComplexSourceReadyNonleafFinalPath.raw_runs_native_linear sh rows ell p hc hr hd hgroup
    hG hA hK hP rho left count slots right src dst control queue scalar tail storage payload f hw current target
    hle hcurrent htarget hsource hroles path R base usedRows hb hu hroom frame leaf hlive
  have hfull := CompactComplexSourceReadyOrientedControls.widen_runs hrun scratch
  have hsave := CompactComplexSourceReadyNonleafFinalPorts.saved sh rows ell p rho left count slots right src dst target
    (contracted (current-target) f) control queue scalar old tail storage ret frame leaf pcStack
  have hempty : w.tape (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)
      (w.head (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)-1)=blank := by
    rw [hsave.1,hsave.2]
    exact hroot
  have hpost := CompactComplexSourceReadyOrientation.root_runs
    (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) w hempty
  have hpostFull := CompactComplexSourceReadyOrientedControls.widen_runs hpost scratch
  have hseq := hfull.seq hpostFull
  exact hseq.consequence (fun _ h => h) (fun _ h => h) (by omega)

open CompactSpectatorVisitGeometry (Array)
open CompactNativeRoleRecombine (recombine)
open CompactComplexSourceReadyCorrectedRoleRejoin (payload payload_source payload_roles contracted_recombine)

/-- Root finalization starts directly from the actual completed role family. -/
theorem family_runs_native_linear (sh : Shape) (rows ell p : ℕ)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows) (hgroup : 0<rows/c)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (rho left count slots right src dst : ℕ)
    (control : Tapes 43 2) (queue : Tapes 1 2) (scalar : State) (tail : Tapes 22 2)
    (storage : Tapes (10+s) 2) (data : Fin c → Array sh (rows/c) ell)
    (hw : ∀ j i,(data j i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (data j i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (current target : ℕ) (hle : target≤current)
    (hcurrent : storage.head ⟨7,by omega⟩=1 ∧ storage.tape ⟨7,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits current))
    (htarget : storage.head ⟨8,by omega⟩=1 ∧ storage.tape ⟨8,by omega⟩=
      RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits target))
    {pathLeft pathExponent levels frames returned : ℕ}
    (path : Path sh.active pathLeft pathExponent levels frames returned)
    (R base usedRows : ℕ) (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (frame : Tapes 2 2) (leaf : Tapes CompactComplexSourceReadyWorkspace.leafTapes 2)
    (pcStack : Fin s)
    (hroot : storage.tape (Fin.natAdd 10 pcStack)
      (storage.head (Fin.natAdd 10 pcStack)-1)=blank)
    (scratch : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words (data j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target (payload data))
    let joined := recombine sh rows c ell hd (fun j => contracted (current-target) (data j))
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      joined (v.append frame) leaf
    HoareTime (CompactComplexSourceReadyNonleafOrientedFinal.program pcStack).2
      (fun z => z=(CompactComplexSourceReadyNonleafContraction.ready
        (bank control queue scalar old tail storage (payload data)) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
      (fun z => z=w.append scratch)
      (CompactComplexSourceReadyNonleafFinalPath.constant c*volume rows sh ell p+4) := by
  have h := runs_native_linear sh rows ell p
    hc hr hd hgroup hG hA hK hP rho left count slots right src dst control queue scalar tail storage (payload data)
    (recombine sh rows c ell hd data) (CompactNativeRoleRecombine.width sh rows c ell _ hd data hw)
    current target hle hcurrent htarget (payload_source data) (payload_roles sh rows ell hd data)
    path R base usedRows hb hu hroom frame leaf pcStack hroot scratch hlive
  simp_rw [CompactNativeRoleRecombine.role_recombine] at h
  rw [contracted_recombine] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafRootFinal
