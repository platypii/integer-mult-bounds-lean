import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalPorts
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControls

/-! Actual widened tag3 executes all-role contraction, current-row merging,
and the real saved-call post-orientation selector before returning to guard0. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

def program (pcStack : Fin s) : Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2 :=
  ⟨_,CompactComplexSourceReadyOrientedControls.finish pcStack
    (CompactComplexSourceReadyOrientedControls.widen (CompactComplexSourceReadyNonleafFinalPath.program (s:=s) (c:=c)).2)⟩
def constant (c : ℕ) := CompactComplexSourceReadyNonleafFinalPath.constant c+
  CompactComplexSourceReadyOrientationInvariants.constant+1

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
    (pcStack : Fin s) (call : Networks.ComplexRecursiveCallSchema.Call) (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : FiniteReturnStack.bank (storage.tape (Fin.natAdd 10 pcStack)) (storage.head (Fin.natAdd 10 pcStack))=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)))
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
      (fun z => z=(CompactComplexSourceReadyOrientation.output call w (contracted (current-target) f)).append scratch)
      (constant c*volume rows sh ell p) := by
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
  have hsrc := CompactComplexSourceReadyNonleafFinalPorts.source sh rows ell p rho left count slots right src dst
    (contracted (current-target) f) (v.append frame) leaf
  have hsave := CompactComplexSourceReadyNonleafFinalPorts.saved sh rows ell p rho left count slots right src dst target
    (contracted (current-target) f) control queue scalar old tail storage ret frame leaf pcStack
  have hsaved : Placement.active (FiniteReturnStackAt.placement (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack)) w=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth Networks.ComplexRecursiveCallSchema.sites.length (25^3)) := by
    rw [FiniteReturnStackAt.active_bank]
    change FiniteReturnStack.bank (w.tape _) (w.head _)=_
    rw [hsave.1,hsave.2]
    exact hstack
  have hpost := CompactComplexSourceReadyOrientationInvariants.runs_linear
    (CompactComplexSourceReadyOrientationInvariants.savedSlot pcStack) call w older origin hsaved sh rows ell p hr
    (contracted (current-target) f) (CompactComplexSourceReadyNonleafFinalGeometry.contracted_width _ f hw) hsrc.1 hsrc.2
  have hpostFull := CompactComplexSourceReadyOrientedControls.widen_runs hpost scratch
  have hseq := hfull.seq hpostFull
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact hseq.consequence (fun _ h => h) (fun _ h => h) (by unfold constant; nlinarith)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
