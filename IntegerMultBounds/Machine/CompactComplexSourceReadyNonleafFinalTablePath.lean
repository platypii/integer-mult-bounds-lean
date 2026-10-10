import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafOrientedFinal
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! Actual tag3 body followed by the native final-return edge reaches guard0.
The machine execution is constructed internally from its real tape premises. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalTablePath
noncomputable section
open CompactComplexSourceReadyNonleafOrientedFinal (program constant runs_native_linear)
open CompactComplexFixedNodeTable
open CompactGadgetReservationShape (Shape)
open CompactComplexNativeCodecFrame (bank)
open CompactComplexControllerExactReturn (contracted committed)
open CompactRecursiveDependencyBudget (Path)
open ActiveRepairRankHeadersCommands (State)
open CompactNativeRoleTransferBudget (volume)
variable {s c : ℕ}

private theorem sigma_hoare {t B : ℕ} {P Q : Σ q,Program t q 2} (h : P=Q)
    {v w : Tapes t 2} (hp : HoareTime P.2 (fun z => z=v) (fun z => z=w) B) :
    HoareTime Q.2 (fun z => z=v) (fun z => z=w) B := by cases h; exact hp

theorem tag3_path (sh : Shape) (rows ell p : ℕ)
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
    (hlive : current≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows)
    {N length width : ℕ} (hN : N≤2^width)
    (stack : Fin (CompactComplexSourceReadyScalarWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (ctrl : Fin 4 → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (classify : Fin (ctrl 0).1 → Bool) (hctrl : program pcStack=ctrl 3) :
    let old := CompactSpectatorLeafSetup.raw sh rows ell p rho left count slots right src dst
    let ws := fun j => CompactComplexStoppedGridHandoff.words
      (CompactNativeRoleReservedBridge.role sh rows c ell hd f j)
    let v := bank control queue scalar old tail (committed storage target)
      (CompactComplexControllerExactReturn.returned ws current target payload)
    let w := CompactComplexSourceReadyNonleafFinalPorts.endpoint sh rows ell p rho left count slots right src dst
      (contracted (current-target) f) (v.append frame) leaf
    let blocks := tableProgramsWith returns ctrl events
    let edges := tableEdgesWith returns ctrl events re
      (controlEdgesWith (N:=N) (length:=length) ctrl classify) ee
    ∃ time≤constant c*volume rows sh ell p+1,
      FiniteFlowPath.Path
        (GuardedFiniteReturnExtraFlow.family (k:=width) stack (fun i => (blocks i).1) (fun i => (blocks i).2))
        (GuardedFiniteReturnExtraFlow.next hN (fun i => (blocks i).1) edges)
        (controlPCFor N length 3)
        ((CompactComplexSourceReadyNonleafContraction.ready
          (bank control queue scalar old tail storage payload) (frame.append (SharedBank.empty 7 2)) leaf).append scratch)
        time 0 ((CompactComplexSourceReadyOrientation.output call w (contracted (current-target) f)).append scratch) := by
  have hactual := runs_native_linear sh rows ell p hc hr hd hgroup hG hA hK hP rho left count slots right src dst
    control queue scalar tail storage payload f hw current target hle hcurrent htarget hsource hroles
    path R base usedRows hb hu hroom frame leaf pcStack call older origin hstack scratch hlive
  exact CompactComplexFixedNodePaths.control_local_path hN stack returns ctrl events re
    (controlEdgesWith (N:=N) (length:=length) ctrl classify) ee 3 0 _ _ _
    (sigma_hoare hctrl hactual) (final_return_edge ctrl classify)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafFinalTablePath
