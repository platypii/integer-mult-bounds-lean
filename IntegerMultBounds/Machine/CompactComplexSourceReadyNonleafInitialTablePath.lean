import IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafTargetSplit
import IntegerMultBounds.Machine.CompactComplexFixedNodePaths

/-! The actual target-and-current-row-split block takes the real nonleaf setup
edge to the first original event, with its execution and edge both paid. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafInitialTablePath
noncomputable section
open CompactComplexSourceReadyNonleafTargetSplit
open CompactComplexFixedNodeTable
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexSourceReadyWorkspace (publicTapes ready)
open CompactComplexSourceReadyNonleafTarget (targeted)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

/-- First original event, or finalization when the event sequence is empty. -/
def firstEventPC (N length : ℕ) : Fin (N+(4+length)+2) :=
  if h : 0<length then GuardedFiniteReturnExtraFlow.extraPC (Fin.natAdd 4 (⟨0,h⟩ : Fin length))
  else controlPCFor N length 3

private theorem sigma_hoare {t B : ℕ} {P Q : Σ q,Program t q 2} (h : P=Q)
    {v w : Tapes t 2} (hp : HoareTime P.2 (fun z => z=v) (fun z => z=w) B) :
    HoareTime Q.2 (fun z => z=v) (fun z => z=w) B := by cases h; exact hp

theorem tag2_path (sh : Shape) (rows ell p : ℕ)
    (rho : Fin sh.chunk) (left k right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hn : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (ht : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=fun _ => blank)
    (hc : 0<c) (hr : 0<rows) (hd : c ∣ rows)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hK : 0<sh.chunk) (hP : 2*sh.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hi : Placement.active CompactComplexNonleafRoleSplit.placement v=
      CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst)
        (CompactNativeRoleReservedBridge.sourcePayload sh rows ell f c))
    {levels frames returned : ℕ}
    (path : CompactRecursiveDependencyBudget.Path sh.active left (k+1) levels frames returned)
    (R baseline usedRows : ℕ) (hb : baseline≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R baseline levels frames returned usedRows)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    {N length width : ℕ} (hN : N≤2^width)
    (stack : Fin (CompactComplexSourceReadyScalarWorkspace.tapes s c))
    (returns : Fin N → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (ctrl : Fin 4 → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (events : Fin length → Σ q,Program (CompactComplexSourceReadyScalarWorkspace.tapes s c) q 2)
    (re : ∀ pc,Fin (returns pc).1 → Option (Fin (N+(4+length)+2)))
    (ee : ∀ pc,Fin (events pc).1 → Option (Fin (N+(4+length)+2)))
    (classify : Fin (ctrl 0).1 → Bool) (hctrl : fullProgram (s:=s) (c:=c)=ctrl 2) :
    let w := ready (Placement.replace CompactComplexNonleafRoleSplit.placement
      (targeted v (n+2*arity^(k+1)))
      (CompactNativeRoleOriginal.bank
        (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst)
        (CompactNativeRoleReservedBridge.rolePayload sh rows c ell hd f)))
    let blocks := tableProgramsWith returns ctrl events
    let edges := tableEdgesWith returns ctrl events re
      (controlEdgesWith (N:=N) (length:=length) ctrl classify) ee
    ∃ time≤constant c*CompactNativeRoleTransferBudget.volume rows sh ell p+1,
      FiniteFlowPath.Path
        (GuardedFiniteReturnExtraFlow.family (k:=width) stack (fun i => (blocks i).1) (fun i => (blocks i).2))
        (GuardedFiniteReturnExtraFlow.next hN (fun i => (blocks i).1) edges)
        (controlPCFor N length 2) ((ready v).append scalar)
        time (firstEventPC N length) (w.append scalar) := by
  have hactual := runs_native_linear sh rows ell p rho left k right src dst n v hraw hn ht
    hc hr hd hG hA hK hP f hw hi path R baseline usedRows hb hu hroom hlive
  have hfull := widen_runs hactual scalar
  exact CompactComplexFixedNodePaths.control_local_path hN stack returns ctrl events re
    (controlEdgesWith (N:=N) (length:=length) ctrl classify) ee 2 (firstEventPC N length) _ _ _
    (sigma_hoare hctrl hfull) (fun _ => rfl)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyNonleafInitialTablePath
