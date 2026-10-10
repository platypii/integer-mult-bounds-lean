import IntegerMultBounds.Machine.CompactComplexNativeRoleBridge
import IntegerMultBounds.Machine.CompactComplexStoppedCallSite

/-! Actual stopped Call execution on the controller/native65 bank. The exact
raw codec headers and genuine once-padded pre-split rows are tracked explicitly;
installation of ell/precision into an initial13 controller bank remains separate. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedCallFrame
noncomputable section
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactComplexRolePhaseSite (roleCount role)
open CompactComplexNativeRoleBridge (bank publicTapes)
open CompactNativeRoleGuardedChildCaller (leafTapes resultWord)
open Networks.ComplexRecursiveCallSchema (Call)
variable {s : ℕ}
attribute [local irreducible] Networks.ComplexPhaseBudget.edges

abbrev privateTapes := CompactNativeRoleSourcePorts.callerTapes 44 roleCount+leafTapes
abbrev tapes (s : ℕ) := publicTapes s roleCount+privateTapes

def program (s : ℕ) (call : Call) :=
  CompactComplexNativeRoleBridge.stoppedProgram (CompactComplexStoppedCallSite.direction call) s (role call.site)

/-- Divisor, row level, precision guard and complete physical execution are
derived for the actual stopped child. No copy or child execution is supplied. -/
theorem actual_runs (m d D G K0 ell q level : ℕ)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (_hstop : Networks.ComplexRecursiveCallSchema.stopped d (k+1)=true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (control : Tapes 43 2) (queue : Tapes 1 2) (tail : Tapes 22 2) (storage : Tapes s 2)
    (f : CompactSpectatorVisitGeometry.Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q)) :
    let sh := CompactReservationNativeRows.shape roleCount m d D G K0
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    let visit := Visit.child path.visit call.slot
    let dir := CompactComplexStoppedCallSite.direction call
    let st := CompactNativeRoleStoppedChildCaller.nodeState sh rows ell p rho visit ha pair
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      let payload := CompactNativeRoleReservedBridge.rolePayload sh rows roleCount ell hdiv f
      let v := bank control queue st tail storage payload
      let g := resultWord dir sh rows roleCount ell p rho visit hdiv f (role call.site)
      let before := CleanSubbank.bank (s:=privateTapes) v
      let after := CleanSubbank.bank (s:=privateTapes)
        (SharedPlacementAlphabet.setTape v (CompactComplexNativeRoleBridge.roleSlot (role call.site)) g 0)
      rows/roleCount=CompactGlobalRowPadding.rowsAt roleCount m d K0 (level+1) ∧
      HoareTime (program s call) (fun z => z=before) (fun z => z=after) time ∧
      time≤(2*CompactNativeRoleStoppedChildBudget.constant roleCount)*
        CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) ∧
      ∀ (states : ℕ) (cont : Program (tapes s) states 2) (entry : Fin 2),
        CompactComplexRolePhaseContinuation.Block.Reached (program s call) cont entry before after time := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  let visit := Visit.child path.visit call.slot
  let dir := CompactComplexStoppedCallSite.direction call
  have hdiv := CompactGlobalRowPadding.split_divides roleCount m d K0 level (by decide) hK hj
  have hr := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by decide) hK (by omega)
  let time := CompactNativeRoleStoppedChildCaller.cost dir roleCount sh rows ell p rho visit ha pair
  have hrun := CompactComplexNativeRoleBridge.stopped_runs dir control queue tail storage sh rows ell p rho visit ha
    pair hdiv (by decide) hr hG hd (CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD).1
    f hw (role call.site)
  refine ⟨hdiv,time,CompactGlobalRowPadding.next_rows _ _ _ _ _,hrun,?_,?_⟩
  · exact CompactNativeRoleStoppedChildBudget.actual_cost_linear dir roleCount m d D G K0 ell q level
      hDd (by decide) hd hG hK hD hj rho visit pair
  · intro states cont entry
    exact CompactComplexRolePhaseContinuation.Block.ready _ cont entry _ _ time hrun

end
end IntegerMultBounds.Machine.CompactComplexStoppedCallFrame
