import IntegerMultBounds.Machine.CompactComplexRolePhaseContinuation
import IntegerMultBounds.Machine.CompactNativeRoleStoppedChildBudget
import IntegerMultBounds.Machine.CompactRecursiveDependencyBudget

/-! A literal recursive Call chooses its real named role, residual child
interval and forward/inverse leaf direction. This executes the stopped child
on the genuine split bank; it does not implement an unstopped recursive call. -/
namespace IntegerMultBounds.Machine.CompactComplexStoppedCallSite
noncomputable section
open CompactComplexRecursiveGeometry
open CompactGadgetReservationShape (Shape)
open CompactRecursiveDependencyBudget (Path)
open Networks.ComplexRecursiveCallSchema (Call)
open CompactComplexRolePhaseSite (roleCount role)
open CompactNativeRoleGuardedChildCaller (leafTapes setRole resultWord)
open CompactNativeRoleStoppedChildCaller (nodeState)
open CompactNativeRoleSourcePorts (callerTapes external)
open CompactSpectatorLeafGuardOriginal (Direction)
variable {s : Shape} {t left k levels frames returned : ℕ}
attribute [local irreducible] Networks.ComplexPhaseBudget.edges

def direction (call : Call) : Direction := if call.inverse then .inverse else .forward

def program (t : ℕ) (call : Call) :=
  CompactNativeRoleStoppedChildCaller.program (direction call) t roleCount (role call.site)

abbrev tapes (t : ℕ) := callerTapes t roleCount+leafTapes

def before (old : Tapes t 2) (ht : 43<t) (rows ell p : ℕ) (rho : Fin s.chunk)
    (path : Path s.active left (k+2) levels frames returned) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (hd : roleCount∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) : Tapes (tapes t) 2 :=
  CleanSubbank.bank (s:=leafTapes) (external old ht
    (nodeState s rows ell p rho (Visit.child path.visit call.slot) hactive pair)
    (CompactNativeRoleReservedBridge.rolePayload s rows roleCount ell hd f))

def after (old : Tapes t 2) (ht : 43<t) (rows ell p : ℕ) (rho : Fin s.chunk)
    (path : Path s.active left (k+2) levels frames returned) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (hd : roleCount∣rows)
    (f : CompactSpectatorVisitGeometry.Array s rows ell) : Tapes (tapes t) 2 :=
  CleanSubbank.bank (s:=leafTapes) (external old ht
    (nodeState s rows ell p rho (Visit.child path.visit call.slot) hactive pair)
    (setRole (CompactNativeRoleReservedBridge.rolePayload s rows roleCount ell hd f) (role call.site)
      (resultWord (direction call) s rows roleCount ell p rho (Visit.child path.visit call.slot) hd f (role call.site))))

/-- The actual Call's role and residual child are executed, with no child
execution callback. All supplied scalar premises are genuine codec invariants. -/
theorem runs (old : Tapes t 2) (ht : 43<t) (rows ell p : ℕ) (rho : Fin s.chunk)
    (path : Path s.active left (k+2) levels frames returned) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (hd : roleCount∣rows)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hp : 2*s.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p) :
    HoareTime (program t call)
      (fun z => z=before old ht rows ell p rho path hactive pair call hd f)
      (fun z => z=after old ht rows ell p rho path hactive pair call hd f)
      (CompactNativeRoleStoppedChildCaller.cost (direction call) roleCount s rows ell p rho
        (Visit.child path.visit call.slot) hactive pair) :=
  CompactNativeRoleStoppedChildCaller.runs (direction call) old ht s rows ell p rho
    (Visit.child path.visit call.slot) hactive pair hd (by decide) hr hG hA hp f hw (role call.site)

/-- Real halted child output enters a fixed continuation in one transition;
the complete stopped-child runtime is charged to its genuine native volume. -/
theorem continuation (old : Tapes t 2) (ht : 43<t) (rows ell p : ℕ) (rho : Fin s.chunk)
    (path : Path s.active left (k+2) levels frames returned) (hactive : s.active≤s.axes)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call) (hd : roleCount∣rows)
    (hr : 0<rows) (hG : 0<s.guard) (hA : 0<s.axes) (hpay : s.payload=1) (hp : 2*s.bits≤p)
    (f : CompactSpectatorVisitGeometry.Array s rows ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth s p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth s p)
    {states : ℕ} (K : Program (tapes t) states 2) (entry : Fin 2) :
    ∃ time,
      CompactComplexRolePhaseContinuation.Block.Reached (program t call) K entry
        (before old ht rows ell p rho path hactive pair call hd f)
        (after old ht rows ell p rho path hactive pair call hd f) time ∧
      time≤CompactNativeRoleStoppedChildBudget.constant roleCount*
        CompactNativeRoleTransferBudget.volume rows s ell p*(arity^(k+1)) := by
  let time := CompactNativeRoleStoppedChildCaller.cost (direction call) roleCount s rows ell p rho
    (Visit.child path.visit call.slot) hactive pair
  refine ⟨time,?_,?_⟩
  · exact CompactComplexRolePhaseContinuation.Block.ready _ K entry _ _ time
      (runs old ht rows ell p rho path hactive pair call hd hr hG hA hp f hw)
  · exact CompactNativeRoleStoppedChildBudget.cost_linear (direction call) roleCount s rows ell p rho
      (Visit.child path.visit call.slot) hactive pair (by decide) hr hd hG hA hpay hp

/-- Once-global padding derives the real role divisor and the next-depth
selected row count. The stopped test is the actual schema's integer test. -/
theorem actual_continuation (m d D G K0 ell q level : ℕ)
    (hDd : D≤d) (hd : 0<d) (hG : 0<G) (hK : 0<K0)
    (hD : CompactGlobalReservation.reservedAxes roleCount m d G K0≤D)
    (hj : level<CompactGlobalRowPadding.depth m d)
    (rho : Fin (CompactReservationNativeRows.shape roleCount m d D G K0).chunk)
    {left k levels frames returned : ℕ}
    (path : Path (CompactReservationNativeRows.shape roleCount m d D G K0).active
      left (k+2) levels frames returned)
    (_hstop : Networks.ComplexRecursiveCallSchema.stopped d (k+1)=true)
    (pair : Networks.BinaryRowProgram.Op (Fin arity)) (call : Call)
    (old : Tapes t 2) (ht : 43<t)
    (f : CompactSpectatorVisitGeometry.Array (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactGlobalRowPadding.rowsAt roleCount m d K0 level) ell)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q) ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth
      (CompactReservationNativeRows.shape roleCount m d D G K0)
      (CompactNativeRoleReservedBridge.precision roleCount m d D K0 q))
    {states : ℕ} (cont : Program (tapes t) states 2) (entry : Fin 2) :
    let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
    let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
    let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
    ∃ (hdiv : roleCount∣rows) (time : ℕ),
      rows/roleCount=CompactGlobalRowPadding.rowsAt roleCount m d K0 (level+1) ∧
      CompactComplexRolePhaseContinuation.Block.Reached (program t call) cont entry
        (before old ht rows ell p rho path ha pair call hdiv f)
        (after old ht rows ell p rho path ha pair call hdiv f) time ∧
      time≤(2*CompactNativeRoleStoppedChildBudget.constant roleCount)*
        CompactFallbackAxisRun.volume D K0 ell q*(arity^(k+1)) := by
  dsimp only
  let sh := CompactReservationNativeRows.shape roleCount m d D G K0
  let rows := CompactGlobalRowPadding.rowsAt roleCount m d K0 level
  let p := CompactNativeRoleReservedBridge.precision roleCount m d D K0 q
  let ha := CompactNativeRoleStoppedChildBudget.actual_active roleCount m d D G K0 hDd
  have hdiv := CompactGlobalRowPadding.split_divides roleCount m d K0 level (by decide) hK hj
  have hr := CompactGlobalRowPadding.rowsAt_positive roleCount m d K0 level (by decide) hK (by omega)
  let time := CompactNativeRoleStoppedChildCaller.cost (direction call) roleCount sh rows ell p rho
    (Visit.child path.visit call.slot) ha pair
  refine ⟨hdiv,time,CompactGlobalRowPadding.next_rows _ _ _ _ _,?_,?_⟩
  · exact CompactComplexRolePhaseContinuation.Block.ready _ cont entry _ _ time
      (runs old ht rows ell p rho path ha pair call hdiv hr hG hd
        (CompactNativeRoleChildPrecision.actual_precision roleCount m d D G K0 q hK hD).1 f hw)
  · exact CompactNativeRoleStoppedChildBudget.actual_cost_linear (direction call)
      roleCount m d D G K0 ell q level hDd (by decide) hd hG hK hD hj rho
      (Visit.child path.visit call.slot) pair

end
end IntegerMultBounds.Machine.CompactComplexStoppedCallSite
