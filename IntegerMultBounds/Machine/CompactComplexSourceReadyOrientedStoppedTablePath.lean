import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedActualTable

/-! Actual stopped control1 reaches the canonical return guard0 after the
forward body and saved-call post orientation. Empty-root branches derive
identity from the real empty saved stack. Every table join is charged. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedTablePath
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexSourceReadyOrientationInvariants (savedSlot)
open CompactComplexSourceReadyOrientedControls (stopped)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyOrientedActualTable (controls classify savedStackSlot)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
variable {s : ℕ}
local notation "RC" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

theorem positive (pcStack : Fin s) : 0<CompactComplexSourceReadyScalarWorkspace.tapes s RC :=
  Nat.zero_lt_of_lt (savedStackSlot pcStack).isLt

def path (headerStack pcStack liveStack : Fin s) :=
  CompactComplexFixedNodePaths.nodePath (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)

private theorem terminal_path (headerStack pcStack liveStack : Fin s)
    (before after : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s RC) 2) (B : ℕ)
    (h : HoareTime (stopped (c:=RC) pcStack).2 (fun w => w=before) (fun w => w=after) B) :
    ∃ t≤B+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1) before t 0 after := by
  apply CompactComplexFixedNodePaths.terminal_control_path (ht:=positive pcStack) (stack:=savedStackSlot pcStack)
    (childReturn:=CompactComplexSourceReadyActualTable.childReturn headerStack liveStack)
    (controls:=controls pcStack) (event:=CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack)
    (isStopped:=classify pcStack) 1 (Or.inl rfl) before after B
  exact h

theorem positive_path (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (dependency : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t 0 ((CompactComplexSourceReadyOrientation.output call beforePost result).append scalar) := by
  dsimp only
  apply terminal_path headerStack pcStack liveStack
  exact CompactComplexSourceReadyOrientedControlsStopped.positive_runs pcStack call sh rows ell p rho dependency right src dst n v scalar older origin hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound


theorem scalar_path (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left levels frames count : ℕ} (dependency : Path sh.active left 0 levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (older : ℤ → Fin 6) (origin : ℤ)
    (hstack : Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v)=
      FiniteReturnStack.bank (FiniteReturnStack.wordPart older origin (CompactComplexCallReturn.code call)
        (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)) le_rfl)
        (origin+CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)))
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n 0))
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^0))+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t 0 ((CompactComplexSourceReadyOrientation.output call beforePost result).append scalar) := by
  dsimp only
  apply terminal_path headerStack pcStack liveStack
  exact CompactComplexSourceReadyOrientedControlsStopped.scalar_runs pcStack call sh rows ell p rho dependency right src dst n v scalar older origin hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound


theorem root_positive_path (headerStack pcStack liveStack : Fin s)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (dependency : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hstack : (ready v).tape (savedSlot pcStack) ((ready v).head (savedSlot pcStack)-1)=blank)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        4)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t 0 (beforePost.append scalar) := by
  dsimp only
  apply terminal_path headerStack pcStack liveStack
  exact CompactComplexSourceReadyOrientedControlsStoppedRoot.positive_runs pcStack sh rows ell p rho dependency right src dst n v scalar hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound


theorem root_scalar_path (headerStack pcStack liveStack : Fin s)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left levels frames count : ℕ} (dependency : Path sh.active left 0 levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s RC) 2)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hstack : (ready v).tape (savedSlot pcStack) ((ready v).head (savedSlot pcStack)-1)=blank)
    (f : CompactSpectatorVisitGeometry.Array (NativePolynomialStageShape.shape sh ell p) rows ell)
    (hG : 0<sh.guard) (hA : 0<sh.axes) (hr : 0<rows) (hp : 2*sh.bits≤p)
    (hw : ∀ i,(f i).1.length=CompactNativeRoleHeaders.recordWidth sh p ∧
      (f i).2.length=CompactNativeRoleHeaders.recordWidth sh p)
    (hraw : Placement.active headerPlacement (base v)=ActiveRepairRankHeadersCommands.bank
      (CompactSpectatorLeafSetup.raw sh rows ell p rho.val left 1 arity right src dst))
    (hsource : v.head (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=0 ∧
      v.tape (CompactComplexSourceReadyLeafPhase.source (s:=10+s))=CompactSpectatorLeafAxis.word f)
    (hlive : v.head CompactComplexNonleafRoleChildBank.current=1 ∧
      v.tape CompactComplexNonleafRoleChildBank.current=RadixZeroFill.encodedBinary (bits n))
    (htarget : v.head CompactComplexNonleafRoleChildBank.target=0 ∧
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))
    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n 0))
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        4)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^0))+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t 0 (beforePost.append scalar) := by
  dsimp only
  apply terminal_path headerStack pcStack liveStack
  exact CompactComplexSourceReadyOrientedControlsStoppedRoot.scalar_runs pcStack sh rows ell p rho dependency right src dst n v scalar hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedTablePath
