import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootStoppedTablePath
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedClassifierTablePath
import IntegerMultBounds.Machine.CompactComplexFixedNodeRootExit

/-! The complete actual corrected stopped-root machine classifies its literal
input, computes and installs the genuine leaf, and halts at the empty root
guard. Concrete tape readiness is supplied at entry; no execution callback
or preceding node path is assumed. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedRootRun
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
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
variable {s : ℕ}
local notation "RC" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

open CompactComplexSourceReadyCorrectedFinalTablePath (positive path)

/-- The literal fixed controller is exactly the corrected actual table package. -/
theorem actual_program_eq (headerStack pcStack liveStack : Fin s) :
    CompactComplexSourceReadyCorrectedActualTable.program headerStack pcStack liveStack=
      ⟨_,CompactComplexFixedNodeTable.fixedProgram (positive pcStack) (savedStackSlot pcStack)
        (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
        (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)⟩ := rfl

attribute [local irreducible] CompactComplexFixedNodeTable.fixedProgram

theorem positive_runs (headerStack pcStack liveStack : Fin s)
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
    (hready : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (hstop : ComplexRecursiveCallSchema.stopped sh.axes (k+1)=true)
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
    HoareTime (CompactComplexFixedNodeTable.fixedProgram (positive pcStack) (savedStackSlot pcStack)
      (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
      (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack))
      (fun z => z=((ready v).append scalar)) (fun z => z=(beforePost.append scalar))
      ((CompactComplexSourceReadyGuard.setupCost sh.axes (k+1)+
        CompactComplexSourceReadyGuard.cleanupCost sh.axes (k+1)+7+1)+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1)+2) := by
  dsimp only
  obtain ⟨a,ha,hclass⟩ := CompactComplexSourceReadyCorrectedClassifierTablePath.root_path
    headerStack pcStack liveStack v (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
    (SharedBank.empty 10 2) scalar hstack sh.axes (k+1) hA hready hd
    ⟨hexponentHead,hexponent⟩
  rw [hstop] at hclass
  change path headerStack pcStack liveStack
    (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 0)
    ((ready v).append scalar) a
    (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
    ((ready v).append scalar) at hclass
  obtain ⟨b,hbt,hleaf⟩ := CompactComplexSourceReadyCorrectedRootStoppedTablePath.root_positive_path
    headerStack pcStack liveStack sh rows ell p rho dependency right src dst n v scalar
    hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have hpath := FiniteFlowPath.append hclass hleaf
  have hempty := CompactComplexSourceReadyCorrectedRootStoppedTablePath.installed_empty pcStack v
    (CompactSpectatorLeafAxis.word
      (CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
        rows ell (p-2*sh.bits) rho dependency.visit f))
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)) scalar hstack
  have h := CompactComplexFixedNodeRootExit.path_halts (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    _ _ (a+b) hpath hempty
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)


theorem scalar_runs (headerStack pcStack liveStack : Fin s)
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
    (hready : CompactComplexSourceReadyGuard.Ready v)
    (hd : v.head CompactComplexSourceReadyGuard.dimension=1 ∧
      v.tape CompactComplexSourceReadyGuard.dimension=RadixZeroFill.encodedBinary (bits sh.axes))
    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho dependency.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n 0))
    HoareTime (CompactComplexFixedNodeTable.fixedProgram (positive pcStack) (savedStackSlot pcStack)
      (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
      (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack))
      (fun z => z=((ready v).append scalar)) (fun z => z=(beforePost.append scalar))
      ((CompactComplexSourceReadyGuard.setupCost sh.axes (0)+
        CompactComplexSourceReadyGuard.cleanupCost sh.axes (0)+7+1)+
        (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
          CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(0)))+1)+2) := by
  dsimp only
  have hstop : ComplexRecursiveCallSchema.stopped sh.axes 0=true := by
    rw [ComplexRecursiveCallSchema.stopped_iff]
    exact Or.inl rfl
  obtain ⟨a,ha,hclass⟩ := CompactComplexSourceReadyCorrectedClassifierTablePath.root_path
    headerStack pcStack liveStack v (SharedBank.empty CompactComplexSourceReadyWorkspace.leafTapes 2)
    (SharedBank.empty 10 2) scalar hstack sh.axes (0) hA hready hd
    ⟨hexponentHead,hexponent⟩
  rw [hstop] at hclass
  change path headerStack pcStack liveStack
    (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 0)
    ((ready v).append scalar) a
    (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
    ((ready v).append scalar) at hclass
  obtain ⟨b,hbt,hleaf⟩ := CompactComplexSourceReadyCorrectedRootStoppedTablePath.root_scalar_path
    headerStack pcStack liveStack sh rows ell p rho dependency right src dst n v scalar
    hstack f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have hpath := FiniteFlowPath.append hclass hleaf
  have hempty := CompactComplexSourceReadyCorrectedRootStoppedTablePath.installed_empty pcStack v
    (CompactSpectatorLeafAxis.word
      (CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
        rows ell (p-2*sh.bits) rho dependency.visit f))
    (CompactComplexDenominatorPolicy.leafTarget n (0)) scalar hstack
  have h := CompactComplexFixedNodeRootExit.path_halts (positive pcStack) (savedStackSlot pcStack)
    (CompactComplexSourceReadyActualTable.childReturn headerStack liveStack) (controls pcStack)
    (CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack) (classify pcStack)
    _ _ (a+b) hpath hempty
  exact h.consequence (fun _ h => h) (fun _ h => h) (by omega)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedRootRun
