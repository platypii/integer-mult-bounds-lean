import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedInstalledResult
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedFinalTablePath

/-! The genuine stopped tag1 installs its oriented result and reaches guard0
inside the corrected table. The same saved-PC bank remains available for pop. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedTablePath
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexSourceReadyOrientationInvariants (savedSlot oriented)
open CompactComplexSourceReadyOrientedControls (stopped)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
open CompactComplexSourceReadyScalarWorkspace (roles)
open CompactComplexSourceReadyCorrectedActualTable (controls classify savedStackSlot)
open CompactComplexScheduledPCLayout (originalCount)
open CompactComplexCompletedLiveLower (schedule)
open CompactComplexSourceReadyCorrectedFinalTablePath (positive path)
variable {s : ℕ}
local notation "RC" => CompactComplexSourceReadyScalarWorkspace.roles
attribute [local irreducible] ComplexRank25.program ComplexRecursiveCallSchema.sites schedule
  CompactComplexRolePhaseSite.roleCount CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

private theorem terminal_path (headerStack pcStack liveStack : Fin s)
    (before after : Tapes (CompactComplexSourceReadyScalarWorkspace.tapes s RC) 2) (B : ℕ)
    (h : HoareTime (stopped (c:=RC) pcStack).2 (fun w => w=before) (fun w => w=after) B) :
    ∃ time≤B+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1) before time 0 after := by
  apply CompactComplexFixedNodePaths.terminal_control_path
    (ht:=positive pcStack) (stack:=savedStackSlot pcStack)
    (childReturn:=CompactComplexSourceReadyActualTable.childReturn headerStack liveStack)
    (controls:=controls pcStack)
    (event:=CompactComplexSourceReadyActualTable.event headerStack pcStack liveStack)
    (isStopped:=classify pcStack) 1 (Or.inl rfl) before after B
  exact h

/-- The literal installed bank retains its original saved return frame. -/
theorem installed_saved (pcStack : Fin s)
    (v : Tapes (publicTapes s RC) 2) (f : ℤ → Fin 6) (target : ℕ)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2) :
    Placement.active (FiniteReturnStackAt.placement (savedStackSlot pcStack))
      ((ready (returned v f target)).append scalar)=
      Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v) := by
  rw [CompactComplexSourceReadyCorrectedActualTable.savedStackSlot_eq,
    FiniteReturnStackAt.active_bank]
  simp only [Tapes.append,Fin.addCases_left]
  rw [←FiniteReturnStackAt.active_bank]
  exact CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack v f target

theorem positive_path_installed (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
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
    let result := CompactSpectatorLeafGuardOriginal.result .forward sh
      rows ell (p-2*sh.bits) rho dependency.visit f
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1,path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t 0 ((ready (returned v (CompactSpectatorLeafAxis.word (oriented call result))
        (CompactComplexDenominatorPolicy.leafTarget n (k+1)))).append scalar) := by
  have hactual := CompactComplexSourceReadyOrientedControlsStopped.positive_runs
    pcStack call sh rows ell p rho dependency right src dst n v scalar older origin hstack f
    hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have h := terminal_path headerStack pcStack liveStack _ _ _ hactual
  dsimp only at h ⊢
  rw [CompactComplexSourceReadyStoppedInstalledResult.oriented_endpoint] at h
  rw [CompactComplexSourceReadyStoppedInstalledResult.polynomial_leaf_result
    sh rows ell p rho dependency.visit f] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedTablePath
