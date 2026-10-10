import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedTablePath

/-! Actual positive and scalar stopped roots follow corrected control1 to
the return guard. Their real empty saved stack selects identity, with the
physical leaf, orientation and table transition all paid. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootStoppedTablePath
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

/-- The installed stopped result retains the original empty root guard cell. -/
theorem installed_empty (pcStack : Fin s) (v : Tapes (publicTapes s RC) 2)
    (f : ℤ → Fin 6) (target : ℕ)
    (scalar : Tapes CompactComplexSourceReadyScalarWorkspace.scratch 2)
    (hroot : (ready v).tape (savedSlot pcStack) ((ready v).head (savedSlot pcStack)-1)=blank) :
    ((ready (returned v f target)).append scalar).tape (savedStackSlot pcStack)
      (((ready (returned v f target)).append scalar).head (savedStackSlot pcStack)-1)=blank := by
  have hs := CompactComplexSourceReadyCorrectedStoppedTablePath.installed_saved pcStack v f target scalar
  rw [FiniteReturnStackAt.active_bank,FiniteReturnStackAt.active_bank] at hs
  have he := congrArg (fun z : Tapes 1 2 => z.tape 0 (z.head 0-1)) hs
  exact he.trans hroot

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
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedRootStoppedTablePath
