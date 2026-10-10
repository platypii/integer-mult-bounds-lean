import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedTablePath
import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedSavedReturnPath

/-! The genuine stopped branch installs its oriented result, then physically pops
the retained saved frame and reaches the original saved call continuation.
Its exact time includes the stopped depth factor and the actual guard/pop. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedReturnPath
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

open SharedPlacementAlphabet (setTape)

theorem return_path (headerStack pcStack liveStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
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
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames count usedRows)
    (hblankTail : ∀ z,origin≤z → older z=blank) :
    let result := CompactSpectatorLeafGuardOriginal.result .forward sh
      rows ell (p-2*sh.bits) rho dependency.visit f
    ∃ t≤((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5),path headerStack pcStack liveStack
      (CompactComplexFixedNodeTable.controlPCFor originalCount schedule.length 1)
      ((ready v).append scalar) t (CompactComplexScheduledPCDecode.savedPC call)
      (setTape ((ready (returned v (CompactSpectatorLeafAxis.word (oriented call result))
        (CompactComplexDenominatorPolicy.leafTarget n (k+1)))).append scalar)
        (savedStackSlot pcStack) older origin) := by
  let result := CompactSpectatorLeafGuardOriginal.result .forward sh
    rows ell (p-2*sh.bits) rho dependency.visit f
  let installed := returned v (CompactSpectatorLeafAxis.word (oriented call result))
    (CompactComplexDenominatorPolicy.leafTarget n (k+1))
  let out := (ready installed).append scalar
  obtain ⟨time,ht,hpath⟩ := CompactComplexSourceReadyCorrectedStoppedTablePath.positive_path_installed
    headerStack pcStack liveStack call sh rows ell p rho dependency right src dst n v scalar older origin hstack f
    hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have hsaved := CompactComplexSourceReadyCorrectedStoppedTablePath.installed_saved pcStack v
    (CompactSpectatorLeafAxis.word (oriented call result))
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)) scalar
  rw [FiniteReturnStackAt.active_bank] at hsaved
  have hreturn := CompactComplexSourceReadyCorrectedSavedReturnPath.full_return_path
    headerStack pcStack liveStack call out older origin (hsaved.trans hstack) hblankTail
  refine ⟨time+(CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5),
    Nat.add_le_add_right ht _,?_⟩
  dsimp only [CompactComplexSourceReadyCorrectedFinalTablePath.path,
    CompactComplexSourceReadyCorrectedSavedReturnPath.path,CompactComplexFixedNodePaths.nodePath]
    at hpath hreturn ⊢
  exact FiniteFlowPath.append hpath hreturn

private theorem paid_return (C W V D : ℕ) (hV : 0<V) (hD : 0<D) :
    C*V*D+1+(W+5)≤(C+W+6)*V*D := by
  have hpaid : W+6≤(W+6)*(V*D) := by
    simpa only [Nat.mul_one] using Nat.mul_le_mul_left (W+6) (Nat.mul_pos hV hD)
  calc
    C*V*D+1+(W+5)=C*(V*D)+(W+6) := by ring
    _≤C*(V*D)+(W+6)*(V*D) := Nat.add_le_add_left hpaid _
    _=(C+W+6)*V*D := by ring

/-- The stopped depth factor is retained when absorbing the actual return cost. -/
theorem cost_bound (rows ell p k : ℕ) (hr : 0<rows) (sh : Shape) :
    ((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)))+1+
      (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+5)≤
      (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1+
        CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3)+6)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1)) := by
  have hV : 0<CompactNativeRoleTransferBudget.volume rows sh ell p :=
    Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  exact paid_return
    (CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
      CompactComplexSourceReadyOrientationInvariants.constant+1)
    (CompactComplexCallReturn.addressWidth ComplexRecursiveCallSchema.sites.length (25^3))
    (CompactNativeRoleTransferBudget.volume rows sh ell p) (arity^(k+1)) hV
    (Nat.pow_pos (by unfold arity; omega))

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedReturnPath
