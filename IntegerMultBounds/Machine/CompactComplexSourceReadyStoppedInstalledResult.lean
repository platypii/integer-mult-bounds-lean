import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedSemantics
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedReturnPrefix
import IntegerMultBounds.Machine.CompactComplexSourceReadyInstalledPayload
import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedStoppedTablePath

/-! Literal reached stopped endpoints identify the genuine installed oriented
leaf result, including polynomial-shape transport and exact restored caller
source. The numerical prefix is proved separately on that same result. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedInstalledResult
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactSpectatorVisitGeometry (Array)
open CompactComplexRecursiveGeometry (Visit arity)
open CompactComplexSourceReadyOrientationInvariants (oriented)
open CompactComplexSourceReadyStoppedLeaf (ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}

/-- The physical polynomial leaf uses the original exact array operation. -/
theorem polynomial_leaf_result (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk) {left k : ℕ}
    (visit : Visit sh.active left k) (f : Array sh rows ell) :
    CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
      rows ell (p-2*sh.bits) rho visit f=
    CompactSpectatorLeafGuardOriginal.result .forward sh rows ell (p-2*sh.bits) rho visit f := by
  have hr (t : ℕ) : CompactSpectatorLeafLoop.run (NativePolynomialStageShape.shape sh ell p)
      rows ell (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits)) rho visit t f=
      CompactSpectatorLeafLoop.run sh rows ell (ButterflyIndependentGuardHeaders.reservation sh.bits (p-2*sh.bits))
        rho visit t f := by
    induction t with
    | zero => rfl
    | succ t ih =>
      simp only [CompactSpectatorLeafLoop.run]
      split_ifs
      · rw [ih]
        rfl
      · exact ih
  exact hr _

private theorem source_ne : CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠
      CompactComplexNonleafRoleChildBank.current (s:=s) ∧
    CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠
      CompactComplexNonleafRoleChildBank.target (s:=s) := by
  constructor <;> intro h <;> have hv := congrArg Fin.val h
  all_goals simp only [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
    CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals omega

/-- Post-orientation yields another literal stopped returned bank, retaining
all caller cells and frames except the source and genuine live/target ports. -/
theorem oriented_endpoint {sh : Shape} {rows ell : ℕ}
    (call : Networks.ComplexRecursiveCallSchema.Call)
    (v : Tapes (CompactComplexSourceReadyStoppedLeaf.publicTapes s c) 2)
    (f : Array sh rows ell) (target : ℕ) :
    CompactComplexSourceReadyOrientation.output call
      (ready (returned v (CompactSpectatorLeafAxis.word f) target)) f=
      ready (returned v (CompactSpectatorLeafAxis.word (oriented call f)) target) := by
  have hs := CompactComplexSourceReadyOrientedControlsStopped.returned_source v f target
  rw [CompactComplexSourceReadyOrientationInvariants.output_eq call _ f hs.1 hs.2]
  have hslot : CompactComplexSourceReadyOrientation.source (s:=s) (c:=c)=
      Fin.castAdd 10 (Fin.castAdd CompactComplexSourceReadyWorkspace.leafTapes
        (CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c))) := by
    apply Fin.ext
    rfl
  rw [hslot]
  unfold ready CompactComplexSourceReadyLeafPhase.ready
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]
  apply congrArg (fun z : Tapes (CompactComplexSourceReadyStoppedLeaf.publicTapes s c) 2 => (z.append (SharedBank.empty CompactComplexSourceReadyLeafPhase.privateTapes 2)).append
    (SharedBank.empty 10 2))
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals by_cases hi : i=CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)
  all_goals simp [returned,setTape,Function.update_apply,hi,source_ne.1,source_ne.2,
    CompactSpectatorLeafAxis.word,NativeZeroPadding.word,NativeZeroPaddingArray.word,ButterflyStreamData.full]

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

open CompactComplexSourceReadyOrientedStoppedTablePath (path)
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
  have h := CompactComplexSourceReadyOrientedStoppedTablePath.positive_path headerStack pcStack liveStack
    call sh rows ell p rho dependency right src dst n v scalar older origin hstack f hG hA hr hp hw hraw hsource
    hlive htarget hexponent hexponentHead R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  dsimp only at h ⊢
  rw [oriented_endpoint] at h
  rw [polynomial_leaf_result sh rows ell p rho dependency.visit f] at h
  exact h

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedInstalledResult
