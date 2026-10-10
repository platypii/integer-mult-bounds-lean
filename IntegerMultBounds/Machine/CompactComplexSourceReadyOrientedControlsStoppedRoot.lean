import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStopped

/-! Empty roots execute the true forward stopped body and the same physical
post selector, whose retained empty stack chooses literal identity. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedRoot
noncomputable section
open Networks
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexSourceReadyOrientationInvariants (savedSlot)
open CompactComplexSourceReadyOrientedControls (stopped nodeStopped orientation)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

private theorem paid (F O V A : ℕ) (hV : 0<V) (hA : 0<A) : F*V*A+1+O*V≤(F+O+1)*V*A := by
  have hm := Nat.le_mul_of_pos_right (O*V) hA
  have hv : 1≤V*A := Nat.succ_le_of_lt (Nat.mul_pos hV hA)
  nlinarith

theorem root_post (pcStack : Fin s) (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ)
    (hb : (ready v).tape (savedSlot pcStack) ((ready v).head (savedSlot pcStack)-1)=blank) :
    HoareTime (orientation (c:=c) pcStack) (fun w => w=ready (returned v f n))
      (fun w => w=ready (returned v f n)) 3 := by
  have hs := CompactComplexSourceReadyOrientedControlsStopped.returned_saved pcStack v f n
  rw [FiniteReturnStackAt.active_bank,FiniteReturnStackAt.active_bank] at hs
  have ht := congrArg (fun b : Tapes 1 2 => b.tape 0) hs
  have hh := congrArg (fun b : Tapes 1 2 => b.head 0) hs
  simp only [FiniteReturnStack.bank] at ht hh
  apply CompactComplexSourceReadyOrientation.root_runs
  rw [ht,hh]
  exact hb

theorem positive_runs (pcStack : Fin s)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (path : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s c) 2)
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
      rows ell (p-2*sh.bits) rho path.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
    HoareTime (stopped (c:=c) pcStack).2 (fun w => w=(ready v).append scalar)
      (fun w => w=beforePost.append scalar)
      ((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        4)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1))) := by
  dsimp only
  let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
    rows ell (p-2*sh.bits) rho path.visit f
  let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
  have hf := CompactComplexSourceReadyStoppedLeafDispatchBudget.positive_runs_linear .forward sh rows ell p rho
    path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have hpst := root_post pcStack v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)) hstack
  have hpst' := hpst.consequence (fun _ h => h) (fun _ h => h)
    (show 3≤3*CompactNativeRoleTransferBudget.volume rows sh ell p from by
      have hv := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
      change 0<CompactNativeRoleTransferBudget.volume rows sh ell p at hv
      omega)
  have h := hoare_extend_eq (hf.seq hpst') scalar
  apply h.consequence (fun _ h => h) (fun _ h => h)
  exact paid _ _ _ _ (Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p))
    (pow_pos (by decide) _)

theorem scalar_runs (pcStack : Fin s)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left levels frames count : ℕ} (path : Path sh.active left 0 levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s c) 2)
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
      rows ell (p-2*sh.bits) rho path.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n 0))
    HoareTime (stopped (c:=c) pcStack).2 (fun w => w=(ready v).append scalar)
      (fun w => w=beforePost.append scalar)
      ((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        4)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^0)) := by
  dsimp only
  let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
    rows ell (p-2*sh.bits) rho path.visit f
  let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n 0))
  have hf := CompactComplexSourceReadyStoppedLeafDispatchBudget.scalar_runs_linear .forward sh rows ell p rho
    path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  rw [CompactComplexSourceReadyStoppedLeaf.output_eq_ready] at hf
  have hpst := root_post pcStack v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n 0) hstack
  have hpst' := hpst.consequence (fun _ h => h) (fun _ h => h)
    (show 3≤3*CompactNativeRoleTransferBudget.volume rows sh ell p from by
      have hv := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
      change 0<CompactNativeRoleTransferBudget.volume rows sh ell p at hv
      omega)
  have h := hoare_extend_eq (hf.seq hpst') scalar
  apply h.consequence (fun _ h => h) (fun _ h => h)
  exact paid _ _ _ _ (Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p))
    (by decide : 0<1)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStoppedRoot
