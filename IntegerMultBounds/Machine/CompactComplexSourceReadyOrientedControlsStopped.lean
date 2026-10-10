import IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsFrame
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatchBudget

/-! The stopped control executes the actual complete forward leaf body and
then reads the same retained saved frame for post-conjugation, before pop. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStopped
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
open SharedPlacementAlphabet (setTape)
variable {s c : ℕ}
attribute [local irreducible] CompactComplexSourceReadyDirection.width
  CompactComplexSourceReadyStoppedLeafDispatchBudget.constant

def publicSaved (pcStack : Fin s) : Fin (publicTapes s c) :=
  CompactComplexNonleafRoleChildBank.storage (Fin.natAdd 10 pcStack)

private theorem publicSaved_ne (pcStack : Fin s) :
    publicSaved (c:=c) pcStack≠CompactComplexSourceReadyLeafPhase.source (s:=10+s) ∧
    publicSaved (c:=c) pcStack≠CompactComplexNonleafRoleChildBank.current ∧
    publicSaved (c:=c) pcStack≠CompactComplexNonleafRoleChildBank.target := by
  constructor
  · intro he
    have hv := congrArg Fin.val he
    simp only [publicSaved,CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
      CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
      CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
      CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
    omega
  · constructor
    all_goals intro he; have hv := congrArg Fin.val he
    all_goals simp only [publicSaved,CompactComplexNonleafRoleChildBank.current,
      CompactComplexNonleafRoleChildBank.target,CompactComplexNonleafRoleChildBank.storage,
      CompactComplexSpectatorTargetBank.oldSlot,CompactComplexControllerNativeFrame.storageSlot,
      Fin.val_castAdd,Fin.val_natAdd] at hv
    all_goals omega

private theorem source_ne :
    CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠CompactComplexNonleafRoleChildBank.current (s:=s) ∧
    CompactComplexSourceReadyLeafPhase.source (s:=10+s) (c:=c)≠CompactComplexNonleafRoleChildBank.target (s:=s) := by
  constructor
  all_goals intro he; have hv := congrArg Fin.val he
  all_goals simp only [CompactComplexSourceReadyLeafPhase.source,CompactComplexNonleafRoleEntry.source,
    CompactComplexNonleafRoleChildBank.current,CompactComplexNonleafRoleChildBank.target,
    CompactComplexNonleafRoleChildBank.storage,CompactComplexSpectatorTargetBank.oldSlot,
    CompactComplexSpectatorTargetBank.numericSlot,CompactComplexControllerNativeFrame.nativeSlot,
    CompactComplexControllerNativeFrame.storageSlot,Fin.val_castAdd,Fin.val_natAdd] at hv
  all_goals omega

theorem returned_saved (pcStack : Fin s) (v : Tapes (publicTapes s c) 2) (f : ℤ → Fin 6) (n : ℕ) :
    Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready (returned v f n))=
      Placement.active (FiniteReturnStackAt.placement (savedSlot pcStack)) (ready v) := by
  obtain ⟨hs,hc,ht⟩ := publicSaved_ne (c:=c) pcStack
  simp only [publicSaved] at hs hc ht
  rw [FiniteReturnStackAt.active_bank,FiniteReturnStackAt.active_bank]
  simp only [savedSlot,ready,CompactComplexSourceReadyLeafPhase.ready,
    Tapes.append,Fin.addCases_left,returned,setTape,Function.update_of_ne hs,
    Function.update_of_ne hc,Function.update_of_ne ht]

theorem returned_source {sh : Shape} {rows ell : ℕ} (v : Tapes (publicTapes s c) 2)
    (f : CompactSpectatorVisitGeometry.Array sh rows ell) (n : ℕ) :
    (ready (returned v (CompactSpectatorLeafAxis.word f) n)).tape CompactComplexSourceReadyOrientation.source=
      NativeZeroPadding.word (NativeZeroPaddingArray.word f) ∧
    (ready (returned v (CompactSpectatorLeafAxis.word f) n)).head CompactComplexSourceReadyOrientation.source=0 := by
  obtain ⟨hc,ht⟩ := source_ne (s:=s) (c:=c)
  simp only [CompactComplexSourceReadyLeafPhase.source] at hc ht
  simp only [CompactComplexSourceReadyOrientation.source,NativePolynomialConjugationWorkspace.source,
    ready,CompactComplexSourceReadyLeafPhase.ready,Tapes.append,Fin.addCases_left,returned,setTape,
    CompactComplexSourceReadyLeafPhase.source,
    Function.update_of_ne hc,Function.update_of_ne ht,Function.update_self]
  exact ⟨rfl,True.intro⟩

private theorem paid (F O V A : ℕ) (hV : 0<V) (hA : 0<A) : F*V*A+1+O*V≤(F+O+1)*V*A := by
  have hm := Nat.le_mul_of_pos_right (O*V) hA
  have hv : 1≤V*A := Nat.succ_le_of_lt (Nat.mul_pos hV hA)
  nlinarith

theorem positive_runs (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k levels frames count : ℕ} (path : Path sh.active left (k+1) levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s c) 2)
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
      rows ell (p-2*sh.bits) rho path.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
    HoareTime (stopped (c:=c) pcStack).2 (fun w => w=(ready v).append scalar)
      (fun w => w=(CompactComplexSourceReadyOrientation.output call beforePost result).append scalar)
      ((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
        CompactNativeRoleTransferBudget.volume rows sh ell p*(arity^(k+1))) := by
  dsimp only
  let result := CompactSpectatorLeafGuardOriginal.result .forward (NativePolynomialStageShape.shape sh ell p)
    rows ell (p-2*sh.bits) rho path.visit f
  let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n (k+1)))
  have hf := CompactComplexSourceReadyStoppedLeafDispatchBudget.positive_runs_linear .forward sh rows ell p rho
    path right src dst n v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
    R basePrecision usedRows hpay hright hsrc hdst hb hu hroom hliveBound
  have hs := returned_source v result (CompactComplexDenominatorPolicy.leafTarget n (k+1))
  have hsave := (returned_saved pcStack v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n (k+1))).trans hstack
  have hwout := CompactComplexSourceReadyLeafSemantics.result_width .forward rows ell p rho path.visit hp f hw
  have hpst := CompactComplexSourceReadyOrientationInvariants.runs_linear (savedSlot pcStack) call beforePost older origin
    hsave sh rows ell p hr result hwout hs.1 hs.2
  have h := hoare_extend_eq (hf.seq hpst) scalar
  apply h.consequence (fun _ h => h) (fun _ h => h)
  exact paid _ _ _ _ (Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p))
    (pow_pos (by decide) _)

theorem scalar_runs (pcStack : Fin s) (call : ComplexRecursiveCallSchema.Call)
    (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left levels frames count : ℕ} (path : Path sh.active left 0 levels frames count)
    (right src dst n : ℕ) (v : Tapes (publicTapes s c) 2)
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
      rows ell (p-2*sh.bits) rho path.visit f
    let beforePost := ready (returned v (CompactSpectatorLeafAxis.word result)
      (CompactComplexDenominatorPolicy.leafTarget n 0))
    HoareTime (stopped (c:=c) pcStack).2 (fun w => w=(ready v).append scalar)
      (fun w => w=(CompactComplexSourceReadyOrientation.output call beforePost result).append scalar)
      ((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+
        CompactComplexSourceReadyOrientationInvariants.constant+1)*
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
  have hs := returned_source v result (CompactComplexDenominatorPolicy.leafTarget n 0)
  have hsave := (returned_saved pcStack v (CompactSpectatorLeafAxis.word result)
    (CompactComplexDenominatorPolicy.leafTarget n 0)).trans hstack
  have hwout := CompactComplexSourceReadyLeafSemantics.result_width .forward rows ell p rho path.visit hp f hw
  have hpst := CompactComplexSourceReadyOrientationInvariants.runs_linear (savedSlot pcStack) call beforePost older origin
    hsave sh rows ell p hr result hwout hs.1 hs.2
  have h := hoare_extend_eq (hf.seq hpst) scalar
  apply h.consequence (fun _ h => h) (fun _ h => h)
  exact paid _ _ _ _ (Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p))
    (by decide : 0<1)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyOrientedControlsStopped
