import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatch
import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCountBudget

/-! One fixed runtime exponent dispatcher pays all positive count traffic,
scalar execution and branch overhead from the true Path and input live ledger. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatchBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactComplexSourceReadyStoppedLeaf (publicTapes ready)
open CompactComplexSourceReadyStoppedLeafCount (returned)
open CompactComplexNonleafRoleSourceReturn (base)
open CompactComplexNonleafRoleEntry (headerPlacement)
open RecursiveChildQuotientsConstant (bits)
variable {s c : ℕ}

def constant := CompactComplexSourceReadyStoppedLeafCountBudget.constant+1

theorem positive_runs_linear (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left k : ℕ} {levels frames returned : ℕ} (path : Path sh.active left (k+1) levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
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
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits (k+1)))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows) :
    HoareTime (CompactComplexSourceReadyStoppedLeafDispatch.program dir) (fun z => z=ready v)
      (fun z => z=ready (CompactComplexSourceReadyStoppedLeafCount.returned v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n (k+1))))
      (constant*volume rows sh ell p*(arity^(k+1))) := by
  have h := CompactComplexSourceReadyStoppedLeafDispatch.positive_runs dir sh rows ell p rho path.visit right src dst n
    v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hVN : 0<volume rows sh ell p*(arity^(k+1)) := Nat.mul_pos hV hN
  have hbnd := CompactComplexSourceReadyStoppedLeafCountBudget.cost_from_path dir rows ell p rho path
    right src dst R basePrecision usedRows n hr hA hG hpay hp hright hsrc hdst hb hu hroom hliveBound
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz) (by
    unfold constant
    simp only [Nat.add_mul,Nat.mul_assoc] at *
    omega)

theorem scalar_runs_linear (dir : Direction) (sh : Shape) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {left : ℕ} {levels frames returned : ℕ} (path : Path sh.active left 0 levels frames returned) (right src dst n : ℕ)
    (v : Tapes (publicTapes s c) 2)
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
      v.tape CompactComplexNonleafRoleChildBank.target=(fun _ => blank))    (hexponent : v.tape (CompactComplexNonleafRoleChildBank.control 1)=RadixZeroFill.encodedBinary (bits 0))
    (hexponentHead : v.head (CompactComplexNonleafRoleChildBank.control 1)=1)    (R basePrecision usedRows : ℕ) (hpay : sh.payload=1)
    (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : basePrecision≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hliveBound : n≤CompactComplexDenominatorCapacity.ledger R basePrecision levels frames returned usedRows) :
    HoareTime (CompactComplexSourceReadyStoppedLeafDispatch.program dir) (fun z => z=ready v)
      (fun z => z=CompactComplexSourceReadyStoppedLeaf.output v (CompactSpectatorLeafAxis.word
        (CompactSpectatorLeafGuardOriginal.result dir (NativePolynomialStageShape.shape sh ell p)
          rows ell (p-2*sh.bits) rho path.visit f)) (CompactComplexDenominatorPolicy.leafTarget n 0))
      (constant*volume rows sh ell p*1) := by
  have h := CompactComplexSourceReadyStoppedLeafDispatch.scalar_runs dir sh rows ell p rho path.visit right src dst n
    v f hG hA hr hp hw hraw hsource hlive htarget hexponent hexponentHead
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hbnd := CompactComplexSourceReadyStoppedLeafBudget.full_cost_from_path dir rows ell p rho path
    arity right src dst R basePrecision usedRows n hr hA hG hpay hp le_rfl hright hsrc hdst hb hu hroom hliveBound
  exact h.consequence (fun _ hz => hz) (fun _ hz => hz) (by
    unfold constant CompactComplexSourceReadyStoppedLeafCountBudget.constant
    simp only [Nat.add_mul,pow_zero,Nat.mul_one] at *
    omega)

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafDispatchBudget
