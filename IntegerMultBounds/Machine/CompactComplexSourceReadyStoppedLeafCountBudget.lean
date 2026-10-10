import IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCount

/-! Actual per-slot count expansion and restoration are charged in full, on
both sides of the complete physical stopped leaf. Scalar leaves retain count1. -/
namespace IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCountBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafGuardOriginal (Direction)
open CompactSpectatorLeafCountBudget (expand restore expanded)
open RecursiveChildQuotientsConstant (bits)
variable {sh : Shape} {left k : ℕ}

def countConstant := 12000*(arity+1)+2000
def constant := CompactComplexSourceReadyStoppedLeafBudget.constant+countConstant+2

theorem count_linear (rows ell p : ℕ) (rho : Fin sh.chunk) (right src dst : ℕ) :
    let st := CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst
    CompactChildHeadersArithmetic.scheduleCost expand st+
      CompactChildHeadersArithmetic.scheduleCost restore (expanded st arity (arity^k))≤
        countConstant*(arity^(k+1)) := by
  let st := CompactSpectatorLeafSetup.raw sh rows ell p rho.val left (arity^k) arity right src dst
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hc : arity^k≤arity^(k+1) := Nat.pow_le_pow_right (by decide) (by omega)
  have ha : arity≤arity^(k+1) := by
    rw [pow_succ]
    exact Nat.le_mul_of_pos_left _ (pow_pos (by decide) _)
  have hq := CompactNativeRoleHeaderBudget.quotient_linear (arity^k*arity) arity
    (Nat.mul_pos (pow_pos (by decide) _) (by decide))
  have he := CompactSpectatorLeafCountBudget.expand_cost st arity (arity^k) rfl rfl
  have hb := ActiveRepairRankHeadersCommands.bits_length (arity^k)
  have hdiv : arity^k*arity/arity=arity^k := Nat.mul_div_cancel _ (by decide)
  dsimp only
  simp [restore,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    expanded,CompactSpectatorLeafSetup.raw,Function.update,hdiv]
  simp only [←pow_succ] at he hq ⊢
  dsimp only [st] at he
  unfold countConstant
  nlinarith

theorem cost_from_path (dir : Direction) (rows ell p : ℕ) (rho : Fin sh.chunk)
    {levels frames returned : ℕ} (path : Path sh.active left (k+1) levels frames returned)
    (right src dst R base usedRows n : ℕ)
    (hr : 0<rows) (hA : 0<sh.axes) (hG : 0<sh.guard) (hpay : sh.payload=1)
    (hP : 2*sh.bits≤p) (hright : right≤sh.active) (hsrc : src≤arity) (hdst : dst≤arity)
    (hb : base≤p-2*sh.bits) (hu : usedRows≤R)
    (hroom : CompactComplexDenominatorCapacity.room R≤sh.chunk)
    (hlive : n≤CompactComplexDenominatorCapacity.ledger R base levels frames returned usedRows) :
    CompactComplexSourceReadyStoppedLeafCount.cost dir sh rows ell p rho path.visit right src dst n≤
      constant*volume rows sh ell p*(arity^(k+1)) := by
  have h0 := count_linear (left:=left) (k:=k) rows ell p rho right src dst
  have h1 := CompactComplexSourceReadyStoppedLeafBudget.full_cost_from_path dir rows ell p rho path
    arity right src dst R base usedRows n hr hA hG hpay hP le_rfl hright hsrc hdst hb hu hroom hlive
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hN : 0<arity^(k+1) := pow_pos (by decide) _
  have hlift := Nat.mul_le_mul_right (arity^(k+1)) (Nat.le_mul_of_pos_right countConstant hV)
  have hVN : 0<volume rows sh ell p*(arity^(k+1)) := Nat.mul_pos hV hN
  dsimp only [CompactComplexSourceReadyStoppedLeafCount.cost] at *
  unfold constant
  simp only [Nat.add_mul,Nat.mul_assoc] at *
  omega

end
end IntegerMultBounds.Machine.CompactComplexSourceReadyStoppedLeafCountBudget
