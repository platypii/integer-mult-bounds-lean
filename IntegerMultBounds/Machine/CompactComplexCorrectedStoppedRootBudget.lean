import IntegerMultBounds.Machine.CompactComplexSourceReadyCorrectedStoppedRootRun

/-! The full stopped-root cost includes runtime classification, literal leaf
execution and the final empty-root halt. Original Path geometry pays every
term uniformly in native volume times the actual visit count. -/
namespace IntegerMultBounds.Machine.CompactComplexCorrectedStoppedRootBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactComplexRecursiveGeometry (arity Visit)
open CompactRecursiveDependencyBudget (Path)
open CompactNativeRoleTransferBudget (volume)
open CompactComplexSourceReadyGuard (setupCost cleanupCost guardConstant)
variable {sh : Shape} {left e levels frames count : ℕ}
attribute [local irreducible] CompactComplexSourceReadyStoppedLeafDispatchBudget.constant
  guardConstant

/-- Literal cost of both checked stopped-root execution theorems. -/
def cost (sh : Shape) (rows ell p exponent : ℕ) :=
  ((setupCost sh.axes exponent+cleanupCost sh.axes exponent+7+1)+
    (((CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+4)*
      volume rows sh ell p*(arity^exponent))+1)+2)

def constant := CompactComplexSourceReadyStoppedLeafDispatchBudget.constant+3*guardConstant+12

/-- The retained original geometry pays the complete classifier, including
exponent zero, without assuming active axes are bounded by the global axes. -/
theorem classifier_native (rows ell p : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left e) (hr : 0<rows) (hG : 0<sh.guard) :
    setupCost sh.axes e+cleanupCost sh.axes e+3≤3*guardConstant*volume rows sh ell p := by
  have hbits := (CompactNativeRoleHeaderBudget.values_le sh rows ell p hr).1
  have hN := CompactSpectatorLeafSemantics.count_le_bits sh rho visit
  have he : e<arity^e := Nat.lt_pow_self (by decide : 1<arity)
  have hH : sh.axes≤sh.H := Nat.le_mul_of_pos_right _ hG
  have haxes : sh.axes≤sh.bits := by unfold Shape.bits;omega
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hsum : sh.axes+e+1≤3*volume rows sh ell p := by omega
  have h := CompactComplexSourceReadyGuard.cost_linear sh.axes e
  have hm := Nat.mul_le_mul_left guardConstant hsum
  exact h.trans (by simpa only [Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hm)

/-- One fixed coefficient pays the actual stopped-root runtime, all joins,
classification and the final halt, from the genuine visit and native volume. -/
theorem cost_native (rows ell p : ℕ) (rho : Fin sh.chunk)
    (visit : Visit sh.active left e) (hr : 0<rows) (hG : 0<sh.guard) :
    cost sh rows ell p e≤constant*volume rows sh ell p*arity^e := by
  have hg := classifier_native rows ell p rho visit hr hG
  have hV : 0<volume rows sh ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos sh ell p)
  have hN : 0<arity^e := pow_pos (by decide) _
  have hguard := Nat.le_mul_of_pos_right (3*guardConstant*volume rows sh ell p) hN
  have hVN : 1≤volume rows sh ell p*arity^e := Nat.mul_pos hV hN
  unfold cost constant
  nlinarith only [hg,hguard,hVN]

/-- Actual dependency Paths supply their Visit internally. -/
theorem cost_from_path (rows ell p : ℕ) (rho : Fin sh.chunk)
    (path : Path sh.active left e levels frames count) (hr : 0<rows) (hG : 0<sh.guard) :
    cost sh rows ell p e≤constant*volume rows sh ell p*arity^e :=
  cost_native rows ell p rho path.visit hr hG

/-- Cost weakening for the exact checked stopped-root Hoare contracts. The
native envelope is derived from actual Path geometry, never supplied. -/
theorem hoare_native {t q : ℕ} {M : Program t q 2} {P Q : Tapes t 2 → Prop}
    (rows ell p : ℕ) (rho : Fin sh.chunk)
    (path : Path sh.active left e levels frames count) (hr : 0<rows) (hG : 0<sh.guard)
    (h : HoareTime M P Q (cost sh rows ell p e)) :
    HoareTime M P Q (constant*volume rows sh ell p*arity^e) :=
  h.consequence (fun _ h => h) (fun _ h => h) (cost_from_path rows ell p rho path hr hG)

end
end IntegerMultBounds.Machine.CompactComplexCorrectedStoppedRootBudget
