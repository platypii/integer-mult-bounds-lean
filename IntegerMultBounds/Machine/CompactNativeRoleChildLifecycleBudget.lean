import IntegerMultBounds.Machine.CompactNativeRoleStoppedChildCaller
import IntegerMultBounds.Machine.NativePolynomialStageHeaderBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafGuardBudget

/-! Paid child metadata lifecycles are bounded using actual original native
volume. Fixed role quotients are binary divisions, with no numeric oracle. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleChildLifecycleBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open CompactNativeRoleTransferBudget (volume)
open CompactSpectatorLeafSetup (raw)
open CompactComplexRecursiveGeometry
open RecursiveChildQuotientsConstant (bits)

theorem row_cost (c : ℕ) (s : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hr : 0<rows) (hd : c∣rows) :
    CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.prepare c)
      (raw s rows ell p rho left count slots right src dst)+
    CompactChildHeadersArithmetic.scheduleCost (CompactNativeRoleChildBank.restore c)
      (raw s (rows/c) ell p rho left count slots right src dst)≤
        (10000*(c+1)+2000*(c+1))*volume rows s ell p := by
  have hq := CompactNativeRoleHeaderBudget.quotient_linear rows c hr
  have hc := ActiveRepairRankHeadersCommands.bits_length c
  have hdiv := Nat.div_le_self rows c
  have hV := (CompactNativeRoleHeaderBudget.values_le s rows ell p hr).2.2.2.2.2.2.2
  have hpos : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  have hm : c≤c*volume rows s ell p := Nat.le_mul_of_pos_right c hpos
  simp [CompactNativeRoleChildBank.prepare,CompactNativeRoleChildBank.restore,CompactNativeRoleChildBank.cmd,
    CompactNativeRoleChildBank.product,CompactChildHeadersArithmetic.scheduleCost,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    raw,Function.update,RecursiveChildQuotientsConstant.cost,Nat.mul_comm c (rows/c),Nat.div_mul_cancel hd]
  have hqV := Nat.mul_le_mul_left (10000*(c+1)) hV
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc] at *
  nlinarith

private theorem cost_append (xs ys : List ButterflyAxisHeadersArithmetic.Op) (st : ActiveRepairRankHeadersCommands.State) :
    ButterflyAxisHeadersArithmetic.scheduleCost (xs++ys) st=
      ButterflyAxisHeadersArithmetic.scheduleCost xs st+
      ButterflyAxisHeadersArithmetic.scheduleCost ys (ButterflyAxisHeadersArithmetic.execute xs st) := by
  induction xs generalizing st with
  | nil => simp [ButterflyAxisHeadersArithmetic.scheduleCost,ButterflyAxisHeadersArithmetic.execute]
  | cons x xs ih => simp only [List.cons_append,ButterflyAxisHeadersArithmetic.scheduleCost,
      ButterflyAxisHeadersArithmetic.execute,ih]; omega

theorem precision_rest_cost (s : Shape) (rows ell p rho left count slots right src dst : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.prepare
      (raw s rows ell p rho left count slots right src dst)+
    ButterflyAxisHeadersArithmetic.scheduleCost CompactNativeRoleChildPrecision.restore
      (CompactNativeRoleChildPrecision.baseline s rows ell p rho left count slots right src dst)≤
    ButterflyAxisHeadersArithmetic.scheduleCost CompactSpectatorLeafSetup.geometry
      (raw s rows ell p rho left count slots right src dst)+2000*(s.bits+p+1) := by
  rw [CompactNativeRoleChildPrecision.prepare,cost_append,cost_append,CompactNativeRoleHeaders.execute_append]
  simp only [CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right src dst hH hK]
  simp [CompactNativeRoleChildPrecision.restore,CompactNativeRoleChildPrecision.baseline,
    CompactNativeRoleChildPrecision.cmd,ButterflyAxisHeadersArithmetic.scheduleCost,
    ButterflyAxisHeadersArithmetic.cost,ButterflyAxisHeadersArithmetic.eval,ButterflyAxisHeadersArithmetic.execute,
    CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,
    ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,
    ActiveRepairRankHeadersCommands.put,CompactSpectatorLeafSetup.state,raw,Function.update]
  have hh : s.H≤s.bits := by unfold Shape.bits; omega
  have hb : s.B≤s.bits := by unfold Shape.bits; omega
  have hf : s.F≤s.bits := by unfold Shape.bits; omega
  have hp := Nat.sub_le p (2*s.bits)
  omega

theorem payload_count_irrelevant (s : Shape) (rows ell p rho left count other slots right src dst : ℕ)
    (hH : 0<s.H) (hK : 0<s.chunk) :
    NativePolynomialStageHeaders.cost s rows ell p rho left count slots right src dst+
      ButterflyAxisHeadersArithmetic.scheduleCost NativePolynomialStageHeaders.restore
        (NativePolynomialStageHeaders.prepared s rows ell p rho left count slots right src dst)=
    NativePolynomialStageHeaders.cost s rows ell p rho left other slots right src dst+
      ButterflyAxisHeadersArithmetic.scheduleCost NativePolynomialStageHeaders.restore
        (NativePolynomialStageHeaders.prepared s rows ell p rho left other slots right src dst) := by
  unfold NativePolynomialStageHeaders.cost
  rw [CompactSpectatorLeafSetupBudget.geometry_cost_eq s rows ell p rho left count slots right src dst hH hK,
    CompactSpectatorLeafSetupBudget.geometry_cost_eq s rows ell p rho left other slots right src dst hH hK]
  simp [NativePolynomialStageHeaders.rest,NativePolynomialStageHeaders.restore,
    NativePolynomialStageHeaders.prepared,ButterflyAxisHeadersArithmetic.scheduleCost,
    ButterflyAxisHeadersArithmetic.cost,ButterflyAxisHeadersArithmetic.eval,CompactChildHeadersArithmetic.cost,
    CompactChildHeadersArithmetic.eval,ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,
    ActiveRepairRankHeadersCommands.cost,ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,
    CompactSpectatorLeafSetup.state,raw,Function.update]

end
end IntegerMultBounds.Machine.CompactNativeRoleChildLifecycleBudget
