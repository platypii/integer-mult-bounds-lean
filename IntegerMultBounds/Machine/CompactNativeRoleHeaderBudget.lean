import IntegerMultBounds.Machine.CompactNativeRoleControllerBudget
import IntegerMultBounds.Machine.CompactSpectatorLeafSetupBudget

/-! The binary quotient of the physical row count costs linearly in row count,
with a fixed role-count constant. Complete role header synthesis is paid below. -/
namespace IntegerMultBounds.Machine.CompactNativeRoleHeaderBudget
noncomputable section
open CompactGadgetReservationShape (Shape)
open RecursiveChildQuotientsConstant (bits)
open ButterflyAxisHeadersArithmetic
open CompactNativeRoleOriginal (symbols)
open CompactNativeRoleHeaders
open CompactNativeRoleTransferBudget (volume)

private theorem square_power (k : ℕ) : (k+1)^2≤4*2^k := by
  induction k with
  | zero => norm_num
  | succ k ih =>
    by_cases h0 : k=0
    · subst k; norm_num
    by_cases h1 : k=1
    · subst k; norm_num
    rw [pow_succ (2:ℕ) k]
    have hk : 2≤k := by omega
    nlinarith

theorem bits_square (n : ℕ) : (bits n).length^2≤4*(n+1) := by
  have hl := GrowingCounterData.canonical_width (bits n) (RecursiveChildQuotientsConstant.bits_canonical n)
  rw [RecursiveChildQuotientsConstant.bits_value] at hl
  have hp : 2^n.log2≤n+1 := by
    by_cases hn : n=0
    · subst n; norm_num
    · exact ((Nat.le_log2 hn).mp le_rfl).trans (by omega)
  have hs := square_power n.log2
  nlinarith

theorem quotient_linear (rows c : ℕ) (hr : 0<rows) :
    BinaryDescriptorDivision.cost (bits rows) (bits c)≤10000*(c+1)*rows := by
  have hh := BinaryDescriptorDivision.cost_le (bits rows) (bits c)
  have hs := bits_square rows
  have hl := ActiveRepairRankHeadersCommands.bits_length rows
  have hc := ActiveRepairRankHeadersCommands.bits_length c
  have hp := Nat.mul_le_mul hl hc
  nlinarith

private theorem cost_append (xs ys : List Op) (st : ActiveRepairRankHeadersCommands.State) :
    scheduleCost (xs++ys) st=scheduleCost xs st+scheduleCost ys (execute xs st) := by
  induction xs generalizing st with
  | nil => simp [scheduleCost,execute]
  | cons x xs ih => simp only [List.cons_append,scheduleCost,execute,ih]; omega

theorem rest_cost_eq (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ) :
    scheduleCost (rest c merge) (CompactSpectatorLeafSetup.state 0 s rows ell p rho left count slots right source target)=
      BinaryDescriptorDivision.cost (bits rows) (bits c)+3*(bits c).length+
      FixedBasePowerDescriptor.constant 2*(2^s.bits+2^ell)+
      100*(9*s.bits+3*p+25)+
      53*(2*(recordWidth s p+1)+2^s.bits*2^ell+symbols s ell p+
        (if merge then rows/c else rows)*symbols s ell p)+73 := by
  have h4 : (bits 4).length=3 := rfl
  have h1 : (bits 1).length=1 := rfl
  have h2 : (bits 2).length=2 := rfl
  cases merge <;>
    dsimp [rest,scheduleCost,cost,eval,CompactChildHeadersArithmetic.cost,CompactChildHeadersArithmetic.eval,
      ActivePrefixStageHeadersOps.cost,ActivePrefixStageHeadersOps.eval,ActiveRepairRankHeadersCommands.cost,
      ActiveRepairRankHeadersCommands.eval,ActiveRepairRankHeadersCommands.put,CompactSpectatorLeafSetup.state,
      Function.update,RecursiveChildQuotientsConstant.cost,recordWidth,ButterflyGuard.width,ButterflyGuard.halfWidth,
      CompactNativeRoleOriginal.symbols,CompactNativeRoleOriginal.inner]
  all_goals norm_num only [h4,h1,h2,Option.getD_some]
  all_goals ring


theorem values_le (s : Shape) (rows ell p : ℕ) (hr : 0<rows) :
    s.bits≤volume rows s ell p ∧ p≤volume rows s ell p ∧
    2^s.bits≤volume rows s ell p ∧ 2^ell≤volume rows s ell p ∧
    2^s.bits*2^ell≤volume rows s ell p ∧
    2*(recordWidth s p+1)≤volume rows s ell p ∧
    symbols s ell p≤volume rows s ell p ∧ rows≤volume rows s ell p := by
  have hw := CompactNativeRoleControllerBudget.width_le_volume s rows ell p hr
  have hS := CompactNativeRoleTransferBudget.symbols_pos s ell p
  have hrows := Nat.le_mul_of_pos_right rows hS
  have hsym := Nat.le_mul_of_pos_left (symbols s ell p) hr
  have hbits : 0<2^s.bits := pow_pos (by decide) _
  have hell : 0<2^ell := pow_pos (by decide) _
  have hW : 0<2*(recordWidth s p+1) := by omega
  have hinner := Nat.le_mul_of_pos_right (2^s.bits*2^ell) hW
  have hwidth := Nat.le_mul_of_pos_left (2*(recordWidth s p+1)) (Nat.mul_pos hbits hell)
  have hb := Nat.le_mul_of_pos_right (2^s.bits) hell
  have he := Nat.le_mul_of_pos_left (2^ell) hbits
  unfold volume symbols CompactNativeRoleOriginal.inner at *
  unfold recordWidth ButterflyGuard.width ButterflyGuard.halfWidth at *
  omega

def constant (c : ℕ) := 60000+10003*(c+1)+2*FixedBasePowerDescriptor.constant 2

theorem headers_linear (c : ℕ) (merge : Bool) (s : Shape) (rows ell p rho left count slots right source target : ℕ)
    (hr : 0<rows) (hA : 0<s.axes) (hG : 0<s.guard) (hK : 0<s.chunk) :
    scheduleCost (schedule c merge) (CompactSpectatorLeafSetup.raw s rows ell p rho left count slots right source target)≤
      constant c*volume rows s ell p := by
  have hH : 0<s.H := Nat.mul_pos hA hG
  have hV : 0<volume rows s ell p := Nat.mul_pos hr (CompactNativeRoleTransferBudget.symbols_pos s ell p)
  obtain ⟨hb,hp,hpow,hpoly,hinner,hwidth,hsym,hrows⟩ := values_le s rows ell p hr
  have hHbits : s.H≤s.bits := by unfold Shape.bits; omega
  have hBbits : s.B≤s.bits := by unfold Shape.bits; omega
  have hFbits : s.F≤s.bits := by unfold Shape.bits; omega
  have hAbits : s.active*s.chunk≤s.bits := by unfold Shape.bits; omega
  have hg := CompactSpectatorLeafSetupBudget.geometry_cost_eq s rows ell p rho left count slots right source target hH hK
  have hq := quotient_linear rows c hr
  have hqV := Nat.mul_le_mul_left (10000*(c+1)) hrows
  have hc := ActiveRepairRankHeadersCommands.bits_length c
  have hcv : c+1≤(c+1)*volume rows s ell p := Nat.le_mul_of_pos_right _ hV
  have hpowV : FixedBasePowerDescriptor.constant 2*2^s.bits+FixedBasePowerDescriptor.constant 2*2^ell≤
      2*(FixedBasePowerDescriptor.constant 2*volume rows s ell p) := by
    calc
      _ = FixedBasePowerDescriptor.constant 2*(2^s.bits+2^ell) := by ring
      _ ≤ FixedBasePowerDescriptor.constant 2*(2*volume rows s ell p) :=
        Nat.mul_le_mul_left _ (by omega)
      _ = _ := by ring
  have he : (if merge then rows/c else rows)*symbols s ell p≤volume rows s ell p := by
    cases merge
    · exact le_rfl
    · exact Nat.mul_le_mul_right _ (Nat.div_le_self rows c)
  rw [schedule,cost_append,CompactSpectatorLeafSetup.geometry_eval s rows ell p rho left count slots right source target hH hK,
    rest_cost_eq,hg]
  unfold constant
  simp only [Nat.mul_add,Nat.add_mul,Nat.mul_assoc] at *
  omega

end
end IntegerMultBounds.Machine.CompactNativeRoleHeaderBudget
