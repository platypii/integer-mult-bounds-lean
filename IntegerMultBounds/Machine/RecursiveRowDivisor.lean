import IntegerMultBounds.Machine.FixedBasePowerDescriptor
import IntegerMultBounds.Machine.Shared50RecursiveDepth

/-! The fixed Shared50 row divisor W^k is actually synthesized from a runtime
binary depth on the unchanged finite alphabet. Its cost is linear in a row
range known to dominate the divisor; no precomputed power descriptor is assumed. -/
namespace IntegerMultBounds.Machine.RecursiveRowDivisor
noncomputable section
open Networks
open Shared50TapeGlobal (roleCount)
variable {q : ℕ}

/-- The fixed World count is large, but never a runtime control parameter. -/
theorem base_ge_two : 2 ≤ roleCount := by
  rw [Shared50RecursiveNodeLayout.roleCount_eq_W,Shared50Parameters.wire_count]
  omega

def program := FixedBasePowerDescriptor.program (q := q) roleCount

def constant := FixedBasePowerDescriptor.constant roleCount

theorem construct_hoare (ks : List Bool) (k : ℕ) (hk : Counter.value ks = k)
    (hc : GrowingCounterData.Canonical ks) :
    HoareTime (program (q := q))
      (fun v => v = FixedBasePowerDescriptor.input ks)
      (fun v => v = FixedBasePowerDescriptor.output roleCount k ks) (constant*roleCount^k) :=
  FixedBasePowerDescriptor.constructs_linear roleCount k base_ge_two ks hk hc

/-- A supplied dominating row range absorbs all real power construction work. -/
theorem construct_bounded (ks : List Bool) (k V : ℕ) (hk : Counter.value ks = k)
    (hc : GrowingCounterData.Canonical ks) (hV : roleCount^k ≤ V) :
    HoareTime (program (q := q))
      (fun v => v = FixedBasePowerDescriptor.input ks)
      (fun v => v = FixedBasePowerDescriptor.output roleCount k ks) (constant*V) :=
  (construct_hoare ks k hk hc).consequence (fun _ h => h) (fun _ h => h)
    (Nat.mul_le_mul_left constant hV)

theorem divisor_value (k : ℕ) :
    Counter.value (FixedBasePowerStep.bits roleCount k) = roleCount^k :=
  FixedBasePowerStep.bits_value roleCount k

theorem divisor_canonical (k : ℕ) :
    GrowingCounterData.Canonical (FixedBasePowerStep.bits roleCount k) :=
  FixedBasePowerStep.bits_canonical roleCount k

end
end IntegerMultBounds.Machine.RecursiveRowDivisor
