module

-- S6 supplier seam
public import IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared
public import IntegerMultBounds.MathlibTM2.M8.Global.SupplierNet

/-!
# The equal-width radix interchange of the cost chain

The cost chain uses the supplier's equal-width radix interchange under these names. The supplier
is the stage-2 supplier on the PR97 node (`M8.Global.pr97`, `M8.Stage2Machine.Total`); its exponent
`τ₂ = 1 - 123899714039/10¹⁵` is the exponent `Parameters.tau` of the cost chain (`supplier_tau`), at
which `uniform_bound` is stated.
-/

@[expose] public section

namespace IntegerMultBounds.Machine.BinaryRadixEqualShared

export IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared (count liftBank liftSlot lowDestination destination sourceSlot lowDestination_injective liftSlot_injective destination_injective liftBank_sparse low_sparse bank private_bank liftBank_cells bank_source bank_set_source destination_room copyProgram eraseProgram header_bounds bank_eq runProgram program cost input runs)

/-- The supplier's program counters, at their sealed width. -/
noncomputable instance supplierCapacity : IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total.Capacity :=
  ⟨IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total.pcBits, IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total.pcCapacity⟩

theorem supplier_tau : IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total.tau = Parameters.tau := by
  norm_num [IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Total.tau, Parameters.tau]

theorem uniform_bound : ∃ C : ℝ, 0 < C ∧ ∀ (P G B u : ℕ) (hs : Fin 4 → List Bool),
    0 < P → 0 < G → 0 < B →
    (∀ i, Counter.value (hs i) = BinaryRadixRangePrepare.values P G B u i) →
    (∀ i, GrowingCounterData.Canonical (hs i)) →
    (cost P G B u hs : ℝ) ≤ C*(RadixRangePadding.volume P (2^u) G B : ℝ)*
      ((max 1 u : ℕ) : ℝ)^Parameters.tau := by
  rw [← supplier_tau]
  exact IntegerMultBounds.MathlibTM2.M8.Machine.BinaryRadixEqualShared.uniform_bound

end IntegerMultBounds.Machine.BinaryRadixEqualShared
