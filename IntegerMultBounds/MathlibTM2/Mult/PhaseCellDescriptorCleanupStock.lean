module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDescriptorBankStep
public import IntegerMultBounds.MathlibTM2.Host.RegisterBankStock

/-! Cleanup charges only the actual private register bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

/-- Output collection and two-sided cleanup are linear in private storage. -/
theorem descriptorBankCleanupCost_le_stock {N A : ℕ} (output : Fin N) (F : Stacks N A) :
    descriptorBankCleanupCost output F ≤ 6 * registerBankStock F + 6 * N + 6 := by
  have ho : (F.R output).length ≤ ∑ i, (F.R i).length :=
    Finset.single_le_sum (fun i _ => Nat.zero_le (F.R i).length) (Finset.mem_univ output)
  unfold descriptorBankCleanupCost registerBankStock
  rw [Finset.sum_add_distrib]
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
