module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeCallBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplitBounds

/-! The concrete call budget is linear in its parent's active volume. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open RecursiveInterchangeLayout (volume)
open Family (Frame)
open NodeSplit (roleView)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

def callSpaceConstant (N : RevNetwork) (k : ℕ) : ℕ :=
  NodeCall.enterSpaceConstant N k+NodeCall.recoverSpaceConstant N

theorem callCost_linear {b₀ : ℕ} (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ)
    (hm : N.width ≤ σ.n) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width) :
    callCost N σ (w,r) ≤ callSpaceConstant N k*volume Shared50ModularControl.prime σ.v := by
  have hv := NodeSplit.viewBounds N σ.v σ.hpos σ.b σ.n σ.hb σ.hw (rows_dvd hok hm)
  have hf : 0 < σ.n/N.width := Nat.div_pos hm (by have := N.two_le_width; omega)
  have he := NodeCall.enterCost_linear N w k (roleView N σ.b σ.n σ.v) hv.rolePos
    σ.b (σ.n/N.width) r σ.hb rfl hr
  have hc := NodeCall.recoverCost_linear N w (roleView N σ.b σ.n σ.v) hv.rolePos
    σ.b (σ.n/N.width) r σ.hb hf rfl hr
  calc
    _ ≤ (NodeCall.enterSpaceConstant N k+NodeCall.recoverSpaceConstant N)*
        volume Shared50ModularControl.prime (roleView N σ.b σ.n σ.v) := by
      unfold callCost
      rw [Nat.add_mul]
      exact Nat.add_le_add he hc
    _ ≤ _ := Nat.mul_le_mul_left _ hv.role

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
