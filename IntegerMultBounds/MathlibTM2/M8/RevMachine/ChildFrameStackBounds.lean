module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.Machine.RecursiveViewFrameSpace

/-! Storage retained on the node stack by the concrete recursive child call.
Two saved views add twelve header words; no child runtime enters the bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl Routines NodeSplit Family NodeBank
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem childFrame_node_head_le {b₀ : ℕ} (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v))
    (L : ℕ) (hparent : ∀ j, (hdr σ.v j).length ≤ L)
    (hmid : ∀ j, (hdr (midView N σ.b σ.n σ.v) j).length ≤ L) :
    ((childFrame (N := N) σ hok hm i w r data).node).head 0 ≤ σ.node.head 0+12*(L+1) := by
  exact RecursiveViewFrame.savedStack_pair_head_le _ _ _ L hparent hmid

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
