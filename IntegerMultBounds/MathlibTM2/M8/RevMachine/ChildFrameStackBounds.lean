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

/-- The remaining recursion depth pays for the two saved views of every
future child. This potential decreases across the actual child-frame update,
so the same bound propagates down an arbitrary live call chain. -/
theorem childFrame_node_potential_le {b₀ : ℕ}
    (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ) (hi : (pcs N)[i] = .call (w,r))
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v))
    (L : ℕ) (hparent : ∀ j, (hdr σ.v j).length ≤ L)
    (hmid : ∀ j, (hdr (midView N σ.b σ.n σ.v) j).length ≤ L) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.node.head 0+(RevNode.depth N.width (Rk N) child.n*(12*(L+1)) : ℕ) ≤
      σ.node.head 0+(RevNode.depth N.width (Rk N) σ.n*(12*(L+1)) : ℕ) := by
  have hnode := childFrame_node_head_le N σ hok hm i w r data L hparent hmid
  have hd := RevNode.depth_child (fun r h => (hRk r h).2) hm
    (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt (w,r) hi)
  have hpay := Nat.mul_le_mul_right (12*(L+1)) hd
  have hpayZ : (((RevNode.depth N.width (Rk N) (r*(σ.n/N.width))+1)*(12*(L+1)) : ℕ) : ℤ) ≤
      (RevNode.depth N.width (Rk N) σ.n*(12*(L+1)) : ℕ) := by exact_mod_cast hpay
  change (RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v))
      (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)).head 0+
      (RevNode.depth N.width (Rk N) (r*(σ.n/N.width))*(12*(L+1)) : ℕ) ≤ _
  change (RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v))
      (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)).head 0 ≤ _ at hnode
  push_cast at hpayZ ⊢
  nlinarith only [hnode,hpayZ]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
