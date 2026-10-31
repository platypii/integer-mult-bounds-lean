module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.NodeSplitBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.CommonBankHeadBounds
public import IntegerMultBounds.Machine.RecursiveViewFrameSpace

/-! Concrete node banks stay within a linear-volume head offset of the frame's
ordinary bank. The bound includes both saved views and every optional counter. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode
open IntegerMultBounds.Machine Networks
open NodeBank (tapes)
noncomputable section
variable (N : RevNetwork)

theorem Good.heads {v : RecursiveInterchangeLayout.Descriptor} {rr : Tapes (tapes N) Shared50ModularControl.prime}
    (h : Good N v rr) : ∀ i, rr.head i = 0 := by
  obtain ⟨_,x,rfl⟩ := h
  intro i
  simp [NodePark.childRoles,SharedPlacementAlphabet.setTape,SharedBank.empty]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevNode

namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open Family (Frame)
open NodeBank (tapes)
open NodeSplit (midView roleView)
open Routines (hdr)
open SharedBankStageInput (raw)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem node_heads_close {b₀ : ℕ} (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ)
    (hm : N.width ≤ σ.n) (rr : Tapes (tapes N) prime) (hg : RevNode.Good N σ.v rr)
    (c₀ : Fin CommonBank.K → Option ℕ) (i : ℕ) (y : Tapes (CommonBank.count (tapes N)) prime)
    (hy : NodeS N σ i y) :
    ∀ n j, (raw (σ.at rr c₀) n).head j-(36*volume prime σ.v : ℕ) ≤ (raw y n).head j ∧
      (raw y n).head j ≤ (raw (σ.at rr c₀) n).head j+(36*volume prime σ.v : ℕ) := by
  obtain ⟨data,_,rfl⟩ := hy
  have hv := NodeSplit.viewBounds N σ.v σ.hpos σ.b σ.n σ.hb σ.hw (rows_dvd hok hm)
  let saved := RecursiveViewFrame.savedStack (hdr (midView N σ.b σ.n σ.v))
    (RecursiveViewFrame.savedStack (hdr σ.v) σ.node)
  have hupper := RecursiveViewFrame.savedStack_pair_head_le (hdr σ.v) (hdr (midView N σ.b σ.n σ.v))
    σ.node (2*volume prime σ.v) hv.parentHeaders hv.middleHeaders
  have hlower : σ.node.head 0 ≤ saved.head 0 := by
    dsimp only [saved]
    rw [RecursiveViewFrame.savedStack_head,RecursiveViewFrame.savedStack_head]
    omega
  have hn : ∀ j, σ.node.head j-(36*volume prime σ.v : ℕ) ≤ saved.head j ∧
      saved.head j ≤ σ.node.head j+(36*volume prime σ.v : ℕ) := by
    intro j
    have hj : j = 0 := Subsingleton.elim _ _
    subst j
    have hp := hv.positive
    change saved.head 0 ≤ σ.node.head 0+12*((2*volume prime σ.v : ℕ)+1) at hupper
    omega
  have hclose := CommonBank.bank_heads_close (36*volume prime σ.v) (by have := hv.positive; omega)
    rr (RecursiveRoleSerialization.roles data) (hdr σ.v) (hdr (roleView N σ.b σ.n σ.v))
    σ.f σ.f σ.p σ.p σ.node saved σ.scalar σ.scalar c₀ (NodeCall.nodeC N σ.b (σ.n/N.width)) σ.st σ.st
    (by intro j; rw [RevNode.Good.heads N hg j]; simp [RecursiveRoleSerialization.roles])
    (by constructor <;> omega) hn (by intro j; constructor <;> omega) (by intro j; constructor <;> omega)
  intro n j
  by_cases hj : j.val < CommonBank.count (tapes N)
  · simpa only [raw,hj,↓reduceDIte,Family.Frame.at] using hclose ⟨j.val,hj⟩
  · simp only [raw,hj,↓reduceDIte]
    constructor <;> omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
