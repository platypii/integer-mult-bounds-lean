module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.ChildFrameStackBounds
public import IntegerMultBounds.Machine.RoleArrayCallSpace

/-! The concrete child parks a fixed number of child-volume streams. Role
subdivision pays for their retention with a linear parent-volume potential. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl Routines NodeSplit Family NodeBank
  RecursiveInterchangeLayout
noncomputable section

namespace NodePark
variable (N : RevNetwork) {u : ℕ}
theorem entered_payload_head (w : N.World ⊕ N.Temp) (n : ℕ) (rr : Tapes (tapes N) prime)
    (hs : Fin 6 → List Bool) (f : ℤ → Fin (prime+4)) (p : ℤ)
    (aux : Tapes u prime) (st : Tapes 2 prime) :
    (RecursiveCallProtocol.entered (parked N w) (wireSlot N w) (io N) n
      (RecursiveCallBank.bank rr hs f p aux st)).head (RecursiveCallBank.controlSlot 2) =
      p+((parked N w).length*n : ℕ) := by
  have h := RoleArrayCall.entered_stack_head (RecursiveCallBank.layout (t := tapes N) (u := u))
    ((parked N w).map RecursiveCallBank.role) (RecursiveCallBank.role (wireSlot N w))
    (RecursiveCallBank.role (io N)) n (RecursiveCallBank.bank rr hs f p aux st)
  rw [List.length_map] at h
  simpa only [RecursiveCallProtocol.entered,RecursiveCallBank.layout,
    (RecursiveCallBank.payload_stack rr hs f p aux st).1] using h
end NodePark

namespace RevHalf
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem childFrame_payload_head {b₀ : ℕ} (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    (childFrame (N := N) σ hok hm i w r data).p =
      σ.p+((NodePark.parked N w).length*volume prime (roleView N σ.b σ.n σ.v) : ℕ) := by
  exact NodePark.entered_payload_head N w _ _ _ _ _ _ _

theorem childFrame_volume {b₀ : ℕ} (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    volume prime (childFrame (N := N) σ hok hm i w r data).v =
      volume prime (roleView N σ.b σ.n σ.v) := by
  apply RevMachine.sub_volume
  · rfl
  · simpa only [Nat.zero_add] using Nat.mul_le_mul_right (σ.n/N.width) hr

theorem childFrame_volume_mul {b₀ : ℕ} (σ : Frame (pcs N) capacity)
    (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    volume prime (childFrame (N := N) σ hok hm i w r data).v*N.roleCount = volume prime σ.v := by
  rw [childFrame_volume N σ hok hm i w r hr data]
  exact (RecursiveInterchangeLayout.role_volume_mul prime N.roleCount
    (midView N σ.b σ.n σ.v) (rows_dvd hok hm)).trans (NodeSplit.mid_volume N σ.hw)

/-- Generated parent and middle headers discharge the stack-size premises.
Geometric child volumes pay for every retained node frame on a live path. -/
theorem childFrame_node_volume_potential_le {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.node.head 0+(72*volume prime child.v : ℕ) ≤
      σ.node.head 0+(72*volume prime σ.v : ℕ) := by
  have hparent : ∀ j, (hdr σ.v j).length ≤ 2*volume prime σ.v :=
    fun j => RecursiveRowsNode.header_length _ σ.hpos _ (hdr_headers _) j
  have hmid : ∀ j, (hdr (midView N σ.b σ.n σ.v) j).length ≤ 2*volume prime σ.v := by
    intro j
    have h := RecursiveRowsNode.header_length (midView N σ.b σ.n σ.v)
      (NodeSplit.mid_positive N (b := σ.b) (n := σ.n) σ.hpos) _ (hdr_headers _) j
    rwa [NodeSplit.mid_volume N σ.hw] at h
  have hnode := childFrame_node_head_le N σ hok hm i w r data _ hparent hmid
  have hvol := childFrame_volume_mul N σ hok hm i w r hr data
  have htwice := Nat.mul_le_mul_left (volume prime (childFrame (N := N) σ hok hm i w r data).v) hroles
  have hhalf : 2*volume prime (childFrame (N := N) σ hok hm i w r data).v ≤ volume prime σ.v := by
    nlinarith only [htwice,hvol]
  have hhalfZ : (2 : ℤ)*volume prime (childFrame (N := N) σ hok hm i w r data).v ≤ volume prime σ.v := by
    exact_mod_cast hhalf
  have hp := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le σ.v σ.hpos
  have hpZ : (1 : ℤ) ≤ volume prime σ.v := by exact_mod_cast hp
  dsimp only
  push_cast at hnode ⊢
  nlinarith only [hnode,hhalfZ,hpZ]

/-- Retained payload plus room for the current active view never increases
at a child call. The fixed tape count pays for parked temporaries as well. -/
theorem childFrame_payload_potential_le {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.p+(tapes N*volume prime child.v : ℕ) ≤ σ.p+(tapes N*volume prime σ.v : ℕ) := by
  have hd := rows_dvd hok hm
  have hvol := RecursiveInterchangeLayout.role_volume_mul prime N.roleCount
    (midView N σ.b σ.n σ.v) hd
  rw [NodeSplit.mid_volume N σ.hw] at hvol
  have hp := NodePark.parked_length_le N w
  have hpark := Nat.mul_le_mul_right (volume prime (roleView N σ.b σ.n σ.v)) hp
  have htwice := Nat.mul_le_mul_left (tapes N*volume prime (roleView N σ.b σ.n σ.v)) hroles
  dsimp only
  rw [childFrame_payload_head N σ hok hm i w r data,childFrame_volume N σ hok hm i w r hr data]
  have hbound : (NodePark.parked N w).length*volume prime (roleView N σ.b σ.n σ.v)+
      tapes N*volume prime (roleView N σ.b σ.n σ.v) ≤ tapes N*volume prime σ.v := by
    change volume prime (roleView N σ.b σ.n σ.v)*N.roleCount = volume prime σ.v at hvol
    have hpay := congrArg (fun v => tapes N*v) hvol
    nlinarith only [hpark,htwice,hpay]
  have hboundZ : (((NodePark.parked N w).length*volume prime (roleView N σ.b σ.n σ.v)+
      tapes N*volume prime (roleView N σ.b σ.n σ.v) : ℕ) : ℤ) ≤
      (tapes N*volume prime σ.v : ℕ) := by exact_mod_cast hbound
  push_cast at hboundZ ⊢
  omega

end RevHalf
end
end IntegerMultBounds.MathlibTM2.M8.RevMachine
