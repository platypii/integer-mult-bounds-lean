module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.ChildFramePayloadBounds
public import IntegerMultBounds.Machine.RecursiveChildCallStackSpace

/-! All four retained allocation pointers have a single linear-volume
potential across the concrete recursive child-call update. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds IntegerMultBounds.Machine Networks
  Networks.Shared50ModularControl Routines NodeSplit Family NodeBank RecursiveInterchangeLayout
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  {capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k}

theorem childFrame_volume_half {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    2*volume prime (childFrame (N := N) σ hok hm i w r data).v ≤ volume prime σ.v := by
  have hvol := childFrame_volume_mul N σ hok hm i w r hr data
  have h := Nat.mul_le_mul_left (volume prime (childFrame (N := N) σ hok hm i w r data).v) hroles
  nlinarith only [h,hvol]

theorem childFrame_descriptor_potential_le {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.st.head 0+(18*volume prime child.v : ℕ) ≤ σ.st.head 0+(18*volume prime σ.v : ℕ) := by
  have hh : ∀ j, (hdr (roleView N σ.b σ.n σ.v) j).length ≤
      2*volume prime (roleView N σ.b σ.n σ.v) := fun j =>
    RecursiveRowsNode.header_length _ (NodeSplit.roleView_positive N σ.hpos (rows_dvd hok hm)) _ (hdr_headers _) j
  have hdesc := RecursiveChildCallSetup.savedStacks_descriptor_head_le
    (hdr (roleView N σ.b σ.n σ.v)) σ.st (Graph.returnCode (pcs N) capacity i) _ hh
  have hvol := childFrame_volume N σ hok hm i w r hr data
  rw [← hvol] at hdesc
  have hhalf := childFrame_volume_half N hroles σ hok hm i w r hr data
  have hhalfZ : (2 : ℤ)*volume prime (childFrame (N := N) σ hok hm i w r data).v ≤ volume prime σ.v := by
    exact_mod_cast hhalf
  have hp := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le
    (childFrame (N := N) σ hok hm i w r data).v (childFrame (N := N) σ hok hm i w r data).hpos
  have hpZ : (1 : ℤ) ≤ volume prime (childFrame (N := N) σ hok hm i w r data).v := by exact_mod_cast hp
  change (childFrame (N := N) σ hok hm i w r data).st.head 0 ≤ _ at hdesc
  dsimp only
  push_cast at hdesc ⊢
  nlinarith only [hdesc,hhalfZ,hpZ]

theorem childFrame_pc_potential_le {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.st.head 1+(k*volume prime child.v : ℕ) ≤ σ.st.head 1+(k*volume prime σ.v : ℕ) := by
  have hh : (childFrame (N := N) σ hok hm i w r data).st.head 1 = σ.st.head 1+k :=
    RecursiveChildCallSetup.savedStacks_pc_head _ _ _
  have hhalf := childFrame_volume_half N hroles σ hok hm i w r hr data
  have hp := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le
    (childFrame (N := N) σ hok hm i w r data).v (childFrame (N := N) σ hok hm i w r data).hpos
  have hpay := Nat.mul_le_mul_left k (show 1+volume prime (childFrame (N := N) σ hok hm i w r data).v ≤ volume prime σ.v by omega)
  have hpayZ : ((k*(1+volume prime (childFrame (N := N) σ hok hm i w r data).v) : ℕ) : ℤ) ≤
      (k*volume prime σ.v : ℕ) := by exact_mod_cast hpay
  dsimp only
  rw [hh]
  push_cast at hpayZ ⊢
  nlinarith only [hpayZ]

/-- This one inequality pays for all retained ancestor payload, node views,
descriptors and return addresses along a live recursive call chain. -/
theorem childFrame_retained_potential_le {b₀ : ℕ} (hroles : 2 ≤ N.roleCount)
    (σ : Frame (pcs N) capacity) (hok : Ok N b₀ σ) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (w : N.World ⊕ N.Temp) (r : ℕ) (hr : r ≤ N.width)
    (data : RecursiveMixedSchedule.Data (tapes N) (roleView N σ.b σ.n σ.v)) :
    let child := childFrame (N := N) σ hok hm i w r data
    child.p+child.node.head 0+child.st.head 0+child.st.head 1+
        ((tapes N+90+k)*volume prime child.v : ℕ) ≤
      σ.p+σ.node.head 0+σ.st.head 0+σ.st.head 1+((tapes N+90+k)*volume prime σ.v : ℕ) := by
  have hp := childFrame_payload_potential_le N hroles σ hok hm i w r hr data
  have hn := childFrame_node_volume_potential_le N hroles σ hok hm i w r hr data
  have hd := childFrame_descriptor_potential_le N hroles σ hok hm i w r hr data
  have hc := childFrame_pc_potential_le N hroles σ hok hm i w r hr data
  dsimp only at hp hn hd hc ⊢
  push_cast at hp hn hd hc ⊢
  nlinarith only [hp,hn,hd,hc]

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
