module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfOrdinaryMargin
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfFrameSpace

/-! All local frame obligations follow from actual block certificates and one
entry reserve. The core remains abstract until the concrete final instantiation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open Family (Frame)
open NodeBank (tapes)
open NodeSplit (roleView midView)
open SharedBankStageInput (raw)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  (capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k)
  (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ : ℕ)
  {core : Graph.Block (CommonBank.count (tapes N)) prime} {coreCost : ℕ → ℕ → ℕ} {C : ℕ}
  (hcore : Family.LeafCore core (RevNode.Good N) coreCost)
  (hspace : Family.CoreSpace core (RevNode.Good N) C)

local notation "S" => Family.inv hcore (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width)
  (Rev97Node.half N hR hRk b₀ capacity)

include hspace in
theorem frame_bounds (D : ℕ) (hD : FrameReserve N k C D) (lo upper : ℤ)
    (σ : (S).Shape) (hn : 1 ≤ σ.n) (x : Tapes (CommonBank.count (tapes N)) prime) (hx : (S).Entry σ x)
    (hs : GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo upper σ x) :
    GraphExists.FrameBounds (ht := Family.pcSlot_pos) S σ x lo upper := by
  have hV := RecursiveAffinePrepare.volume_positive Shared50ModularControl.prime_prime.two_le σ.v σ.hpos
  have hraw : ∀ n j, lo+(D*volume prime σ.v : ℕ) ≤ (raw x n).head j ∧
      (raw x n).head j+(D*volume prime σ.v : ℕ) ≤ upper :=
    GraphExists.volume_margin_raw S D lo upper σ x hs
  have hzero := hraw (CommonBank.count (tapes N)+1) (Fin.last (CommonBank.count (tapes N)))
  simp only [raw,Fin.val_last,lt_self_iff_false,↓reduceDIte] at hzero
  refine { lower_nonpos := by omega
           upper_nonneg := by omega
           prepare := ?_
           leaf := ?_
           test := ?_
           split := ?_
           segment := ?_
           enter := ?_
           recover := ?_
           merge := ?_
           finish := ?_
           pop := ?_ }
  · intro z hz j
    obtain ⟨hok,rr,hg,rfl⟩ := hx
    have ht := Family.prepare_runs (m := N.width) (roles := rr) (f := σ.f) (p := σ.p) (node := σ.node)
      (scalar := σ.scalar) (st := σ.st) σ.hb (by have := N.two_le_width; omega) σ.hw
    have hc := preparation_cost_bound N σ.v σ.hpos σ.b σ.n σ.hb hn σ.hw
    have hb := Nat.mul_le_mul_right (volume prime σ.v) hD.prepare
    change RunInvariant (Family.prepare (T := tapes N)).program
      (· = raw (σ.at rr (Prepare.rest σ.b N.width)) (Family.prepare (T := tapes N)).tapes) z at hz
    dsimp only [Family.Frame.at] at hz
    have hp := hz.heads_eq ht j
    have hm := hraw (Family.prepare (T := tapes N)).tapes j
    dsimp only [Family.Frame.at] at hm
    omega
  · intro i hi y hy z hz
    change i < σ.n % N.width at hi
    obtain ⟨roles,hg,rfl⟩ := hy
    have hb : Family.leafSpaceConstant C*volume prime σ.v+1 ≤ D*volume prime σ.v := by
      have h := Nat.mul_le_mul_right (volume prime σ.v) hD.leaf
      rw [Nat.add_mul] at h
      omega
    have hm := ordinary_bank_margin N capacity hR hRk b₀ hcore D
      (Family.leafSpaceConstant C*volume prime σ.v) lo upper σ x hx hs roles hg
      (Family.leafC σ.b N.width σ.n (σ.n % N.width-i)) hb
    obtain ⟨roles',hg',h⟩ := Family.leaf_runs_within (m := N.width) (r := σ.n % N.width-i)
      hcore hspace σ.hpos σ.hb σ.hw (by omega) (by have := Nat.mod_le σ.n N.width; omega)
      σ.hfree hg lo upper (by simpa only [Family.Frame.at] using hm)
    exact h.invariant hz
  · intro i hi y hy
    obtain ⟨roles,hg,rfl⟩ := hy
    have hm := ordinary_bank_margin N capacity hR hRk b₀ hcore D 1 lo upper σ x hx hs roles hg
      (Family.leafC σ.b N.width σ.n (σ.n % N.width-i)) (by
        have h := Nat.mul_le_mul_right (volume prime σ.v) hD.finish
        omega)
    exact hm _
  · intro hn y hy z hz j
    change N.width ≤ σ.n at hn
    obtain ⟨roles,hg,rfl⟩ := hy
    have hb : NodeSplit.splitSpaceConstant N*volume prime σ.v+1 ≤ D*volume prime σ.v := by
      have h := Nat.mul_le_mul_right (volume prime σ.v) hD.split
      rw [Nat.add_mul] at h
      omega
    have hm := ordinary_bank_margin N capacity hR hRk b₀ hcore D
      (NodeSplit.splitSpaceConstant N*volume prime σ.v) lo upper σ x hx hs roles hg
      (Family.leafC σ.b N.width σ.n 0) hb (NodeSplit.splitB N).tapes j
    obtain ⟨hp,data,rfl⟩ := hg
    dsimp only [Family.inv] at hz
    simp only [Nat.sub_self] at hz
    have hh := NodeSplit.split_heads N σ.v σ.hpos σ.b σ.n σ.hb σ.hw hn (rows_dvd hx.1 hn)
      (Shared50RecursiveNodeSemantics.encoded data) σ.f σ.p σ.node σ.scalar σ.st hz j
    dsimp only [Family.Frame.at] at hm
    omega
  · intro hn i s hi y hy z hz j
    change N.width ≤ σ.n at hn
    have hv := NodeSplit.viewBounds N σ.v σ.hpos σ.b σ.n σ.hb σ.hw (rows_dvd hx.1 hn)
    have hc := segment_space_le N i s hi
    have hb := Nat.mul_le_mul_right (volume prime σ.v) hD.segment
    rw [Nat.add_mul] at hb
    have hvol := Nat.mul_le_mul_left (RevNode.segSpaceConstant N s) hv.role
    have hle := Nat.mul_le_mul_right (volume prime σ.v) hc
    have hm := hraw (RevNode.segB N s).tapes j
    have ho := node_head_offsets N capacity hR hRk b₀ hcore σ x hx hn i.val y hy (RevNode.segB N s).tapes j
    obtain ⟨data,hinv,rfl⟩ := hy
    have hf : 0 < σ.n/N.width := Nat.div_pos hn (by have := N.two_le_width; omega)
    have hh := RevNode.seg_heads N s σ.hb hf _ rfl hv.rolePos _ (Routines.hdr_headers _)
      σ.f σ.p (RecursiveViewFrame.savedStack (Routines.hdr (midView N σ.b σ.n σ.v))
        (RecursiveViewFrame.savedStack (Routines.hdr σ.v) σ.node)) σ.scalar _ σ.st
      (RevNode.nodeC_segCounters N σ.b (σ.n/N.width)) data z hz j
    omega
  · intro hn i c hi y hy z hz
    exact enter_heads_of_margin N capacity hR hRk b₀ hcore D lo upper
      (by have := hD.call; omega) σ x hx hs hn i c hi y hy hz
  · intro hn i c hi y hy step z hz d hd
    exact recover_heads_of_margin N capacity hR hRk b₀ hcore D lo upper
      (by have := hD.call; omega) σ x hx hs hn i c hi y step z hz hd
  · intro hn y hy z hz j
    change N.width ≤ σ.n at hn
    have hv := NodeSplit.viewBounds N σ.v σ.hpos σ.b σ.n σ.hb σ.hw (rows_dvd hx.1 hn)
    have hb := Nat.mul_le_mul_right (volume prime σ.v) hD.merge
    rw [Nat.add_mul] at hb
    have hm := hraw (NodeSplit.mergeB N).tapes j
    have ho := node_head_offsets N capacity hR hRk b₀ hcore σ x hx hn (pcs N).length y hy (NodeSplit.mergeB N).tapes j
    obtain ⟨data,hinv,rfl⟩ := hy
    have hh := NodeSplit.merge_heads N σ.v σ.hpos σ.b σ.n σ.hb (by have := N.two_le_width; omega)
      σ.hw (rows_dvd hx.1 hn) data hinv σ.f σ.p σ.node σ.scalar σ.st σ.hfree hz j
    omega
  · intro y hy z hz j
    obtain ⟨roles,hg,rfl⟩ := hy
    have hb : 22*volume prime σ.v+1 ≤ D*volume prime σ.v := by
      have h := Nat.mul_le_mul_right (volume prime σ.v) hD.finish
      omega
    have hm := ordinary_bank_margin N capacity hR hRk b₀ hcore D (22*volume prime σ.v)
      lo upper σ x hx hs roles hg (Family.leafC σ.b N.width σ.n 0) hb Prepare.finish.tapes j
    have hh := Family.finish_heads σ.v σ.hpos σ.b N.width σ.n σ.hb σ.hw roles σ.f σ.p
      σ.node σ.scalar σ.st hz j
    dsimp only [Family.Frame.at] at hm
    omega
  · intro y hy
    obtain ⟨roles,hg,rfl⟩ := hy
    have hm := ordinary_bank_margin N capacity hR hRk b₀ hcore D (k+1) lo upper σ x hx hs roles hg
      (Prepare.rest σ.b N.width) (by
        have h := Nat.mul_le_mul_right (volume prime σ.v) hD.pop
        nlinarith only [h,hV])
    exact hm _

include hspace in
/-- Geometric child shrinkage closes the recursion with these concrete local
frame certificates; no child execution premise remains. -/
theorem frame_contract_within (D : ℕ) (hD : FrameReserve N k C D)
    (lo upper : ℤ) (hroles : 2 ≤ N.roleCount) :
    ∀ σ x, 1 ≤ σ.n → (S).Entry σ x → GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo upper σ x →
      GraphExists.ContractWithin (ht := Family.pcSlot_pos) S
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ upper) σ x := by
  have hc := GraphExists.contract_within S
    (fun σ x => 1 ≤ σ.n ∧ GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo upper σ x)
    lo upper (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width)
    (fun r hr => (hRk r hr).2)
    (fun σ x hx hs => frame_bounds N capacity hR hRk b₀ hcore hspace D hD lo upper σ hs.1 x hx hs.2)
    (by
      intro σ x hx hs hm i c hi y hy step
      have hr := (hRk c.2 (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt c hi)).1
      have hf : 0 < σ.n/N.width := Nat.div_pos hm (by have := N.two_le_width; omega)
      refine ⟨?_,child_margin N capacity hR hRk b₀ hcore D lo upper hroles hD.call σ x hx hs.2 hm i c hi y hy step⟩
      have hp := Nat.mul_pos (show 0 < c.2 by omega) hf
      have he := step.size
      change step.child.n = c.2*(σ.n/N.width) at he
      omega)
  intro σ x hn hx hs
  exact hc σ x hx ⟨hn,hs⟩

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
