module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.Rev97Node
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfBankBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalfCallBounds
public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameCallBounds
import all IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameCallBounds

/-! Concrete node-bank offsets and call costs discharge the child-entry margin
condition of the generic recursive workspace theorem. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
open IntegerMultBounds.Machine Networks
open Networks.Shared50ModularControl (prime)
open NodeBank (tapes)
noncomputable section
variable (N : RevNetwork) {k : ℕ}
  (capacity : Fintype.card (Graph.PC (pcs N).length) ≤ 2^k)
  (hR : RevRuns N) (hRk : ∀ r ∈ Rk N, 1 ≤ r ∧ r < N.width) (b₀ : ℕ)
  {core : Graph.Block (CommonBank.count (tapes N)) prime} {coreCost : ℕ → ℕ → ℕ}
  (hcore : Family.LeafCore core (RevNode.Good N) coreCost)

local notation "S" => Family.inv hcore (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width)
  (Rev97Node.half N hR hRk b₀ capacity)

theorem node_head_offsets (σ : (S).Shape) (x₀ : Tapes (CommonBank.count (tapes N)) prime)
    (hx : (S).Entry σ x₀) (hm : N.width ≤ σ.n) (i : ℕ) (y : Tapes (CommonBank.count (tapes N)) prime)
    (hy : (S).Node σ x₀ i y) :
    ∀ n j, (SharedBankStageInput.raw x₀ n).head j-(36*RecursiveInterchangeLayout.volume prime σ.v : ℕ) ≤
        (SharedBankStageInput.raw y n).head j ∧
      (SharedBankStageInput.raw y n).head j ≤ (SharedBankStageInput.raw x₀ n).head j+
        (36*RecursiveInterchangeLayout.volume prime σ.v : ℕ) := by
  obtain ⟨hok,rr,hg,rfl⟩ := hx
  exact node_heads_close N σ hok hm rr hg (Prepare.rest σ.b N.width) i y hy

theorem call_cost_bound (σ : (S).Shape) (x₀ : Tapes (CommonBank.count (tapes N)) prime)
    (hx : (S).Entry σ x₀) (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N))
    (c : Schedule.Call (N.World ⊕ N.Temp)) (hic : (pcs N)[i] = .call c) :
    (S).cCall σ c ≤ callSpaceConstant N k*(S).vol σ := by
  have hr := (hRk c.2 (GraphContract.rank_mem Prod.snd (pcs N) i.val i.isLt c hic)).2.le
  exact callCost_linear N σ hx.1 hm c.1 c.2 hr

theorem child_margin (D : ℕ) (lo hi : ℤ) (hroles : 2 ≤ N.roleCount)
    (hD : 2*(36+callSpaceConstant N k) ≤ D)
    (σ : (S).Shape) (x₀ : Tapes (CommonBank.count (tapes N)) prime) (hx : (S).Entry σ x₀)
    (hmargin : GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x₀)
    (hm : N.width ≤ σ.n) (i : Graph.Site (pcs N)) (c : Schedule.Call (N.World ⊕ N.Temp))
    (hic : (pcs N)[i] = .call c) (y : Tapes (CommonBank.count (tapes N)) prime)
    (hy : (S).Node σ x₀ i.val y) (C : GraphExists.ChildStep S σ x₀ y i c) :
    GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi C.child C.entered := by
  apply GraphExists.child_volume_margin S D 36 (callSpaceConstant N k) lo hi hroles hD
    σ x₀ y i c hic C hmargin
  · exact node_head_offsets N capacity hR hRk b₀ hcore σ x₀ hx hm i.val y hy _
  · exact call_cost_bound N capacity hR hRk b₀ hcore σ x₀ hx hm i c hic

/-- The concrete family needs only its local frame bounds; all child-margin
and recursion obligations are discharged by its proved bank and call bounds. -/
theorem volume_contract (D : ℕ) (lo hi : ℤ) (hroles : 2 ≤ N.roleCount)
    (hD : 2*(36+callSpaceConstant N k) ≤ D)
    (hlocal : ∀ σ x₀, (S).Entry σ x₀ →
      GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x₀ →
      GraphExists.FrameBounds (ht := Family.pcSlot_pos) S σ x₀ lo hi) :
    ∀ σ x₀, (S).Entry σ x₀ → GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x₀ →
      GraphExists.ContractWithin (ht := Family.pcSlot_pos) S
        (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀ := by
  apply GraphExists.contract_within S (GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi)
    lo hi (lt_of_lt_of_le Nat.zero_lt_two N.two_le_width) (fun r hr => (hRk r hr).2) hlocal
  intro σ x₀ hx hs hm i c hic y hy C
  exact child_margin N capacity hR hRk b₀ hcore D lo hi hroles hD σ x₀ hx hs hm i c hic y hy C

/-- Entry uses the node bank's offset and its actual linear execution cost. -/
theorem enter_heads_of_margin (D : ℕ) (lo hi : ℤ) (hD : 36+callSpaceConstant N k ≤ D)
    (σ : (S).Shape) (x₀ : Tapes (CommonBank.count (tapes N)) prime) (hx : (S).Entry σ x₀)
    (hs : GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x₀) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (c : Schedule.Call (N.World ⊕ N.Temp)) (hic : (pcs N)[i] = .call c)
    (y : Tapes (CommonBank.count (tapes N)) prime) (hy : (S).Node σ x₀ i.val y) {z}
    (hz : RunInvariant (NodeCall.enterB N c.1 c.2 (Graph.returnCode (pcs N) capacity i)).program
      (· = SharedBankStageInput.raw y (NodeCall.enterB N c.1 c.2 (Graph.returnCode (pcs N) capacity i)).tapes) z) :
    ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi := by
  exact GraphExists.enter_heads_of_margin S σ x₀ hx hm D 36 (callSpaceConstant N k) lo hi hs
    (fun i y hy => node_head_offsets N capacity hR hRk b₀ hcore σ x₀ hx hm i y hy _)
    (call_cost_bound N capacity hR hRk b₀ hcore σ x₀ hx hm) hD i c hic y hy hz

/-- Recovery uses its exact parent post-bank, with no child-frame decoding. -/
theorem recover_heads_of_margin (D : ℕ) (lo hi : ℤ) (hD : 36+2*callSpaceConstant N k ≤ D)
    (σ : (S).Shape) (x₀ : Tapes (CommonBank.count (tapes N)) prime) (hx : (S).Entry σ x₀)
    (hs : GraphExists.VolumeMargin (ht := Family.pcSlot_pos) S D lo hi σ x₀) (hm : N.width ≤ σ.n)
    (i : Graph.Site (pcs N)) (c : Schedule.Call (N.World ⊕ N.Temp)) (hic : (pcs N)[i] = .call c)
    (y : Tapes (CommonBank.count (tapes N)) prime) (C : GraphExists.ChildStep S σ x₀ y i c)
    (z : Tapes (CommonBank.count (tapes N)) prime) (hz : (S).Exit C.child C.entered z) {d}
    (hd : RunInvariant (NodeCall.recoverB N c.1).program
      (· = SharedBankStageInput.raw z (NodeCall.recoverB N c.1).tapes) d) :
    ∀ j, lo ≤ d.head j ∧ d.head j ≤ hi := by
  exact GraphExists.recover_heads_of_margin S σ x₀ D 36 (callSpaceConstant N k) lo hi hs
    (fun i y hy => node_head_offsets N capacity hR hRk b₀ hcore σ x₀ hx hm i y hy _)
    (call_cost_bound N capacity hR hRk b₀ hcore σ x₀ hx hm) hD i c hic y C z hz hd

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.RevHalf
