module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameVolumeWithin
public import IntegerMultBounds.Machine.RunInvariantPostBounds

/-! Call entry is bounded from the parent node bank; recovery is bounded from
its exact parent post-bank. Child-stack decoding is unnecessary for either bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph
open SharedBankStageInput (raw)
noncomputable section
private theorem raw_head_castLE {s u n a : ℕ} (x : Tapes s a) (h : u ≤ n) (j : Fin u) :
    (raw x n).head (Fin.castLE h j) = (raw x u).head j := by
  rfl

variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)
  (σ : S.Shape) (x₀ : Tapes t a) (hx : S.Entry σ x₀) (hm : m ≤ S.size σ)
  (D nodeCost callCost : ℕ) (lo hi : ℤ)
  (hmargin : VolumeMargin (ht := ht) S D lo hi σ x₀)
  (hnodes : ∀ i y, S.Node σ x₀ i y → ∀ j,
    (raw x₀ (tapeCount pieces capacity stack ht impl)).head j-(nodeCost*S.vol σ : ℕ) ≤
      (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
    (raw y (tapeCount pieces capacity stack ht impl)).head j ≤
      (raw x₀ (tapeCount pieces capacity stack ht impl)).head j+(nodeCost*S.vol σ : ℕ))
  (hcost : ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → S.cCall σ c ≤ callCost*S.vol σ)

include hx hm hmargin hnodes hcost

theorem enter_heads_of_margin (hD : nodeCost+callCost ≤ D)
    (i : Site pieces) (c : Call) (hic : pieces[i] = .call c) (y : Tapes t a) (hy : S.Node σ x₀ i.val y)
    {z} (hz : RunInvariant (impl.enter c (returnCode pieces capacity i)).program
      (· = raw y (impl.enter c (returnCode pieces capacity i)).tapes) z) :
    ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi := by
  obtain ⟨C⟩ := child_step S σ x₀ y hx hm i c hic hy
  have hb : block pieces capacity stack ht impl (.piece i) = impl.enter c (returnCode pieces capacity i) := by
    simp only [block,hic]
  have hle : (impl.enter c (returnCode pieces capacity i)).tapes ≤ tapeCount pieces capacity stack ht impl := by
    rw [←hb]; exact SharedBankFamily.block_le _ _
  have hE : C.enterCost ≤ callCost*S.vol σ := by have := C.cost; have := hcost i c hic; omega
  have hbudget := Nat.mul_le_mul_right (S.vol σ) hD
  rw [Nat.add_mul] at hbudget
  intro j
  let j' := Fin.castLE hle j
  have hn := hnodes i.val y hy j'
  have hm := hmargin j'
  have he := hz.heads_eq C.enter j
  have hraw : (raw y (tapeCount pieces capacity stack ht impl)).head j' =
      (raw y (impl.enter c (returnCode pieces capacity i)).tapes).head j := raw_head_castLE y hle j
  rw [hraw] at hn
  omega

omit hx hm in
theorem recover_heads_of_margin (hD : nodeCost+2*callCost ≤ D)
    (i : Site pieces) (c : Call) (hic : pieces[i] = .call c) (y : Tapes t a)
    (C : ChildStep S σ x₀ y i c) (z : Tapes t a) (hz : S.Exit C.child C.entered z)
    {d} (hd : RunInvariant (impl.recover c).program (· = raw z (impl.recover c).tapes) d) :
    ∀ j, lo ≤ d.head j ∧ d.head j ≤ hi := by
  obtain ⟨y',hy',hr⟩ := C.recover z hz
  have hb : block pieces capacity stack ht impl (.recover i) = impl.recover c := by simp only [block,hic]
  have hle : (impl.recover c).tapes ≤ tapeCount pieces capacity stack ht impl := by
    rw [←hb]; exact SharedBankFamily.block_le _ _
  have hR : C.recoverCost ≤ callCost*S.vol σ := by have := C.cost; have := hcost i c hic; omega
  have hR₂ := Nat.mul_le_mul_left 2 hR
  have hbudget := Nat.mul_le_mul_right (S.vol σ) hD
  rw [Nat.add_mul,Nat.mul_assoc] at hbudget
  intro j
  let j' := Fin.castLE hle j
  have hn := hnodes (i.val+1) y' hy' j'
  have hm := hmargin j'
  have he := hd.heads_eq_post hr j
  have hraw : (raw y' (tapeCount pieces capacity stack ht impl)).head j' =
      (raw y' (impl.recover c).tapes).head j := raw_head_castLE y' hle j
  rw [hraw] at hn
  omega

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
