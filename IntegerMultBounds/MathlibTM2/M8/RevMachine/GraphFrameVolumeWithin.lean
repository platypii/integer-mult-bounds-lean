module

public import IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphFrameWithin
public import IntegerMultBounds.Machine.HoareHeadChange

/-! Geometric volume shrinkage pays for child entry inside one root-relative
head interval. Sibling count and elapsed runtime never multiply workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
open IntegerMultBounds.Machine Graph
open SharedBankStageInput (raw)
noncomputable section
variable {Seg Call : Type} {t a k : ℕ} {pieces : List (Piece Seg Call)}
  {capacity : Fintype.card (PC pieces.length) ≤ 2^k} {stack : Fin t} {ht : 0 < t}
  {impl : Implementation t a k Seg Call} {m W : ℕ} {rank : Call → ℕ}
  (S : Inv pieces capacity stack impl m W rank)

/-- A frame's active volume reserves its remaining workspace inside fixed root bounds. -/
def VolumeMargin (D : ℕ) (lo hi : ℤ) (σ : S.Shape) (x₀ : Tapes t a) : Prop :=
  ∀ j, lo+(D*S.vol σ : ℕ) ≤ (raw x₀ (tapeCount pieces capacity stack ht impl)).head j ∧
    (raw x₀ (tapeCount pieces capacity stack ht impl)).head j+(D*S.vol σ : ℕ) ≤ hi

theorem child_volume_margin (D nodeCost callCost : ℕ) (lo hi : ℤ)
    (hW : 2 ≤ W) (hD : 2*(nodeCost+callCost) ≤ D)
    (σ : S.Shape) (x₀ y : Tapes t a) (i : Site pieces) (c : Call) (hic : pieces[i] = .call c)
    (C : ChildStep S σ x₀ y i c)
    (hmargin : VolumeMargin (ht := ht) S D lo hi σ x₀)
    (hnode : ∀ j,
      (raw x₀ (tapeCount pieces capacity stack ht impl)).head j-(nodeCost*S.vol σ : ℕ) ≤
        (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
      (raw y (tapeCount pieces capacity stack ht impl)).head j ≤
        (raw x₀ (tapeCount pieces capacity stack ht impl)).head j+(nodeCost*S.vol σ : ℕ))
    (hcost : S.cCall σ c ≤ callCost*S.vol σ) :
    VolumeMargin (ht := ht) S D lo hi C.child C.entered := by
  have hblock : block pieces capacity stack ht impl (.piece i) = impl.enter c (returnCode pieces capacity i) := by
    simp only [block,hic]
  have hle : (impl.enter c (returnCode pieces capacity i)).tapes ≤ tapeCount pieces capacity stack ht impl := by
    rw [←hblock]
    exact SharedBankFamily.block_le _ _
  have hp := SharedBankFamily.pad_realizes hle (SharedBankFamily.common_le _) y C.entered C.enterCost C.enter
  have he := HoareTime.head_change hp
  have hhalf : 2*S.vol C.child ≤ S.vol σ := by
    have hWp : (W : ℝ) ≠ 0 := by exact_mod_cast (show W ≠ 0 by omega)
    have hv := (eq_div_iff hWp).mp C.volume
    have hWr : (2 : ℝ) ≤ W := by exact_mod_cast hW
    have : (2 : ℝ)*S.vol C.child ≤ S.vol σ := by
      nlinarith only [hv,hWr,(show (0 : ℝ) ≤ S.vol C.child from Nat.cast_nonneg _)]
    exact_mod_cast this
  have hbudget : (nodeCost+callCost)*S.vol σ+D*S.vol C.child ≤ D*S.vol σ := by
    have h₁ := Nat.mul_le_mul_right (S.vol σ) hD
    have h₂ := Nat.mul_le_mul_left D hhalf
    nlinarith only [h₁,h₂]
  have hE : C.enterCost ≤ callCost*S.vol σ := by have := C.cost; omega
  intro j
  have hm := hmargin j
  have hn := hnode j
  have hc := he j
  dsimp only [VolumeMargin] at *
  rw [Nat.add_mul] at hbudget
  omega

/-- The family workspace theorem reduces to local block bounds, node-bank head
positions and a linear entry/recovery cost, all on the existing frame shapes. -/
theorem contract_volume_within (D nodeCost callCost : ℕ) (lo hi : ℤ)
    (hm : 0 < m) (hW : 2 ≤ W) (hD : 2*(nodeCost+callCost) ≤ D)
    (hrank : ∀ r ∈ GraphContract.ranks rank pieces, r < m)
    (hlocal : ∀ σ x₀, S.Entry σ x₀ → VolumeMargin (ht := ht) S D lo hi σ x₀ →
      FrameBounds (ht := ht) S σ x₀ lo hi)
    (hnode : ∀ σ x₀, S.Entry σ x₀ → ∀ i y, S.Node σ x₀ i y → ∀ j,
      (raw x₀ (tapeCount pieces capacity stack ht impl)).head j-(nodeCost*S.vol σ : ℕ) ≤
        (raw y (tapeCount pieces capacity stack ht impl)).head j ∧
      (raw y (tapeCount pieces capacity stack ht impl)).head j ≤
        (raw x₀ (tapeCount pieces capacity stack ht impl)).head j+(nodeCost*S.vol σ : ℕ))
    (hcost : ∀ σ x₀, S.Entry σ x₀ → m ≤ S.size σ →
      ∀ (i : Site pieces) (c : Call), pieces[i] = .call c → S.cCall σ c ≤ callCost*S.vol σ) :
    ∀ σ x₀, S.Entry σ x₀ → VolumeMargin (ht := ht) S D lo hi σ x₀ →
      ContractWithin (ht := ht) S (fun v => ∀ j, lo ≤ v.head j ∧ v.head j ≤ hi) σ x₀ := by
  apply contract_within S (VolumeMargin (ht := ht) S D lo hi) lo hi hm hrank hlocal
  intro σ x₀ hx hs hnodeSize i c hic y hy C
  exact child_volume_margin S D nodeCost callCost lo hi hW hD σ x₀ y i c hic C hs
    (hnode σ x₀ hx i.val y hy) (hcost σ x₀ hx hnodeSize i c hic)

end
end IntegerMultBounds.MathlibTM2.M8.RevMachine.GraphExists
