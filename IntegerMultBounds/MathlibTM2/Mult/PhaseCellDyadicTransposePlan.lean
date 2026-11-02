module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRectangularChunkLayout

/-! Euclidean plans for rectangular dyadic transposes. Peeling equal bit fields
avoids padding the replica dimension to a power of the key dimension. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host

private theorem runRectangularChunkSwaps_inverse_eq {α : Type*}
    (H K W : ℕ) (fill : α) (rs : List RectangularChunkSwap)
    (hvolume : ∀ r ∈ rs, r.volume = H*K*W)
    (hrun : ∀ ys : List α, ys.length = H*K*W →
      runRectangularChunkSwaps fill rs ys = swapList 1 H 1 K W fill ys)
    (xs : List α) (hlen : xs.length = K*H*W) :
    runRectangularChunkSwaps fill (rs.reverse.map RectangularChunkSwap.inverse) xs =
      swapList 1 K 1 H W fill xs := by
  let ys := swapList 1 K 1 H W fill xs
  have hy : ys.length = H*K*W := by simp [ys,swapList,Nat.mul_assoc]
  have hh := runRectangularChunkSwaps_reverse_cancel fill rs (H*K*W) hvolume ys hy
  rw [hrun ys hy] at hh
  have hi := swapList_involution (P := 1) (H := K) (G := 1) (D := H) (B := W)
    fill xs (by simpa only [BinaryAdjacentWidthInterchange.volume,Nat.one_mul,Nat.mul_one] using hlen)
  dsimp only [ys] at hh
  rw [hi] at hh
  exact hh

private theorem replicaKey_swap_factor_inverse {α : Type*} (H N K W : ℕ)
    (fill : α) (xs : List α) (hlen : xs.length = K*(H*N)*W) :
    swapList H K 1 N W fill (swapList 1 K 1 H (N*W) fill xs) =
      swapList 1 K 1 (H*N) W fill xs := by
  have hh := runRectangularChunkSwaps_inverse_eq (H*N) K W fill
    [⟨H,N,K,W⟩,⟨1,H,K,N*W⟩]
    (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl <;> dsimp only [RectangularChunkSwap.volume] <;> ring)
    (by
      intro ys hy
      exact replicaKey_swap_factor fill ys (by simpa only [Nat.mul_assoc] using hy)) xs hlen
  simpa [RectangularChunkSwap.inverse,runRectangularChunkSwaps] using hh

/-- The indices describe the two bit widths and the trailing symbol block.
A plan records only the structural decomposition, not payload data. -/
inductive DyadicTransposePlan : ℕ → ℕ → ℕ → Type
  | zeroLeft (b W : ℕ) : DyadicTransposePlan 0 b W
  | zeroRight (a W : ℕ) : DyadicTransposePlan a 0 W
  | left {a b W : ℕ} (hb : 0 < b) (rest : DyadicTransposePlan a b (2^b*W)) :
      DyadicTransposePlan (a+b) b W
  | right {a b W : ℕ} (ha : 0 < a) (rest : DyadicTransposePlan b a (2^a*W)) :
      DyadicTransposePlan a (a+b) W

def DyadicTransposePlan.stages {a b W : ℕ} :
    DyadicTransposePlan a b W → List RectangularChunkSwap
  | .zeroLeft _ _ => []
  | .zeroRight _ _ => []
  | .left (a := a) (b := b) (W := W) _ rest =>
      ⟨2^a,2^b,2^b,W⟩::rest.stages
  | .right (a := a) (b := b) (W := W) _ rest =>
      (rest.stages.reverse.map RectangularChunkSwap.inverse)++[⟨2^b,2^a,2^a,W⟩]

/-- Sum of the swapped bit widths; useful for paying the residual route
without assigning the largest width to all of its smaller stages. -/
def DyadicTransposePlan.widthCharge {a b W : ℕ} : DyadicTransposePlan a b W → ℕ
  | .zeroLeft _ _ => 0
  | .zeroRight _ _ => 0
  | .left (b := b) _ rest => b+rest.widthCharge
  | .right (a := a) _ rest => a+rest.widthCharge

theorem DyadicTransposePlan.widthCharge_le {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    plan.widthCharge ≤ a+b := by
  induction plan with
  | zeroLeft => simp [widthCharge]
  | zeroRight => simp [widthCharge]
  | left hb rest ih => simp only [widthCharge]; omega
  | right ha rest ih => simp only [widthCharge]; omega

theorem DyadicTransposePlan.stages_length_le {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    plan.stages.length ≤ plan.widthCharge := by
  induction plan with
  | zeroLeft => simp [stages,widthCharge]
  | zeroRight => simp [stages,widthCharge]
  | left hb rest ih => simp only [stages,widthCharge,List.length_cons]; omega
  | right ha rest ih =>
    simp only [stages,widthCharge,List.length_append,List.length_map,List.length_reverse,List.length_singleton]
    omega

theorem DyadicTransposePlan.stages_equalWidth {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    ∀ r ∈ plan.stages, r.leftWidth = r.rightWidth := by
  induction plan with
  | zeroLeft => simp [stages]
  | zeroRight => simp [stages]
  | left hb rest ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r; rfl
    · exact ih r hr
  | right ha rest ih =>
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      exact (ih s (List.mem_reverse.mp hs)).symm
    · have he := List.mem_singleton.mp hr
      subst r; rfl

theorem DyadicTransposePlan.stages_bits {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    ∀ r ∈ plan.stages, ∃ k : ℕ, 0 < k ∧ k ≤ min a b ∧
      r.leftWidth = 2^k ∧ r.rightWidth = 2^k := by
  induction plan with
  | zeroLeft => simp [stages]
  | zeroRight => simp [stages]
  | @left a b W hb rest ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r; exact ⟨b,hb,by omega,rfl,rfl⟩
    · obtain ⟨k,hk,hbound,hl,hr⟩ := ih r hr
      exact ⟨k,hk,by omega,hl,hr⟩
  | @right a b W ha rest ih =>
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      obtain ⟨k,hk,hbound,hl,hr⟩ := ih s (List.mem_reverse.mp hs)
      exact ⟨k,hk,by omega,hr,hl⟩
    · have he := List.mem_singleton.mp hr
      subst r; exact ⟨a,ha,by omega,rfl,rfl⟩

theorem DyadicTransposePlan.stages_volume {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    ∀ r ∈ plan.stages, r.volume = 2^a*2^b*W := by
  induction plan with
  | zeroLeft => simp [stages]
  | zeroRight => simp [stages]
  | @left a b W hb rest ih =>
    intro r hr
    rcases List.mem_cons.mp hr with he | hr
    · subst r; simp only [RectangularChunkSwap.volume,pow_add]
    · rw [ih r hr,pow_add]; ring
  | @right a b W ha rest ih =>
    intro r hr
    rcases List.mem_append.mp hr with hr | hr
    · obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
      have hh := ih s (List.mem_reverse.mp hs)
      dsimp only [RectangularChunkSwap.volume,RectangularChunkSwap.inverse] at hh ⊢
      rw [pow_add]
      nlinarith only [hh]
    · have he := List.mem_singleton.mp hr
      subst r; simp only [RectangularChunkSwap.volume,pow_add]; ring

theorem DyadicTransposePlan.run_eq {a b W : ℕ} (plan : DyadicTransposePlan a b W)
    {α : Type*} (fill : α) (xs : List α) (hlen : xs.length = 2^a*2^b*W) :
    runRectangularChunkSwaps fill plan.stages xs = swapList 1 (2^a) 1 (2^b) W fill xs := by
  induction plan generalizing xs with
  | zeroLeft b W =>
    simpa only [stages,runRectangularChunkSwaps,pow_zero,replicaChunkSwaps,
      runReplicaChunkSwaps] using runReplicaChunkSwaps_eq (2^b) W 0 fill xs (by simpa using hlen)
  | zeroRight a W =>
    have hz : swapList 1 1 1 (2^a) W fill xs = xs := by
      simpa only [pow_zero,replicaChunkSwaps,runReplicaChunkSwaps] using
        (runReplicaChunkSwaps_eq (2^a) W 0 fill xs (by simpa using hlen)).symm
    have hi := swapList_involution (P := 1) (H := 1) (G := 1) (D := 2^a) (B := W)
      fill xs (by simpa [BinaryAdjacentWidthInterchange.volume] using hlen)
    rw [hz] at hi
    exact hi.symm
  | @left a b W hb rest ih =>
    simp only [stages,runRectangularChunkSwaps]
    rw [ih _ (by simp [swapList,Nat.mul_assoc])]
    simpa only [pow_add] using replicaKey_swap_factor (H := 2^a) (N := 2^b)
      fill xs (by simpa only [pow_add] using hlen)
  | @right a b W ha rest ih =>
    rw [stages,runRectangularChunkSwaps_append]
    have hinv := runRectangularChunkSwaps_inverse_eq (2^b) (2^a) (2^a*W) fill
      rest.stages rest.stages_volume (fun ys hy => ih ys hy) xs
      (by simpa only [pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hlen)
    rw [hinv]
    change swapList (2^b) (2^a) 1 (2^a) W fill
      (swapList 1 (2^a) 1 (2^b) (2^a*W) fill xs) = _
    simpa only [pow_add,Nat.mul_comm] using replicaKey_swap_factor_inverse (2^b) (2^a) (2^a) W fill xs
      (by simpa only [pow_add,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using hlen)

theorem DyadicTransposePlan.run_words {a b W : ℕ} (plan : DyadicTransposePlan a b W)
    {α : Type*} (fill : α) (f : Fin (2^a) → Fin (2^b) → Fin W → α) :
    runRectangularChunkSwaps fill plan.stages (replicaKeyWords f) = keyReplicaWords f := by
  rw [plan.run_eq fill _ (by simp [replicaKeyWords,Nat.mul_assoc])]
  exact replicaKeyWords_swap fill f

theorem DyadicTransposePlan.run_inverse_words {a b W : ℕ} (plan : DyadicTransposePlan a b W)
    {α : Type*} (fill : α) (f : Fin (2^a) → Fin (2^b) → Fin W → α) :
    runRectangularChunkSwaps fill (plan.stages.reverse.map RectangularChunkSwap.inverse)
      (keyReplicaWords f) = replicaKeyWords f := by
  have hh := runRectangularChunkSwaps_reverse_cancel fill plan.stages (2^a*2^b*W)
    plan.stages_volume (replicaKeyWords f) (by simp [replicaKeyWords,Nat.mul_assoc])
  rwa [plan.run_words] at hh

/-- Structural recursion on fuel constructs every dyadic rectangle. Fuel is
not part of the emitted physical schedule. -/
def dyadicTransposePlan (fuel a b W : ℕ) (h : a+b ≤ fuel) : DyadicTransposePlan a b W :=
  match fuel with
  | 0 => by
      have ha : a = 0 := by omega
      subst a
      exact .zeroLeft b W
  | fuel+1 =>
      if ha : a = 0 then ha ▸ .zeroLeft b W
      else if hb : b = 0 then hb ▸ .zeroRight a W
      else if hba : b ≤ a then
        (Nat.sub_add_cancel hba) ▸
          .left (by omega) (dyadicTransposePlan fuel (a-b) b (2^b*W) (by omega))
      else
        (Nat.add_sub_of_le (by omega : a ≤ b)) ▸
          .right (by omega) (dyadicTransposePlan fuel (b-a) a (2^a*W) (by omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
