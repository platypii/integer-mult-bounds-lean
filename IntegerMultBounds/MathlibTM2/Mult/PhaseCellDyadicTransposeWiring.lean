module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicTransposePlan
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBalancedChunkInterchangeLoop
public import Mathlib.Data.Nat.Log

/-! Attach borrowed dimension masters to an exact dyadic transpose plan.
All mathematical stage obligations follow from the structural plan. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Host

def DyadicTransposePlan.wiredStages {a b W T : ℕ} (plan : DyadicTransposePlan a b W)
    (dims : RectangularChunkSwap → Fin 5 → Fin T) : List (BalancedChunkInterchangeStage T) :=
  plan.stages.map fun r => ⟨dims r,r.outerCount,r.blockWidth,Nat.log 2 r.leftWidth,Nat.log 2 r.leftWidth⟩

theorem DyadicTransposePlan.wiredStages_shape {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T) :
    (plan.wiredStages dims).map BalancedChunkInterchangeStage.shape = plan.stages := by
  rw [wiredStages,List.map_map]
  conv_rhs => rw [← List.map_id plan.stages]
  apply List.map_congr_left
  intro r hr
  obtain ⟨k,hk,hbound,hl,hr⟩ := plan.stages_bits r hr
  cases r
  simp only [BalancedChunkInterchangeStage.shape,Function.comp_apply] at *
  simp only [hl,Nat.log_pow (by decide : 1 < 2),hr,id_eq]

theorem DyadicTransposePlan.wiredStages_bits {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T)
    (xs : List Bool) :
    balancedChunkStageBits (plan.wiredStages dims) xs = runRectangularChunkSwaps false plan.stages xs := by
  rw [balancedChunkStageBits_eq,plan.wiredStages_shape]

theorem DyadicTransposePlan.wiredStages_words {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T)
    (f : Fin (2^a) → Fin (2^b) → Fin W → Bool) :
    balancedChunkStageBits (plan.wiredStages dims) (replicaKeyWords f) = keyReplicaWords f := by
  rw [plan.wiredStages_bits]
  exact plan.run_words false f

theorem DyadicTransposePlan.stages_bitSum {a b W : ℕ} (plan : DyadicTransposePlan a b W) :
    (plan.stages.map (fun r => Nat.log 2 r.leftWidth)).sum = plan.widthCharge := by
  induction plan with
  | zeroLeft => rfl
  | zeroRight => rfl
  | left hb rest ih =>
    simp only [DyadicTransposePlan.stages,List.map_cons,List.sum_cons,
      Nat.log_pow (by decide : 1 < 2),DyadicTransposePlan.widthCharge,ih]
  | right ha rest ih =>
    have he : ((rest.stages.reverse.map RectangularChunkSwap.inverse).map
        (fun r => Nat.log 2 r.leftWidth)).sum =
        (rest.stages.map (fun r => Nat.log 2 r.leftWidth)).sum := by
      rw [List.map_map]
      dsimp only [Function.comp_def]
      have hm : rest.stages.reverse.map (fun r => Nat.log 2 r.inverse.leftWidth) =
          rest.stages.reverse.map (fun r => Nat.log 2 r.leftWidth) := by
        apply List.map_congr_left
        intro r hr
        dsimp only [RectangularChunkSwap.inverse]
        rw [rest.stages_equalWidth r (List.mem_reverse.mp hr)]
      rw [hm,List.map_reverse,List.sum_reverse]
    simp only [DyadicTransposePlan.stages,List.map_append,List.sum_append,he,
      List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,Nat.add_zero,
      Nat.log_pow (by decide : 1 < 2),DyadicTransposePlan.widthCharge,ih]
    omega

theorem DyadicTransposePlan.wiredStages_bitSum {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T) :
    ((plan.wiredStages dims).map (fun r => r.leftBits)).sum = plan.widthCharge := by
  simpa only [wiredStages,List.map_map,Function.comp_def] using plan.stages_bitSum

/-- The remaining physical premises concern actual tape wiring and contents;
balance, positivity and common volume are consequences of the plan. -/
theorem DyadicTransposePlan.wiredStages_ready {a b W T : ℕ}
    (plan : DyadicTransposePlan a b W) (dims : RectangularChunkSwap → Fin 5 → Fin T)
    (hW : 0 < W) :
    ∀ r ∈ plan.wiredStages dims,
      (0 < r.outerCount ∧ 0 < r.blockWidth) ∧
      (r.leftBits ≤ r.rightBits+1 ∧ r.rightBits ≤ r.leftBits+1) ∧
      2^a*2^b*W = BinaryAdjacentWidthInterchange.volume r.outerCount
        (2^r.leftBits) 1 (2^r.rightBits) r.blockWidth := by
  intro r hr
  obtain ⟨s,hs,rfl⟩ := List.mem_map.mp hr
  obtain ⟨k,hk,hbound,hl,hr⟩ := plan.stages_bits s hs
  have hv := plan.stages_volume s hs
  have hpos : 0 < 2^a*2^b*W := Nat.mul_pos (Nat.mul_pos (pow_pos (by decide : 0 < 2) a) (pow_pos (by decide : 0 < 2) b)) hW
  have ho : 0 < s.outerCount := by
    by_contra hh
    have hz : s.outerCount = 0 := by omega
    simp only [RectangularChunkSwap.volume,hz,Nat.zero_mul] at hv
    omega
  have hb : 0 < s.blockWidth := by
    by_contra hh
    have hz : s.blockWidth = 0 := by omega
    simp only [RectangularChunkSwap.volume,hz,Nat.mul_zero] at hv
    omega
  refine ⟨⟨ho,hb⟩,⟨Nat.le_succ _,Nat.le_succ _⟩,?_⟩
  simpa only [BinaryAdjacentWidthInterchange.volume,RectangularChunkSwap.volume,
    Nat.mul_one,hl,hr,Nat.log_pow (by decide : 1 < 2)] using hv.symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
