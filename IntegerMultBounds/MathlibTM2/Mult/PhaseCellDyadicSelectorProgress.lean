module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDyadicSelectorStep

/-! Arithmetic progress of selector dispatch. A residual transition preserves
the full packet volume and the selected row while reducing structural fuel. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

theorem dyadicSelectorTransition_spec (fuel a b C i : ℕ) (h : a+b ≤ fuel)
    (hi : i < dyadicStageCount fuel a b) :
    match dyadicSelectorTransition a b C (dyadicStageCount fuel a b) i with
    | .found row => row = selectDyadicStage fuel a b C (dyadicStageCount fuel a b) i
    | .next a' b' C' n' i' =>
        a'+b' ≤ fuel-1 ∧ a'+b' ≤ a+b ∧ C'*2^(a'+b') = C*2^(a+b) ∧
        n' = dyadicStageCount (fuel-1) a' b' ∧ i' < n' ∧
        selectDyadicStage fuel a b C (dyadicStageCount fuel a b) i =
          selectDyadicStage (fuel-1) a' b' C' n' i' := by
  cases fuel with
  | zero => simp [dyadicStageCount] at hi
  | succ fuel =>
    by_cases ha0 : a = 0
    · simp [dyadicStageCount,ha0] at hi
    by_cases hb0 : b = 0
    · simp [dyadicStageCount,hb0] at hi
    by_cases hab : a < b
    · have hn : dyadicStageCount (fuel+1) a b = 1+dyadicStageCount fuel (b-a) a := by
        simp [dyadicStageCount,ha0,hb0,not_le.mpr hab]
      by_cases hnext : i+1 < dyadicStageCount (fuel+1) a b
      · simp only [dyadicSelectorTransition,if_pos hab,if_pos hnext,Nat.add_sub_cancel]
        refine ⟨by omega,by omega,?_,by omega,by omega,?_⟩
        · rw [Nat.sub_add_cancel hab.le,pow_add]
          ring
        · have hlast : ¬i+1 = dyadicStageCount (fuel+1) a b := by omega
          have hlast' : ¬i+1 = 1+dyadicStageCount fuel (b-a) a := by omega
          simp [selectDyadicStage,ha0,hb0,not_le.mpr hab,hlast',hn,Nat.mul_comm]
      · have hlast : i+1 = dyadicStageCount (fuel+1) a b := by omega
        simp [dyadicSelectorTransition,selectDyadicStage,ha0,hb0,hab,not_le.mpr hab,hnext,hlast]
    · have hba : b ≤ a := by omega
      have hn : dyadicStageCount (fuel+1) a b = 1+dyadicStageCount fuel (a-b) b := by
        simp [dyadicStageCount,ha0,hb0,hba]
      by_cases hi0 : 0 < i
      · simp only [dyadicSelectorTransition,if_neg hab,if_pos hi0,Nat.add_sub_cancel]
        refine ⟨by omega,by omega,?_,by omega,by omega,?_⟩
        · rw [Nat.sub_add_cancel hba,pow_add]
          ring
        · have hi0' : i ≠ 0 := by omega
          simp [selectDyadicStage,ha0,hb0,hba,hi0',hn,Nat.mul_comm]
      · have hz : i = 0 := by omega
        subst i
        simp [dyadicSelectorTransition,selectDyadicStage,ha0,hb0,hab,hba]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
