module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWeightCache

/-! Keep the four grouped-weight cache ports disjoint from the retained 144-register caller. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host

def cachedGroupReg (i : Fin 121) : Fin 148 :=
  ⟨if i.val < 117 then i.val else i.val+27,by split <;> omega⟩

theorem cachedGroupReg_injective : Function.Injective cachedGroupReg := by
  intro i j h
  have hv := congrArg (fun k : Fin 148 => k.val) h
  simp only [cachedGroupReg] at hv
  split at hv <;> split at hv <;> apply Fin.ext <;> omega

theorem cachedGroupReg_legacy (i : Fin 117) :
    cachedGroupReg (weightCacheCoreReg i) = ⟨i.val,by omega⟩ := by
  apply Fin.ext
  simp [cachedGroupReg,weightCacheCoreReg,i.isLt]

theorem cachedGroupReg_off (k : Fin 148) (hlo : 117 ≤ k.val) (hhi : k.val < 144) :
    ∀ i, cachedGroupReg i ≠ k := by
  intro i he
  have hv := congrArg (fun k : Fin 148 => k.val) he
  simp only [cachedGroupReg] at hv
  split at hv <;> omega

theorem cachedGroupProject_updateR {A : ℕ} (S : Stacks 148 A) (k : Fin 148)
    (xs : List (Fin (A+4))) (hlo : 117 ≤ k.val) (hhi : k.val < 144) :
    embStk cachedGroupReg {S with R := Function.update S.R k xs} = embStk cachedGroupReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  exact Function.update_of_ne (cachedGroupReg_off k hlo hhi i) _ _

theorem cachedGroupReg_high (i : Fin 148) (hi : 144 ≤ i.val) :
    ∃ j : Fin 121, 117 ≤ j.val ∧ cachedGroupReg j = i := by
  refine ⟨⟨i.val-27,by omega⟩,by simp; omega,?_⟩
  apply Fin.ext
  simp only [cachedGroupReg]
  split <;> omega

/-- The original gather/publication caller occupies the first 144 registers. -/
def cachedGroupLegacyReg (i : Fin 144) : Fin 148 := ⟨i.val,by omega⟩

theorem cachedGroupLegacyReg_injective : Function.Injective cachedGroupLegacyReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 148 => k.val) h)

theorem cachedGroupLegacyReg_off (i : Fin 148) (hi : 144 ≤ i.val) :
    ∀ j, cachedGroupLegacyReg j ≠ i := by
  intro j he
  have hv := congrArg (fun k : Fin 148 => k.val) he
  dsimp [cachedGroupLegacyReg] at hv
  omega

theorem cachedGroupCore_view {A : ℕ} (S : Stacks 148 A) :
    embStk weightCacheCoreReg (embStk cachedGroupReg S) =
      embStk groupReg (embStk cachedGroupLegacyReg S) := by
  have he (i : Fin 117) : cachedGroupReg (weightCacheCoreReg i) = cachedGroupLegacyReg (groupReg i) := by
    apply Fin.ext
    simp [cachedGroupReg,weightCacheCoreReg,cachedGroupLegacyReg,groupReg,i.isLt]
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; exact congrArg S.L (he i)
  · funext i; exact congrArg S.R (he i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
