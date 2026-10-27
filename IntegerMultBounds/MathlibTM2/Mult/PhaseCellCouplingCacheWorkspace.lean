module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBuildCouplingPageCache

/-! Two coefficient-cache keys live beyond the complete 248-register legacy batch bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

def couplingLegacyReg (i : Fin 144) : Fin 248 :=
  sharedComplexBatchCoreReg (sharedPageRecoveryReg (boundaryFactorLegacyReg
    (tableReg (boundaryArithmeticReg (componentReg i)))))

theorem couplingLegacyReg_injective : Function.Injective couplingLegacyReg :=
  sharedComplexBatchCoreReg_injective.comp (sharedPageRecoveryReg_injective.comp
    (boundaryFactorLegacyReg_injective.comp (tableReg_injective.comp
      (boundaryArithmeticReg_injective.comp componentReg_injective))))

def couplingCacheLegacyReg (i : Fin 248) : Fin 256 := ⟨i.val,by omega⟩

theorem couplingCacheLegacyReg_injective : Function.Injective couplingCacheLegacyReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 256 => k.val) h)

def couplingCachePort (recovery : Bool) (i : Fin 4) : Fin 256 :=
  ⟨(if recovery then 252 else 248)+i.val,by cases recovery <;> simp_all <;> omega⟩

theorem couplingCachePort_ge (recovery : Bool) (i : Fin 4) :
    248 ≤ (couplingCachePort recovery i).val := by cases recovery <;> simp [couplingCachePort] <;> omega

def couplingCacheReg (recovery : Bool) (i : Fin 144) : Fin 256 :=
  if i = 135 then couplingCachePort recovery 0 else
  if i = 138 then couplingCachePort recovery 1 else
  if i = 139 then couplingCachePort recovery 2 else
  if i = 140 then couplingCachePort recovery 3 else couplingCacheLegacyReg (couplingLegacyReg i)

theorem couplingCacheReg_injective (recovery : Bool) : Function.Injective (couplingCacheReg recovery) := by
  intro i j h
  have hv := congrArg Fin.val h
  have hi := (couplingLegacyReg i).isLt
  have hj := (couplingLegacyReg j).isLt
  cases recovery <;>
    simp [couplingCacheReg,couplingCachePort,couplingCacheLegacyReg] at hv <;>
    split_ifs at hv <;> simp_all <;>
    first | (subst_vars; rfl) | (apply couplingLegacyReg_injective; exact Fin.ext (by omega)) | omega

theorem couplingCacheReg_ordinary (recovery : Bool) (i : Fin 144)
    (h135 : i ≠ 135) (h138 : i ≠ 138) (h139 : i ≠ 139) (h140 : i ≠ 140) :
    couplingCacheReg recovery i = couplingCacheLegacyReg (couplingLegacyReg i) := by
  simp [couplingCacheReg,h135,h138,h139,h140]

theorem couplingCacheReg_native (recovery : Bool) (i : Fin 117) :
    couplingCacheReg recovery (groupReg i) = couplingCacheLegacyReg (couplingLegacyReg (groupReg i)) := by
  apply couplingCacheReg_ordinary
  all_goals intro h; have hv := congrArg Fin.val h; have hi := i.isLt; simp [groupReg] at hv; omega

theorem couplingCacheReg_other (recovery : Bool) (i : Fin 144) (j : Fin 4) :
    couplingCacheReg recovery i ≠ couplingCachePort (!recovery) j := by
  have hi := (couplingLegacyReg i).isLt
  have hj := j.isLt
  intro h
  have hv := congrArg Fin.val h
  cases recovery <;> simp only [couplingCacheReg,couplingCachePort,couplingCacheLegacyReg] at hv <;>
    split_ifs at hv <;> simp_all <;> omega

theorem couplingCacheLegacyReg_off (recovery : Bool) (j : Fin 4) (i : Fin 248) :
    couplingCacheLegacyReg i ≠ couplingCachePort recovery j := by
  intro h
  have hv := congrArg Fin.val h
  have hi := i.isLt
  have hj := couplingCachePort_ge recovery j
  change i.val = (couplingCachePort recovery j).val at hv
  omega

theorem couplingCache_native_view {A : ℕ} (recovery : Bool) (S : Stacks 256 A) :
    embStk groupReg (embStk (couplingCacheReg recovery) S) =
      embStk groupReg (embStk couplingLegacyReg (embStk couplingCacheLegacyReg S)) := by
  refine Stacks.ext rfl rfl ?_ ?_
  · funext i; simp [embStk,Function.comp_def,couplingCacheReg_native]
  · funext i; simp [embStk,Function.comp_def,couplingCacheReg_native]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
