module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyHaloLengthKeyLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLengthKeyReady

/-! The retained-family loop uses the existing numerical caller invariant on
its original 144 ports. Family and active-cache ports remain separate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def weightFamilyLegacyBank {A : ℕ} (S : Stacks 151 A) : Stacks 144 A :=
  embStk cachedGroupLegacyReg (embStk weightFamilyCoreReg S)

theorem weightFamilyLegacyBank_pop {A : ℕ} (S : Stacks 151 A) (count : List (Fin (A+4))) :
    weightFamilyLegacyBank {S with R := Function.update S.R 127 count} =
      {weightFamilyLegacyBank S with R := Function.update (weightFamilyLegacyBank S).R 127 count} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [weightFamilyLegacyBank,embStk,cachedGroupLegacyReg,weightFamilyCoreReg,
    Function.update_apply,Fin.ext_iff]

theorem weightFamilyLegacyBank_published {A : ℕ} (S T : Stacks 151 A)
    (keys output : List (Fin (A+4)))
    (h : (embStk weightFamilyCoreReg T).R =
      publishedClassR (Function.update (embStk weightFamilyCoreReg S).R 126 keys) output) :
    (weightFamilyLegacyBank T).R =
      publishedClassR (Function.update (weightFamilyLegacyBank S).R 126 keys) output := by
  funext i
  have hi := congrArg (fun R => R (cachedGroupLegacyReg i)) h
  simpa [weightFamilyLegacyBank,embStk,publishedClassR,cachedGroupLegacyReg,
    weightFamilyCoreReg,Function.update_apply,Fin.ext_iff] using hi

theorem LengthKeyReady.pop_family {A P N q l s t u band V w : ℕ}
    {input : List (Fin (A+4))} {S : Stacks 151 A}
    (h : LengthKeyReady P N q l s t u band V w input (weightFamilyLegacyBank S))
    (count : List (Fin (A+4))) :
    LengthKeyReady P N q l s t u band V w input
      (weightFamilyLegacyBank {S with R := Function.update S.R 127 count}) := by
  rw [weightFamilyLegacyBank_pop]
  apply h.of_frame (S' := {weightFamilyLegacyBank S with R := Function.update (weightFamilyLegacyBank S).R 127 count})
    ((weightFamilyLegacyBank S).R 126) count ((weightFamilyLegacyBank S).R 132) rfl
  funext i
  by_cases h126 : i = 126 <;> by_cases h127 : i = 127 <;> by_cases h132 : i = 132 <;>
    simp [keyLoopR,h126,h127,h132]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
