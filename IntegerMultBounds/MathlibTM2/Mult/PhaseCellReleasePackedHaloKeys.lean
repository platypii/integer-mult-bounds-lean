module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Retire the selected-key width and unary length after the interior pass.
Coupling uses the independent geometry and word-width headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 168 Q A U}

def releasePackedHaloKeys : Pr P 168 Q A U := clearWords [125,128]

def releasedPackedHaloKeys {A : ℕ} (S : Stacks 168 A) : Stacks 168 A :=
  {S with R := Function.update (Function.update S.R 125 []) 128 []}

theorem releasePackedHaloKeys_exec (V s : ℕ) (v : HS 168 Q A U) (S : Stacks 168 A)
    (hV : (S.R 125).length = V) (hs : (S.R 128).length ≤ s) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2*(V+s)+5 ∧
      Exec body releasePackedHaloKeys (mk v S) n (mk v' (releasedPackedHaloKeys S)) := by
  obtain ⟨v',hu,he⟩ := clearWords_exec (body := body) [(125 : Fin 168),128] (by decide) v S
  refine ⟨v',_,hu,?_,he.cast rfl ?_⟩
  · simp only [List.map_cons,List.map_nil,List.sum_cons,List.sum_nil,
      List.length_cons,List.length_nil,hV]
    omega
  · apply congrArg (mk v')
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h125 : i = 125 <;> by_cases h128 : i = 128 <;>
      simp [releasedPackedHaloKeys,h125,h128]

theorem releasedPackedHaloKeys_core {A : ℕ} (S : Stacks 168 A) :
    embStk sharedCouplingCoreReg (releasedPackedHaloKeys S) = embStk sharedCouplingCoreReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have h : ∀ i : Fin 117, sharedCouplingCoreReg i ≠ 125 ∧ sharedCouplingCoreReg i ≠ 128 := by decide
  simp only [embStk,releasedPackedHaloKeys,Function.comp_apply,
    Function.update_of_ne (h i).1,Function.update_of_ne (h i).2]

theorem releasedPackedHaloKeys_native {A : ℕ} (S : Stacks 168 A) :
    embStk packedCellCoreReg (releasedPackedHaloKeys S) = embStk packedCellCoreReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hi := i.isLt
  simp [embStk,releasedPackedHaloKeys,packedCellCoreReg,Fin.ext_iff,
    show i.val ≠ 125 by omega,show i.val ≠ 128 by omega]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
