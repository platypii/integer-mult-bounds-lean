module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSharedPageComplexBatchRelease

/-! The batch release changes only its owned page and output prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def sharedComplexBatchOwnedRegs : List (Fin 248) := sharedPageOwnedRegs.map sharedComplexBatchCoreReg

theorem sharedComplexBatchOwnedRegs_eq :
    sharedComplexBatchOwnedRegs = sharedPageOwnedRegs.map sharedComplexBatchReleaseReg := by
  apply List.map_congr_left
  intro i hi
  exact (sharedComplexBatchReleaseReg_owned i hi).symm

theorem sharedComplexBatchOwnedRegs_release (i : Fin 240) :
    sharedComplexBatchReleaseReg i ∈ sharedComplexBatchOwnedRegs ↔ i ∈ sharedPageOwnedRegs := by
  rw [sharedComplexBatchOwnedRegs_eq]
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    exact sharedComplexBatchReleaseReg_injective he ▸ hj
  · intro hi
    exact List.mem_map.mpr ⟨i,hi,rfl⟩

theorem sharedComplexBatchOwnedRegs_off (j : Fin 248) (hj : 240 ≤ j.val) :
    j ∉ sharedComplexBatchOwnedRegs := by
  intro he
  obtain ⟨i,_,hi⟩ := List.mem_map.mp he
  exact sharedComplexBatchCoreReg_off i j hj hi

theorem sharedComplexBatchReleaseResult_frame {A : ℕ} (S : Stacks 248 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) (h240 : S.R 240 = []) :
    sharedComplexBatchReleaseResult S rows result tail =
      {S with R := fun i => if i ∈ sharedComplexBatchOwnedRegs then [] else
        (Function.update S.R 132 (result++tail)) i} := by
  let M := sharedComplexBatchReleaseInput S rows
  let T := embStk sharedComplexBatchReleaseReg M
  let T' : Stacks 240 A := {T with R := fun i => if i ∈ sharedPageOwnedRegs then [] else
    (Function.update T.R 132 (result++tail)) i}
  let R := embOvr sharedComplexBatchReleaseReg T'.get M
  have hproject := embStk_ovr sharedComplexBatchReleaseReg_injective T' M
  refine Stacks.ext rfl rfl ?_ ?_
  · funext j
    by_cases hj : ∃ i, sharedComplexBatchReleaseReg i = j
    · obtain ⟨i,rfl⟩ := hj
      exact congrArg (fun X : Stacks 240 A => X.L i) hproject
    · exact (embOvr_off (e := sharedComplexBatchReleaseReg) T'.get M
        (by intro i he; exact hj ⟨i,he⟩)).1
  · funext j
    by_cases hj240 : j = 240
    · subst j
      simp [sharedComplexBatchReleaseResult,sharedComplexBatchOwnedRegs_off 240 (by decide),h240]
    by_cases hj : ∃ i, sharedComplexBatchReleaseReg i = j
    · obtain ⟨i,rfl⟩ := hj
      have hread : R.R (sharedComplexBatchReleaseReg i) = T'.R i :=
        congrArg (fun X : Stacks 240 A => X.R i) hproject
      change Function.update R.R 240 [] (sharedComplexBatchReleaseReg i) = _
      rw [Function.update_of_ne hj240,hread]
      change T'.R i = if sharedComplexBatchReleaseReg i ∈ sharedComplexBatchOwnedRegs then [] else
        Function.update S.R 132 (result++tail) (sharedComplexBatchReleaseReg i)
      simp only [sharedComplexBatchOwnedRegs_release]
      by_cases hi : i ∈ sharedPageOwnedRegs
      · simp only [T',hi,ite_true]
      · simp only [T',hi,ite_false]
        by_cases hi132 : i = 132
        · subst i; rfl
        have hn132 : sharedComplexBatchReleaseReg i ≠ 132 :=
          sharedComplexBatchReleaseReg_injective.ne hi132
        simp only [Function.update_of_ne hi132,Function.update_of_ne hn132]
        exact Function.update_of_ne hj240 _ _
    · have hoff : ∀ i, sharedComplexBatchReleaseReg i ≠ j := by
        intro i he; exact hj ⟨i,he⟩
      have hnot : j ∉ sharedComplexBatchOwnedRegs := by
        rw [sharedComplexBatchOwnedRegs_eq]
        intro he
        obtain ⟨i,_,hi⟩ := List.mem_map.mp he
        exact hoff i hi
      have hn132 : j ≠ 132 := by intro he; subst j; exact hoff 132 rfl
      rw [sharedComplexBatchReleaseResult_off S rows result tail j hj240 hoff]
      simp only [hnot,ite_false,Function.update_of_ne hn132]

theorem sharedComplexBatchOwnedRegs_core (i : Fin 240) :
    sharedComplexBatchCoreReg i ∈ sharedComplexBatchOwnedRegs ↔ i ∈ sharedPageOwnedRegs := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    exact sharedComplexBatchCoreReg_injective he ▸ hj
  · intro hi
    exact List.mem_map.mpr ⟨i,hi,rfl⟩

theorem sharedComplexBatchReleaseResult_restore {A : ℕ} (original S : Stacks 248 A) (rows : ℕ)
    (result : List (Fin (A+4))) (h240 : S.R 240 = [])
    (hinp : S.inp = original.inp) (hout : S.out = original.out) (hL : S.L = original.L)
    (hframe : ∀ i, i ∉ sharedComplexBatchOwnedRegs → i ≠ 132 → S.R i = original.R i)
    (howned : ∀ i ∈ sharedComplexBatchOwnedRegs, original.R i = []) :
    sharedComplexBatchReleaseResult S rows result (original.R 132) =
      {original with R := Function.update original.R 132 (result++original.R 132)} := by
  rw [sharedComplexBatchReleaseResult_frame S rows result (original.R 132) h240]
  refine Stacks.ext hinp hout hL ?_
  funext i
  have hn132 : (132 : Fin 248) ∉ sharedComplexBatchOwnedRegs := by
    have hn : (132 : Fin 240) ∉ sharedPageOwnedRegs := by norm_num [sharedPageOwnedRegs_mem]
    exact fun h => hn ((sharedComplexBatchOwnedRegs_core 132).mp h)
  by_cases hi132 : i = 132
  · subst i; simp only [hn132,ite_false,Function.update_self]
  by_cases hi : i ∈ sharedComplexBatchOwnedRegs
  · simp only [hi,ite_true,Function.update_of_ne hi132,howned i hi]
  · simp only [hi,ite_false,Function.update_of_ne hi132]
    exact hframe i hi hi132

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
