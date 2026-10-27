module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFactorBatchRelease

/-! The batch release changes only its owned page and output prefix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

def placedFactorBatchOwnedRegs : List (Fin 256) := sharedPageOwnedRegs.map couplingBoundaryReg

theorem placedFactorBatchOwnedRegs_eq :
    placedFactorBatchOwnedRegs = sharedPageOwnedRegs.map placedFactorBatchReleaseReg := by
  apply List.map_congr_left
  intro i hi
  exact (placedFactorBatchReleaseReg_owned i hi).symm

theorem placedFactorBatchOwnedRegs_release (i : Fin 240) :
    placedFactorBatchReleaseReg i ∈ placedFactorBatchOwnedRegs ↔ i ∈ sharedPageOwnedRegs := by
  rw [placedFactorBatchOwnedRegs_eq]
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    exact placedFactorBatchReleaseReg_injective he ▸ hj
  · intro hi
    exact List.mem_map.mpr ⟨i,hi,rfl⟩

theorem placedFactorBatchOwnedRegs_off (j : Fin 256) (hj : 240 ≤ j.val) :
    j ∉ placedFactorBatchOwnedRegs := by
  intro he
  obtain ⟨i,_,hi⟩ := List.mem_map.mp he
  exact cachedBoundaryReg_off i j hj hi

theorem placedFactorBatchReleaseResult_frame {A : ℕ} (S : Stacks 256 A) (rows : ℕ)
    (result tail : List (Fin (A+4))) (h240 : S.R 240 = []) :
    placedFactorBatchReleaseResult S rows result tail =
      {S with R := fun i => if i ∈ placedFactorBatchOwnedRegs then [] else
        (Function.update S.R 132 (result++tail)) i} := by
  let M := placedFactorBatchReleaseInput S rows
  let T := embStk placedFactorBatchReleaseReg M
  let T' : Stacks 240 A := {T with R := fun i => if i ∈ sharedPageOwnedRegs then [] else
    (Function.update T.R 132 (result++tail)) i}
  let R := embOvr placedFactorBatchReleaseReg T'.get M
  have hproject := embStk_ovr placedFactorBatchReleaseReg_injective T' M
  refine Stacks.ext rfl rfl ?_ ?_
  · funext j
    by_cases hj : ∃ i, placedFactorBatchReleaseReg i = j
    · obtain ⟨i,rfl⟩ := hj
      exact congrArg (fun X : Stacks 240 A => X.L i) hproject
    · exact (embOvr_off (e := placedFactorBatchReleaseReg) T'.get M
        (by intro i he; exact hj ⟨i,he⟩)).1
  · funext j
    by_cases hj240 : j = 240
    · subst j
      simp [placedFactorBatchReleaseResult,placedFactorBatchOwnedRegs_off 240 (by decide),h240]
    by_cases hj : ∃ i, placedFactorBatchReleaseReg i = j
    · obtain ⟨i,rfl⟩ := hj
      have hread : R.R (placedFactorBatchReleaseReg i) = T'.R i :=
        congrArg (fun X : Stacks 240 A => X.R i) hproject
      change Function.update R.R 240 [] (placedFactorBatchReleaseReg i) = _
      rw [Function.update_of_ne hj240,hread]
      change T'.R i = if placedFactorBatchReleaseReg i ∈ placedFactorBatchOwnedRegs then [] else
        Function.update S.R 132 (result++tail) (placedFactorBatchReleaseReg i)
      simp only [placedFactorBatchOwnedRegs_release]
      by_cases hi : i ∈ sharedPageOwnedRegs
      · simp only [T',hi,ite_true]
      · simp only [T',hi,ite_false]
        by_cases hi132 : i = 132
        · subst i; rfl
        have hn132 : placedFactorBatchReleaseReg i ≠ 132 :=
          placedFactorBatchReleaseReg_injective.ne hi132
        simp only [Function.update_of_ne hi132,Function.update_of_ne hn132]
        exact Function.update_of_ne hj240 _ _
    · have hoff : ∀ i, placedFactorBatchReleaseReg i ≠ j := by
        intro i he; exact hj ⟨i,he⟩
      have hnot : j ∉ placedFactorBatchOwnedRegs := by
        rw [placedFactorBatchOwnedRegs_eq]
        intro he
        obtain ⟨i,_,hi⟩ := List.mem_map.mp he
        exact hoff i hi
      have hn132 : j ≠ 132 := by intro he; subst j; exact hoff 132 rfl
      rw [placedFactorBatchReleaseResult_off S rows result tail j hj240 hoff]
      simp only [hnot,ite_false,Function.update_of_ne hn132]

theorem placedFactorBatchOwnedRegs_core (i : Fin 240) :
    couplingBoundaryReg i ∈ placedFactorBatchOwnedRegs ↔ i ∈ sharedPageOwnedRegs := by
  constructor
  · intro hi
    obtain ⟨j,hj,he⟩ := List.mem_map.mp hi
    exact couplingBoundaryReg_injective he ▸ hj
  · intro hi
    exact List.mem_map.mpr ⟨i,hi,rfl⟩

theorem placedFactorBatchReleaseResult_restore {A : ℕ} (original S : Stacks 256 A) (rows : ℕ)
    (result : List (Fin (A+4))) (h240 : S.R 240 = [])
    (hinp : S.inp = original.inp) (hout : S.out = original.out) (hL : S.L = original.L)
    (hframe : ∀ i, i ∉ placedFactorBatchOwnedRegs → i ≠ 132 → S.R i = original.R i)
    (howned : ∀ i ∈ placedFactorBatchOwnedRegs, original.R i = []) :
    placedFactorBatchReleaseResult S rows result (original.R 132) =
      {original with R := Function.update original.R 132 (result++original.R 132)} := by
  rw [placedFactorBatchReleaseResult_frame S rows result (original.R 132) h240]
  refine Stacks.ext hinp hout hL ?_
  funext i
  have hn132 : (132 : Fin 256) ∉ placedFactorBatchOwnedRegs := by
    have hn : (132 : Fin 240) ∉ sharedPageOwnedRegs := by norm_num [sharedPageOwnedRegs_mem]
    exact fun h => hn ((placedFactorBatchOwnedRegs_core 132).mp h)
  by_cases hi132 : i = 132
  · subst i; simp only [hn132,ite_false,Function.update_self]
  by_cases hi : i ∈ placedFactorBatchOwnedRegs
  · simp only [hi,ite_true,Function.update_of_ne hi132,howned i hi]
  · simp only [hi,ite_false,Function.update_of_ne hi132]
    exact hframe i hi hi132

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
