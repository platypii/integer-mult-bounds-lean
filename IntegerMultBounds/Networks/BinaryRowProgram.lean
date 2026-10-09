import Mathlib.LinearAlgebra.Matrix.Transvection
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.ToLin
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! Every invertible binary coordinate map has a literal finite schedule of
row additions. All instructions carry distinct source and target registers;
the chronological list implements the matrix exactly. -/
namespace IntegerMultBounds.Networks.BinaryRowProgram

open Module

structure Op (ι : Type*) where
  target : ι
  source : ι
  distinct : target ≠ source

variable {ι : Type*} [Fintype ι] [DecidableEq ι]

def Op.matrix (op : Op ι) : Matrix ι ι (ZMod 2) :=
  Matrix.transvection op.target op.source 1

def matrix (word : List (Op ι)) : Matrix ι ι (ZMod 2) :=
  (word.reverse.map Op.matrix).prod

def Op.execute (op : Op ι) (x : ι → ZMod 2) : ι → ZMod 2 :=
  Function.update x op.target (x op.target + x op.source)

def run (word : List (Op ι)) (x : ι → ZMod 2) : ι → ZMod 2 :=
  word.foldl (fun x op => op.execute x) x

theorem matrix_append (u v : List (Op ι)) : matrix (u ++ v) = matrix v * matrix u := by
  simp [matrix, List.reverse_append, List.map_append, List.prod_append]

theorem execute_eq_mulVec (op : Op ι) (x : ι → ZMod 2) :
    op.execute x = op.matrix.mulVec x := by
  ext i
  simp [Op.execute, Op.matrix, Matrix.transvection, Matrix.add_mulVec,
    Matrix.single_mulVec, Function.update_apply]
  split_ifs <;> simp_all

theorem run_eq_mulVec (word : List (Op ι)) (x : ι → ZMod 2) :
    run word x = (matrix word).mulVec x := by
  induction word generalizing x with
  | nil => simp [run, matrix]
  | cons op word ih =>
    change run word (op.execute x) = _
    rw [ih, execute_eq_mulVec]
    simp [matrix, Matrix.mulVec_mulVec]

omit [Fintype ι] in
theorem execute_involutive (op : Op ι) : Function.Involutive op.execute := by
  intro x
  funext i
  by_cases hi : i = op.target
  · subst i
    simp [Op.execute, op.distinct.symm, add_assoc,
      CharTwo.add_self_eq_zero]
  · simp [Op.execute, Function.update_of_ne hi]

omit [Fintype ι] in
theorem run_append (u v : List (Op ι)) (x : ι → ZMod 2) :
    run (u ++ v) x = run v (run u x) := List.foldl_append

omit [Fintype ι] in
/-- Reversing the literal pair list computes the inverse without synthesizing
a second basis decomposition. -/
theorem reverse_restores (word : List (Op ι)) (x : ι → ZMod 2) :
    run word.reverse (run word x) = x := by
  induction word generalizing x with
  | nil => rfl
  | cons op word ih =>
    rw [List.reverse_cons, run_append]
    change op.execute (run word.reverse (run word (op.execute x))) = x
    rw [ih]
    exact execute_involutive op x

private theorem binary_cases (c : ZMod 2) : c = 0 ∨ c = 1 := by
  fin_cases c
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- Gaussian elimination over F2 needs neither scaling instructions nor
register exchanges: every invertible map is an exact distinct-pair word. -/
theorem exists_word (M : Matrix ι ι (ZMod 2)) (hM : M.det ≠ 0) :
    ∃ word : List (Op ι), matrix word = M := by
  refine Matrix.diagonal_transvection_induction_of_det_ne_zero
    (𝕜 := ZMod 2) (fun N => ∃ word : List (Op ι), matrix word = N) M hM ?_ ?_ ?_
  · intro D hD
    have hentries : ∀ i, D i ≠ 0 := by
      simpa only [Matrix.det_diagonal, Finset.prod_ne_zero_iff, Finset.mem_univ,
        forall_true_left] using hD
    have hone : D = fun _ => 1 := by
      funext i
      rcases binary_cases (D i) with hzero | hone
      · exact (hentries i hzero).elim
      · exact hone
    refine ⟨[], ?_⟩
    simp [matrix, hone]
  · intro t
    rcases binary_cases t.c with hz | ho
    · refine ⟨[], ?_⟩
      simp [matrix, Matrix.TransvectionStruct.toMatrix, hz, Matrix.transvection]
    · refine ⟨[⟨t.i,t.j,t.hij⟩], ?_⟩
      simp [matrix, Op.matrix, Matrix.TransvectionStruct.toMatrix, ho]
  · intro A B _ _ hA hB
    obtain ⟨u, hu⟩ := hA
    obtain ⟨v, hv⟩ := hB
    exact ⟨v ++ u, by rw [matrix_append, hu, hv]⟩

noncomputable def word (M : Matrix ι ι (ZMod 2)) (hM : M.det ≠ 0) : List (Op ι) :=
  Classical.choose (exists_word M hM)

theorem word_matrix (M : Matrix ι ι (ZMod 2)) (hM : M.det ≠ 0) :
    matrix (word M hM) = M := Classical.choose_spec (exists_word M hM)

theorem word_run (M : Matrix ι ι (ZMod 2)) (hM : M.det ≠ 0) (x : ι → ZMod 2) :
    run (word M hM) x = M.mulVec x := by rw [run_eq_mulVec, word_matrix]

/-- A genuine binary coordinate equivalence supplies its own invertibility
proof; no row-addition decomposition is assumed. -/
theorem equiv_det_ne_zero (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) :
    (LinearMap.toMatrix' e.toLinearMap).det ≠ 0 := by
  have hu : IsUnit (LinearMap.toMatrix' e.toLinearMap) :=
    LinearMap.isUnit_toMatrix'_iff.mpr ((Module.End.isUnit_iff _).mpr e.bijective)
  exact ((Matrix.isUnit_iff_isUnit_det _).mp hu).ne_zero

noncomputable def equivWord (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) : List (Op ι) :=
  word (LinearMap.toMatrix' e.toLinearMap) (equiv_det_ne_zero e)

theorem equivWord_run (e : (ι → ZMod 2) ≃ₗ[ZMod 2] (ι → ZMod 2)) (x : ι → ZMod 2) :
    run (equivWord e) x = e x := by
  rw [equivWord, word_run, LinearMap.toMatrix'_mulVec]
  rfl

/-- In particular, two actual binary bases induce a fixed literal schedule
from old coordinates to new coordinates. -/
noncomputable def basisWord {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (old new : Basis ι (ZMod 2) E) : List (Op ι) :=
  equivWord (old.equivFun.symm.trans new.equivFun)

theorem basisWord_run {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    (old new : Basis ι (ZMod 2) E) (x : E) :
    run (basisWord old new) (old.equivFun x) = new.equivFun x := by
  rw [basisWord, equivWord_run]
  simp

end IntegerMultBounds.Networks.BinaryRowProgram
