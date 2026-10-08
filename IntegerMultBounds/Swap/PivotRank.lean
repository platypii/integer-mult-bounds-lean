import IntegerMultBounds.Swap.LowerTriangular
import Mathlib.LinearAlgebra.Matrix.Rank
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

/-! The number of pivots of a lower triangular factorization is the rank. A
pivot matrix `Π` with distinct rows and distinct columns satisfies
`Πᵀ Π = D` and `Π D = Π` for the diagonal indicator `D` of its columns, so its
rank is the number of pivots; invertible factors do not change the rank. -/

namespace IntegerMultBounds.Swap.PivotRank

open Matrix Finset
open IntegerMultBounds.Swap.Shear (pivotMatrix)
open IntegerMultBounds.Swap.LowerTriangular

variable {F ι κ : Type*} [Field F] [Fintype ι] [Fintype κ]

section Pivots
variable [DecidableEq ι] [DecidableEq κ]

omit [Fintype ι] [Fintype κ] in
theorem pivotMatrix_apply {R : Type*} [CommRing R] (L : List (ι × κ)) (hL : L.Nodup)
    (i : ι) (j : κ) : pivotMatrix L i j = if (i, j) ∈ L then (1 : R) else 0 := by
  induction L with
  | nil => simp [pivotMatrix]
  | cons p rest ih =>
    rw [List.nodup_cons] at hL
    rw [pivotMatrix, Matrix.add_apply, ih hL.2]
    by_cases hp : (i, j) = p
    · subst hp
      simp [Matrix.single, hL.1]
    · have hs : single p.1 p.2 (1 : R) i j = 0 := by
        simp only [Matrix.single, of_apply]
        rw [ite_eq_right]
        rintro ⟨h1, h2⟩
        exact hp (Prod.ext h1.symm h2.symm)
      rw [hs, zero_add]
      simp [List.mem_cons, hp]

omit [Fintype κ] in
theorem transpose_mul_self (L : List (ι × κ)) (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) :
    (pivotMatrix L : Matrix ι κ F)ᵀ * pivotMatrix L =
      diagonal fun j => if j ∈ L.map Prod.snd then (1 : F) else 0 := by
  have hL : L.Nodup := h₁.of_map _
  ext j j'
  rw [mul_apply]
  simp only [transpose_apply, pivotMatrix_apply L hL]
  by_cases hjj : j = j'
  · subst hjj
    rw [diagonal_apply_eq]
    by_cases hj : j ∈ L.map Prod.snd
    · rw [ite_eq_left hj]
      obtain ⟨p, hp, hpj⟩ := List.mem_map.mp hj
      have hpe : (p.1, j) = p := Prod.ext rfl hpj.symm
      rw [sum_eq_single p.1]
      · rw [hpe, ite_eq_left hp, mul_one]
      · intro i _ hi
        rw [ite_eq_right, zero_mul]
        intro hij
        have := List.inj_on_of_nodup_map h₂ hij hp (by rw [← hpj])
        exact hi (congrArg Prod.fst this)
      · intro h
        exact absurd (mem_univ _) h
    · rw [ite_eq_right hj]
      apply sum_eq_zero
      intro i _
      rw [ite_eq_right, zero_mul]
      intro hij
      exact hj (List.mem_map.mpr ⟨(i, j), hij, rfl⟩)
  · rw [diagonal_apply_ne _ hjj]
    apply sum_eq_zero
    intro i _
    by_cases h1 : (i, j) ∈ L
    · by_cases h2 : (i, j') ∈ L
      · exfalso
        have := List.inj_on_of_nodup_map h₁ h1 h2 rfl
        exact hjj (congrArg Prod.snd this)
      · rw [ite_eq_right h2, mul_zero]
    · rw [ite_eq_right h1, zero_mul]

omit [Fintype ι] in
theorem mul_diagonal_self (L : List (ι × κ)) (hL : L.Nodup) :
    (pivotMatrix L : Matrix ι κ F) *
      diagonal (fun j => if j ∈ L.map Prod.snd then (1 : F) else 0) = pivotMatrix L := by
  ext i j
  rw [mul_diagonal, pivotMatrix_apply L hL]
  by_cases h : (i, j) ∈ L
  · rw [ite_eq_left h, ite_eq_left (List.mem_map.mpr ⟨(i, j), h, rfl⟩), mul_one]
  · rw [ite_eq_right h, zero_mul]

/-- A pivot matrix with distinct rows and columns has rank the number of pivots. -/
theorem rank_pivotMatrix (L : List (ι × κ)) (h₁ : (L.map Prod.fst).Nodup)
    (h₂ : (L.map Prod.snd).Nodup) : (pivotMatrix L : Matrix ι κ F).rank = L.length := by
  classical
  have hL : L.Nodup := h₁.of_map _
  set D : Matrix κ κ F := diagonal fun j => if j ∈ L.map Prod.snd then (1 : F) else 0 with hD
  have hDrank : D.rank = L.length := by
    rw [hD, rank_diagonal, Fintype.card_subtype]
    have hfilter : (univ.filter fun j => (if j ∈ L.map Prod.snd then (1 : F) else 0) ≠ 0) =
        (L.map Prod.snd).toFinset := by
      ext j
      by_cases hj : j ∈ L.map Prod.snd <;> simp only [mem_filter, mem_univ, true_and, hj,
        ite_true, ite_false, ne_eq, one_ne_zero, not_false_eq_true, not_true_eq_false,
        List.mem_toFinset]
    rw [hfilter, List.toFinset_card_of_nodup h₂, List.length_map]
  apply le_antisymm
  · calc (pivotMatrix L : Matrix ι κ F).rank = (pivotMatrix L * D).rank := by
          rw [hD, mul_diagonal_self L hL]
      _ ≤ D.rank := rank_mul_le_right _ _
      _ = L.length := hDrank
  · calc L.length = D.rank := hDrank.symm
      _ = ((pivotMatrix L : Matrix ι κ F)ᵀ * pivotMatrix L).rank := by
          rw [hD, transpose_mul_self L h₁ h₂]
      _ ≤ (pivotMatrix L : Matrix ι κ F).rank := rank_mul_le_right _ _

end Pivots

section Factorizations
variable [LinearOrder ι] [LinearOrder κ]

/-- The pivot count of a lower triangular factorization is the rank of the matrix. -/
theorem length_eq_rank {S : Finset ι} {T : Finset κ} {A : Matrix ι κ F}
    (f : Factorization S T A) : f.L.length = A.rank := by
  have h1 : (pivotMatrix f.L : Matrix ι κ F).rank = f.L.length :=
    rank_pivotMatrix _ f.nodup₁ f.nodup₂
  have h2 : (f.E₁ * (pivotMatrix f.L : Matrix ι κ F) * f.E₂).rank =
      (pivotMatrix f.L : Matrix ι κ F).rank := by
    rw [rank_mul_eq_left_of_isUnit_det f.E₂ (f.E₁ * (pivotMatrix f.L : Matrix ι κ F))
        (isUnit_det_of_left_inverse f.inv₂'),
      rank_mul_eq_right_of_isUnit_det f.E₁ (pivotMatrix f.L : Matrix ι κ F)
        (isUnit_det_of_right_inverse f.inv₁)]
  have h3 : A.rank = (f.E₁ * (pivotMatrix f.L : Matrix ι κ F) * f.E₂).rank :=
    congrArg Matrix.rank f.eq
  rw [h3, h2, h1]

/-- Lemma 4.1 with its count: every matrix over a field factors with exactly
`rank A` pivots. -/
theorem exists_factorization_rank (A : Matrix ι κ F) :
    ∃ f : Factorization univ univ A, f.L.length = A.rank :=
  let ⟨f⟩ := factorization A
  ⟨f, length_eq_rank f⟩

end Factorizations

end IntegerMultBounds.Swap.PivotRank
