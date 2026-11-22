module

public import IntegerMultBounds.MathlibTM2.Cover.LabelFactorization

/-! Factor a flat change of field coordinates uniformly in the radix width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Swap
open Shared50ModularControl (prime prime_prime)
open Matrix Modular

/-- In column-vector order the right factor acts first, then a fixed permutation
of the digits, then the left factor. Both triangular passes have bounded entries
and stay invertible at every radix width. -/
theorem chartFactors {d : ℕ} (U : Matrix (Fin d) (Fin d) ℚ) (unit : IsUnit U)
    (pos : 1 ≤ d) (size : d ≤ 529)
    (entries : ∀ i j, (U i j).num.natAbs ≤ 10^10000 ∧ (U i j).den ≤ 10^10000) :
    ∃ (A B : Matrix (Fin d) (Fin d) ℚ) (π : Equiv.Perm (Fin d)),
      (∀ E ∈ [A,B], (∀ i j, M8.Height.ht (E i j) ≤ coefficientBound) ∧
        ∀ w, Shear.LowerTriangular (reduce (prime^w) E) ∧ IsUnit (reduce (prime^w) E)) ∧
      ∀ w x, reduce (prime^w) U *ᵥ x =
        reduce (prime^w) A *ᵥ ((reduce (prime^w) B *ᵥ x) ∘ π) := by
  let F := M8.Exchange.factors U
  have len : F.L.length = d := by
    rw [PivotRank.length_eq_rank F, Matrix.rank_of_isUnit U unit, Fintype.card_fin]
  obtain ⟨π,hπ⟩ := Cover.Route.exists_perm F.L F.nodup₁ F.nodup₂ len
  have hd := (Cover.LabelFactorization.boundedFactors U pos size entries).1
  have red := reduce_factorization_of_prime F prime_prime hd
  have small := M8.Exchange.numbersE_le U (by simpa using pos) (by simpa using size) entries
  have height {E : Matrix (Fin d) (Fin d) ℚ} (h : M8.Height.Bounded E (2^M8.Exchange.facE U)) (i j) :=
    (M8.Exchange.ht_le_of_bounded h (M8.Exchange.facE_le_numbersE U) i j).trans
      (M8.Exchange.le_coefficientBound small)
  obtain ⟨hA,_,hB,_⟩ := M8.Exchange.factors_bounded U
  refine ⟨F.E₁,F.E₂,π,?_,?_⟩
  · intro E h
    simp only [List.mem_cons,List.not_mem_nil,or_false] at h
    rcases h with rfl | rfl
    · refine ⟨height hA,fun w => ?_⟩
      obtain ⟨_,lower,_,_,_,inv,inv',_⟩ := red w
      exact ⟨lower,isUnit_iff_exists.mpr ⟨_,inv,inv'⟩⟩
    · refine ⟨height hB,fun w => ?_⟩
      obtain ⟨_,_,_,lower,_,_,_,inv,inv',_⟩ := red w
      exact ⟨lower,isUnit_iff_exists.mpr ⟨_,inv,inv'⟩⟩
  · intro w x
    obtain ⟨_,_,_,_,_,_,_,_,_,eq⟩ := red w
    rw [eq,← mulVec_mulVec,← mulVec_mulVec]
    apply congrArg
    funext i
    simp [mulVec,dotProduct,PivotRank.pivotMatrix_apply F.L (F.nodup₁.of_map _),hπ]

end IntegerMultBounds.MathlibTM2.M6.BitNode
