module

public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Invocation
public import IntegerMultBounds.MathlibTM2.M8.Rev.Edge

/-! A single reversed coordinate layout for the original orthogonal PR589 frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open Matrix Nine

private theorem nested_mul {i j : ℕ} (le : Geometry.label i ≤ Geometry.label j) :
    labelProj i * labelProj j = labelProj i ∧ labelProj j * labelProj i = labelProj i := by
  have both (x : Geometry.Address) :
      Geometry.projector i (Geometry.projector j x) = Geometry.projector i x ∧
      Geometry.projector j (Geometry.projector i x) = Geometry.projector i x := by
    simp only [Geometry.projector_eq]
    exact ProjectionRank.project_nested Geometry.form Geometry.form_symm _ _
      (Geometry.restrict_nondegenerate _) (Geometry.restrict_nondegenerate _) le x
  constructor
  all_goals
    simp only [labelProj,← LinearMap.toMatrix'_comp]
    apply congrArg LinearMap.toMatrix'
    apply LinearMap.ext
    intro x
  · exact (both x).1
  · exact (both x).2

/-- In one bounded integral basis, every nested pair of the 636 original
frames has a reversed program with precisely the billed rank and pivot block.
The zero-to-retained pairs include the nine COPY windows. -/
theorem orthogonalMoves_common_basis :
    ∃ basis : Matrix (Fin 8) (Fin 8) ℕ,
      (∀ a b, basis a b ≤ 2^28) ∧ (basis.map (Nat.cast : ℕ → ℚ)).det ≠ 0 ∧
      ∀ i j : Fin 636, Geometry.label i ≤ Geometry.label j →
        let g := basis.map (Nat.cast : ℕ → ℚ)
        let U := g * (labelProj j - labelProj i) * g⁻¹
        let rank := Geometry.moveRank i j
        (∀ s, AffineFieldProgram.run (M8.Rev.revProgram U) s =
          M8.ReversedExchange.revExchange U s) ∧
        AffineFieldProgram.interchanges (M8.Rev.revProgram U) = rank ∧
        ∀ a b, AffineFieldProgram.Op.interchange a b ∈ M8.Rev.revProgram U ↔
          (a,b) ∈ M8.ReversedExchange.revPivots 8 rank := by
  classical
  let residual := fun p : Fin 636 × Fin 636 =>
    if Geometry.label p.1 ≤ Geometry.label p.2 then labelProj p.2 - labelProj p.1 else 0
  have idem (p) : IsIdempotentElem (residual p) := by
    unfold residual
    split
    · rename_i le
      obtain ⟨ab,ba⟩ := nested_mul le
      exact M8.Exchange.sub_idempotent _ _ (labelProj_mul_self _) (labelProj_mul_self _) ab ba
    · exact zero_mul _
  obtain ⟨basis,bound,det,generic⟩ := M8.GenericBasis.exists_generic_basis_of_idempotent
    (fun k => residual (finProdFinEquiv.symm k)) (fun k => idem _)
  have degree (r : Fin (636*636) → ℕ) : M8.GenericBasis.degreeBound 8 r ≤ 2^28 := by
    have per (j) : (∑ i ∈ M8.GenericBasis.sizes (m := 8) (r j), i.val*(8+1)) ≤ 9*72 := by
      calc
        _ ≤ ∑ _i ∈ M8.GenericBasis.sizes (m := 8) (r j), 72 :=
          Finset.sum_le_sum fun i _ => Nat.mul_le_mul_right 9 (show i.val ≤ 8 from Nat.le_of_lt_succ i.isLt)
        _ ≤ _ := by
          simp only [Finset.sum_const,smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_univ _)
    calc
      _ ≤ 8 + ∑ _j : Fin (636*636), 9*72 := Nat.add_le_add_left (Finset.sum_le_sum fun j _ => per j) _
      _ ≤ _ := by simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]; decide
  refine ⟨basis,fun a b => (bound a b).trans (degree _),det,?_⟩
  intro i j le g U rank
  have h := generic (finProdFinEquiv (i,j))
  have id := idem (i,j)
  simp only [Equiv.symm_apply_apply,residual,le,ite_true] at h id
  have unit : IsUnit g.det := isUnit_iff_ne_zero.mpr det
  have conjugate : U.rank = (labelProj j - labelProj i).rank := by
    rw [show U = _ from rfl,rank_mul_eq_left_of_isUnit_det _ _ (by simpa using unit.inv),
      rank_mul_eq_right_of_isUnit_det _ _ unit]
  have price : (labelProj j - labelProj i).rank = rank := by
    change Module.finrank ℚ (LinearMap.range (Matrix.toLin' (labelProj j - labelProj i))) = _
    rw [labelProj,labelProj,← map_sub,Matrix.toLin'_toMatrix']
    rfl
  have uidem : U*U=U := by
    dsimp only [U]
    calc
      _ = g * ((labelProj j-labelProj i)*(g⁻¹*g)*(labelProj j-labelProj i))*g⁻¹ := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [nonsing_inv_mul g unit,Matrix.mul_one,id.eq]
  have pivots := M8.Rev.mem_revProgram_interchange U (conjugate.symm ▸ h)
  exact ⟨M8.Rev.revProgram_run U uidem,(M8.Rev.revProgram_interchanges U).trans (conjugate.trans price),
    fun a b => (pivots a b).trans (by rw [conjugate,price])⟩

end IntegerMultBounds.MathlibTM2.M6.BitNode
