module

public import IntegerMultBounds.MathlibTM2.M8.Rev.Heights
public import IntegerMultBounds.Networks.Certificates.PR589.Nine.Invocation

/-! Uniform rational heights for the original PR589 orthogonal projectors. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M6.BitNode
open IntegerMultBounds.Networks IntegerMultBounds.Networks.Certificates.PR589
open Matrix Nine M8.Height

private theorem gram_projector {i d : ℕ} (A : Matrix (Fin d) (Fin 8) ℚ)
    (span : LinearMap.range Aᵀ.mulVecLin = Geometry.label i)
    (indep : LinearIndependent ℚ A.row) :
    labelProj i = Aᵀ * (A*Aᵀ)⁻¹ * A := by
  let G := A*Aᵀ
  have full : LinearMap.range G.mulVecLin = ⊤ := by
    apply Submodule.eq_top_of_finrank_eq
    change G.rank = _
    rw [rank_self_mul_transpose,indep.rank_matrix,Module.finrank_fintype_fun_eq_card]
  have unit := (isUnit_iff_isUnit_det G).mp (mulVec_surjective_iff_isUnit.mp
    (LinearMap.range_eq_top.mp full))
  let P := Aᵀ*G⁻¹*A
  have ap : A*P=A := by
    change A*(Aᵀ*G⁻¹*A)=A
    rw [← Matrix.mul_assoc,← Matrix.mul_assoc,show A*Aᵀ=G from rfl,mul_nonsing_inv G unit,Matrix.one_mul]
  have eq : Geometry.projector i = P.mulVecLin := by
    apply projector_eq_of
    · intro x
      rw [← span]
      refine ⟨G⁻¹ *ᵥ (A *ᵥ x),?_⟩
      simp [P]
    · intro x n hn
      rw [← span] at hn
      obtain ⟨b,rfl⟩ := hn
      rw [form_eq_dot]
      change ((Aᵀ *ᵥ b) ⬝ᵥ (x-P *ᵥ x)) / 2 = 0
      rw [dotProduct_comm,dotProduct_transpose_mulVec,mulVec_sub,mulVec_mulVec,ap,sub_self]
      simp
  rw [labelProj,eq]
  exact LinearMap.toMatrix'_toLin' P

private theorem gram_height {d : ℕ} (hd : d ≤ 8) (Z : Matrix (Fin d) (Fin 8) ℤ)
    (small : ∀ i j, (Z i j).natAbs ≤ 2) :
    let A := Z.map (Int.castRingHom ℚ)
    Bounded (Aᵀ*(A*Aᵀ)⁻¹*A) (2^16384) := by
  intro A
  have entries : Bounded A (2^1) := fun i j => by
    simpa [A,M8.Rev.ht_intCast] using max_le (small i j) (by decide : 1 ≤ 2)
  have gram (i j) : ((Z*Zᵀ) i j).natAbs ≤ 2^5 := by
    rw [Matrix.mul_apply]
    refine (Int.natAbs_sum_le _ _).trans ?_
    calc
      _ ≤ ∑ _k : Fin 8, 2*2 := Finset.sum_le_sum fun k _ => by
        rw [Int.natAbs_mul]; exact Nat.mul_le_mul (small i k) (small j k)
      _ = _ := by decide
  have inv := M8.Rev.bounded_inv_intCast (e := 5) (k := 3) gram hd
  have mapped : (Z*Zᵀ).map (Int.castRingHom ℚ) = A*Aᵀ := by
    rw [Matrix.map_mul]; rfl
  rw [mapped] at inv
  apply (bounded_mul (bounded_mul (bounded_transpose entries) inv) entries).pow_mono
  simp only [Fintype.card_fin]
  calc
    _ ≤ 8*(8*(1+2*(8*(3+5))+1)+1+1) := by gcongr
    _ ≤ _ := by decide

/-- Every original frame is spanned by integral roots of height two. The
Gram formula bounds its orthogonal projector independently of the label. -/
theorem labelProj_bounded (i : Fin 636) : Bounded (labelProj i) (2^16384) := by
  classical
  let roots := Geometry.root '' {j | j ∈ Frames.labels i.val}
  obtain ⟨rows,mem,span,indep⟩ := Submodule.exists_fun_fin_finrank_span_eq ℚ roots
  choose idx inside value using mem
  let Z := fun k (j : Fin 8) => (Frames.lines (idx k)).getD j.val 0
  let A := Matrix.map Z (Int.castRingHom ℚ)
  have rowsEq : A.row = rows := by
    funext k
    exact value k
  have rangeEq : LinearMap.range Aᵀ.mulVecLin = Geometry.label i := by
    rw [Matrix.range_mulVecLin,col_transpose,rowsEq]
    exact span
  rw [gram_projector A rangeEq (rowsEq ▸ indep)]
  have size : Module.finrank ℚ (Submodule.span ℚ roots) ≤ 8 :=
    (Submodule.finrank_le _).trans_eq (by simp [Geometry.Address])
  apply gram_height size Z
  have labels : ∀ n : Fin 636, (Frames.labels n.val).all (· < 111) = true := by decide +kernel
  have entries : ∀ (n : Fin 111) (j : Fin 8), ((Frames.lines n.val).getD j.val 0).natAbs ≤ 2 := by decide +kernel
  intro k j
  have lt : idx k < 111 := of_decide_eq_true (List.all_eq_true.mp (labels i) _ (inside k))
  exact entries ⟨idx k,lt⟩ j

end IntegerMultBounds.MathlibTM2.M6.BitNode
