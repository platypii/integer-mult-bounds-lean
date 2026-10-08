import IntegerMultBounds.Networks.BinaryOrthonormal
import IntegerMultBounds.Networks.ProjectionRank
import Mathlib.Algebra.Group.AddChar
import Mathlib.Basic.Complex.Basic

/-! Exact finite-rank projection decompositions underlying binary phase frames.
Actual network residuals must still supply their norm-one witnesses. No tape
costs or unproved network labels are assumed here. -/

namespace IntegerMultBounds.Networks.BinaryPhase

open Module ProjectionRank

section Projections
variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E] [FiniteDimensional K E]
    (B : LinearMap.BilinForm K E) (hs : B.IsSymm)

/-- The projection associated with one orthonormal direction. -/
def rankOne (v : E) : E →ₗ[K] E := (B v).smulRight v

omit [FiniteDimensional K E] in
@[simp] theorem rankOne_apply (v x : E) : rankOne B v x = B v x • v := rfl

omit [FiniteDimensional K E] in
/-- Each normalized direction has an actual one-dimensional range. -/
theorem rankOne_range (v : E) (hv : B v v = 1) :
    LinearMap.range (rankOne B v) = K ∙ v := by
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · intro x hx
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hx
    refine ⟨t • v, ?_⟩
    simp [rankOne, map_smul, hv]

omit [FiniteDimensional K E] in
theorem rankOne_rank (v : E) (hv : B v v = 1) :
    finrank K (LinearMap.range (rankOne B v)) = 1 := by
  rw [rankOne_range B v hv]
  apply finrank_span_singleton
  intro hz
  simp [hz] at hv

omit [FiniteDimensional K E] in
/-- Coefficients in an orthonormal basis are the actual bilinear pairings. -/
theorem basis_repr (W : Submodule K E) {d : ℕ} (b : Basis (Fin d) K W)
    (hgram : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) (y : W) (i : Fin d) :
    b.repr y i = B (b i) y := by
  have hh := congrArg (fun z : W => B (b i) z) (b.sum_repr y)
  simp only [Submodule.coe_sum, Submodule.coe_smul, map_sum, map_smul, hgram, smul_eq_mul] at hh
  simpa using hh

/-- The orthogonal projection is an exact sum of one rank-one operator per
orthonormal basis vector, rather than a rank annotation. -/
theorem project_eq_sum (W : Submodule K E) (hw : (B.restrict W).Nondegenerate)
    {d : ℕ} (b : Basis (Fin d) K W)
    (hgram : ∀ i j, B (b i) (b j) = if i = j then 1 else 0) :
    project B hs W hw = ∑ i, rankOne B (b i) := by
  ext x
  let y : W := ⟨project B hs W hw x, project_mem B hs W hw x⟩
  have hc (i : Fin d) : b.repr y i = B (b i) x := by
    rw [basis_repr B W b hgram]
    have hz := sub_project_mem B hs W hw x (b i) (b i).property
    rw [map_sub] at hz
    exact (sub_eq_zero.mp hz).symm
  have hh := congrArg (fun z : W => (z : E)) (b.sum_repr y)
  simpa only [Submodule.coe_sum, Submodule.coe_smul, hc, LinearMap.sum_apply,
    rankOne_apply] using hh.symm

/-- The projection difference is exactly the residual projection, with the
orthogonal complement determined by the ambient form. -/
theorem difference_eq_project (U V : Submodule K E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V) :
    project B hs V hv - project B hs U hu =
      project B hs (residual B U V) (residual_nondegenerate B hs U V hu hv hUV) := by
  ext x
  let D := project B hs V hv x - project B hs U hu x
  have hd : D ∈ residual B U V := by
    rw [← difference_range B hs U V hu hv hUV]
    exact ⟨x, rfl⟩
  have ht : x - D ∈ B.orthogonal (residual B U V) := by
    intro z hz
    have hlarge := sub_project_mem B hs V hv x z hz.1
    have hsmall : B z (project B hs U hu x) = 0 := by
      rw [hs.eq]
      exact hz.2 _ (project_mem B hs U hu x)
    have he : x - D = (x - project B hs V hv x) + project B hs U hu x := by dsimp [D]; abel
    rw [he, map_add, hlarge, hsmall, add_zero]
  have hp := project_right B hs (residual B U V) (residual_nondegenerate B hs U V hu hv hUV) ht
  rw [map_sub, project_left B hs _ _ hd] at hp
  exact (sub_eq_zero.mp hp).symm

end Projections

section Binary
variable {E : Type*} [AddCommGroup E] [Module (ZMod 2) E] [FiniteDimensional (ZMod 2) E]
    (B : LinearMap.BilinForm (ZMod 2) E) (hs : B.IsSymm)

/-- Every nested nondegenerate binary edge whose nonzero residual contains a
unit has a proved rank-one decomposition with exactly its dimension difference
many directions. The zero residual uses the empty basis. -/
theorem exists_difference_decomposition (U V : Submodule (ZMod 2) E)
    (hu : (B.restrict U).Nondegenerate) (hv : (B.restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : residual B U V = ⊥ ∨ ∃ v : residual B U V, B v v = 1) :
    ∃ b : Basis (Fin (finrank (ZMod 2) (residual B U V))) (ZMod 2) (residual B U V),
      (∀ i j, B (b i) (b j) = if i = j then 1 else 0) ∧
      project B hs V hv - project B hs U hu = ∑ i, rankOne B (b i) ∧
      finrank (ZMod 2) (residual B U V) = finrank (ZMod 2) V - finrank (ZMod 2) U := by
  have hb : ∃ b : Basis (Fin (finrank (ZMod 2) (residual B U V))) (ZMod 2) (residual B U V),
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
    rcases hunit with hzero | hone
    · have hd : finrank (ZMod 2) (residual B U V) = 0 := Submodule.finrank_eq_zero.mpr hzero
      let : IsEmpty (Fin (finrank (ZMod 2) (residual B U V))) := by rw [hd]; infer_instance
      exact ⟨basisOfFinrankZero hd, fun i => isEmptyElim i⟩
    · exact BinaryOrthonormal.exists_orthonormal_basis (B.restrict (residual B U V))
        (hs.restrict _) (residual_nondegenerate B hs U V hu hv hUV) hone
  obtain ⟨b, hgram⟩ := hb
  refine ⟨b, hgram, ?_, residual_finrank B hs U V hu hUV⟩
  rw [difference_eq_project B hs U V hu hv hUV]
  exact project_eq_sum B hs _ _ b hgram

end Binary
section Weight

/-- The representative of a binary scalar in the integers modulo four. -/
def bitLift (b : ZMod 2) : ZMod 4 := b.val

@[simp] theorem bitLift_zero : bitLift 0 = 0 := rfl
@[simp] theorem bitLift_one : bitLift 1 = 1 := rfl

/-- Twice the representative is additive, though the representative itself is not. -/
def doubleLift : ZMod 2 →+ ZMod 4 where
  toFun := fun b => 2 * bitLift b
  map_zero' := by rfl
  map_add' := by intro a b; fin_cases a <;> fin_cases b <;> decide

theorem bitLift_add (a b : ZMod 2) :
    bitLift (a + b) = bitLift a + bitLift b - doubleLift (a * b) := by
  fin_cases a <;> fin_cases b <;> decide

/-- Hamming weight reduced modulo four, using the actual coordinate bits. -/
def weightPhase {h : ℕ} (x : Fin h → ZMod 2) : ZMod 4 := ∑ i, bitLift (x i)

/-- Integer Hamming weight of the binary coordinate vector. -/
def weight {h : ℕ} (x : Fin h → ZMod 2) : ℕ := ∑ i, (x i).val

theorem weightPhase_eq_weight {h : ℕ} (x : Fin h → ZMod 2) :
    weightPhase x = (weight x : ZMod 4) := by simp [weightPhase, weight, bitLift]

/-- The exact quadratic correction records overlap parity. -/
theorem weightPhase_add {h : ℕ} (x y : Fin h → ZMod 2) :
    weightPhase (x + y) = weightPhase x + weightPhase y - doubleLift (Labels.binary h x y) := by
  simp only [weightPhase, Pi.add_apply, bitLift_add, Finset.sum_sub_distrib, Finset.sum_add_distrib]
  rw [← map_sum]
  simp [Labels.binary, Labels.form_apply]

/-- Orthogonal binary vectors have additive weight modulo four. -/
theorem weightPhase_add_of_orthogonal {h : ℕ} (x y : Fin h → ZMod 2)
    (hxy : Labels.binary h x y = 0) :
    weightPhase (x + y) = weightPhase x + weightPhase y := by
  rw [weightPhase_add, hxy, map_zero, sub_zero]

@[simp] theorem weightPhase_zero {h : ℕ} : weightPhase (0 : Fin h → ZMod 2) = 0 := by
  simp [weightPhase]

theorem weightPhase_smul {h : ℕ} (t : ZMod 2) (v : Fin h → ZMod 2) :
    weightPhase (t • v) = bitLift t * weightPhase v := by
  fin_cases t
  · change weightPhase ((0 : ZMod 2) • v) = bitLift 0 * weightPhase v
    simp
  · change weightPhase ((1 : ZMod 2) • v) = bitLift 1 * weightPhase v
    simp

theorem weightPhase_sum {h : ℕ} {ι : Type*} (s : Finset ι) (v : ι → Fin h → ZMod 2)
    (horth : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → Labels.binary h (v i) (v j) = 0) :
    weightPhase (∑ i ∈ s, v i) = ∑ i ∈ s, weightPhase (v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, weightPhase_add_of_orthogonal]
    · rw [ih]
      intro j hj k hk hjk
      exact horth j (by simp [hj]) k (by simp [hk]) hjk
    · rw [map_sum]
      apply Finset.sum_eq_zero
      intro j hj
      apply horth i (by simp) j (by simp [hj])
      intro hij
      exact hi (hij ▸ hj)

/-- An orthonormal projection has a weight phase equal to the sum of its
individual one-direction phases. -/
theorem weightPhase_project {h d : ℕ} (hs : (Labels.binary h).IsSymm)
    (W : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hw : ((Labels.binary h).restrict W).Nondegenerate) (b : Basis (Fin d) (ZMod 2) W)
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0)
    (x : Fin h → ZMod 2) :
    weightPhase (project (Labels.binary h) hs W hw x) =
      ∑ i, weightPhase (b i : Fin h → ZMod 2) * bitLift (Labels.binary h (b i) x) := by
  rw [project_eq_sum (Labels.binary h) hs W hw b hgram]
  simp only [LinearMap.sum_apply, rankOne_apply]
  rw [weightPhase_sum]
  · apply Finset.sum_congr rfl
    intro i _
    rw [weightPhase_smul, mul_comm]
  · intro i _ j _ hij
    simp [map_smul, LinearMap.smul_apply, hgram, hij]

/-- The phase difference on a nested edge is exactly the residual phase. -/
theorem weightPhase_difference {h : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (x : Fin h → ZMod 2) :
    weightPhase (project (Labels.binary h) hs V hv x) -
        weightPhase (project (Labels.binary h) hs U hu x) =
      weightPhase (project (Labels.binary h) hs (residual (Labels.binary h) U V)
        (residual_nondegenerate (Labels.binary h) hs U V hu hv hUV) x) := by
  let hw := residual_nondegenerate (Labels.binary h) hs U V hu hv hUV
  have hp := congrArg (fun f : (Fin h → ZMod 2) →ₗ[ZMod 2] (Fin h → ZMod 2) => f x)
    (difference_eq_project (Labels.binary h) hs U V hu hv hUV)
  change project (Labels.binary h) hs V hv x - project (Labels.binary h) hs U hu x =
    project (Labels.binary h) hs (residual (Labels.binary h) U V) hw x at hp
  have hadd : project (Labels.binary h) hs V hv x = project (Labels.binary h) hs U hu x +
      project (Labels.binary h) hs (residual (Labels.binary h) U V) hw x := by
    rw [← hp]
    abel
  have horth : Labels.binary h (project (Labels.binary h) hs U hu x)
      (project (Labels.binary h) hs (residual (Labels.binary h) U V) hw x) = 0 :=
    (project_mem (Labels.binary h) hs _ hw x).2 _ (project_mem (Labels.binary h) hs U hu x)
  rw [hadd, weightPhase_add_of_orthogonal _ _ horth, add_sub_cancel_left]

/-- The complete rank-dependent phase formula. The number of actual basis terms
is the dimension difference; the residual norm-one hypothesis is explicit. -/
theorem exists_phase_decomposition {h : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (hunit : residual (Labels.binary h) U V = ⊥ ∨
      ∃ v : residual (Labels.binary h) U V, Labels.binary h v v = 1) :
    ∃ b : Basis (Fin (finrank (ZMod 2) (residual (Labels.binary h) U V)))
        (ZMod 2) (residual (Labels.binary h) U V),
      (∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0) ∧
      (∀ x, weightPhase (project (Labels.binary h) hs V hv x) -
          weightPhase (project (Labels.binary h) hs U hu x) =
        ∑ i, weightPhase (b i : Fin h → ZMod 2) * bitLift (Labels.binary h (b i) x)) ∧
      finrank (ZMod 2) (residual (Labels.binary h) U V) = finrank (ZMod 2) V - finrank (ZMod 2) U := by
  obtain ⟨b, hgram, _, hd⟩ := exists_difference_decomposition (Labels.binary h) hs U V hu hv hUV hunit
  refine ⟨b, hgram, ?_, hd⟩
  intro x
  rw [weightPhase_difference hs U V hu hv hUV]
  exact weightPhase_project hs _ _ b hgram x

/-- Dot-product norm is the parity of the actual integer Hamming weight. -/
theorem weight_cast_two {h : ℕ} (v : Fin h → ZMod 2) :
    (weight v : ZMod 2) = Labels.binary h v v := by
  have hm (t : ZMod 2) : t * t = t := by fin_cases t <;> rfl
  simp [weight, Labels.binary, Labels.form_apply, hm]

/-- Every unit direction contributes a positive or negative quarter-turn phase. -/
theorem unit_weightPhase {h : ℕ} (v : Fin h → ZMod 2) (hv : Labels.binary h v v = 1) :
    weightPhase v = 1 ∨ weightPhase v = -1 := by
  have hpar : weight v % 2 = 1 := by
    have hh := congrArg ZMod.val ((weight_cast_two v).trans hv)
    simpa only [ZMod.val_natCast, show (1 : ZMod 2).val = 1 from rfl] using hh
  have hmod : weight v % 4 = 1 ∨ weight v % 4 = 3 := by omega
  rw [weightPhase_eq_weight]
  rcases hmod with hmod | hmod
  · left
    apply ZMod.val_injective 4
    simpa only [ZMod.val_natCast, show (1 : ZMod 4).val = 1 from rfl] using hmod
  · right
    apply ZMod.val_injective 4
    simpa using hmod

end Weight

section ComplexPhase

/-- Exact fourth roots of unity; all values are Gaussian integers. -/
noncomputable def phase (q : ZMod 4) : ℂ := Complex.I ^ q.val

@[simp] theorem phase_zero : phase 0 = 1 := rfl

@[simp] theorem phase_one : phase 1 = Complex.I := by change Complex.I ^ 1 = Complex.I; exact pow_one _

theorem phase_add (q r : ZMod 4) : phase (q + r) = phase q * phase r := by
  unfold phase
  rw [ZMod.val_add]
  fin_cases q <;> fin_cases r <;> norm_num [ZMod.val, pow_succ, Complex.I_mul_I]

noncomputable def phaseCharacter : AddChar (ZMod 4) ℂ where
  toFun := phase
  map_zero_eq_one' := phase_zero
  map_add_eq_mul' := phase_add

theorem phase_sum {ι : Type*} (s : Finset ι) (q : ι → ZMod 4) :
    phase (∑ i ∈ s, q i) = ∏ i ∈ s, phase (q i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | @insert i s hi ih => simp [Finset.sum_insert hi, Finset.prod_insert hi, phase_add, ih]

theorem phase_neg_mul (q : ZMod 4) : phase (-q) * phase q = 1 := by
  rw [← phase_add, neg_add_cancel, phase_zero]

/-- The scalar identity which Walsh conjugation turns into a translation kernel. -/
theorem phase_bit (q : ZMod 4) (b : ZMod 2) :
    phase (q * bitLift b) = (1 + phase q) / 2 +
      (1 - phase q) / 2 * (if b = 0 then 1 else -1) := by
  fin_cases b
  · change phase (q * 0) = (1 + phase q) / 2 + (1 - phase q) / 2 * 1
    rw [mul_zero, phase_zero]
    ring
  · change phase (q * 1) = (1 + phase q) / 2 + (1 - phase q) / 2 * (-1)
    rw [mul_one]
    ring

/-- Multiplication by a fourth-root phase at every address, with an explicit
inverse. This is the diagonal operator before Walsh conjugation. -/
noncomputable def phaseDiagonal {α : Type*} (q : α → ZMod 4) :
    (α → ℂ) ≃ₗ[ℂ] (α → ℂ) where
  toFun f x := phase (q x) * f x
  invFun f x := phase (-q x) * f x
  left_inv f := by
    funext x
    dsimp only
    rw [← mul_assoc, phase_neg_mul, one_mul]
  right_inv f := by
    funext x
    dsimp only
    rw [← mul_assoc, ← phase_add, add_neg_cancel, phase_zero, one_mul]
  map_add' f g := by funext x; exact mul_add _ _ _
  map_smul' t f := by
    funext x
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]
    ring

/-- Composition adds the exact phases; no approximation or tolerance appears. -/
theorem phaseDiagonal_trans {α : Type*} (q r : α → ZMod 4) :
    (phaseDiagonal q).trans (phaseDiagonal r) = phaseDiagonal (q + r) := by
  ext f x
  simp only [phaseDiagonal, LinearEquiv.trans_apply, LinearEquiv.coe_mk,
    LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, phase_add]
  ring

/-- Exact diagonal edge factorization into one scalar phase factor for each
orthonormal residual direction. Walsh conjugation into translation operators
is a separate obligation. -/
theorem diagonal_edge_apply {h d : ℕ} (hs : (Labels.binary h).IsSymm)
    (U V : Submodule (ZMod 2) (Fin h → ZMod 2))
    (hu : ((Labels.binary h).restrict U).Nondegenerate)
    (hv : ((Labels.binary h).restrict V).Nondegenerate) (hUV : U ≤ V)
    (b : Basis (Fin d) (ZMod 2) (residual (Labels.binary h) U V))
    (hgram : ∀ i j, Labels.binary h (b i) (b j) = if i = j then 1 else 0)
    (f : (Fin h → ZMod 2) → ℂ) (x : Fin h → ZMod 2) :
    ((phaseDiagonal (fun x => weightPhase (project (Labels.binary h) hs U hu x))).symm.trans
      (phaseDiagonal (fun x => weightPhase (project (Labels.binary h) hs V hv x)))) f x =
      (∏ i, phase (weightPhase (b i : Fin h → ZMod 2) * bitLift (Labels.binary h (b i) x))) * f x := by
  change phase (weightPhase (project (Labels.binary h) hs V hv x)) *
    (phase (-weightPhase (project (Labels.binary h) hs U hu x)) * f x) = _
  rw [← mul_assoc, ← phase_add, ← sub_eq_add_neg, weightPhase_difference hs U V hu hv hUV,
    weightPhase_project hs _ _ b hgram x, phase_sum]

end ComplexPhase
end IntegerMultBounds.Networks.BinaryPhase
