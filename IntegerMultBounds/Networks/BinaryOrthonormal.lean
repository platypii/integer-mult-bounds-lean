import Mathlib.LinearAlgebra.BilinearForm.Orthogonal
import Mathlib.LinearAlgebra.Basis.Fin
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic

/-! Orthonormalization of symmetric bilinear forms over the binary field.
Characteristic two needs a separate argument: a unit line absorbs a hyperbolic
plane through the three vectors `w+a`, `w+b`, and `w+a+b`. -/

namespace IntegerMultBounds.Networks.BinaryOrthonormal

open Module LinearMap

abbrev F := ZMod 2

private theorem eq_one_of_ne_zero (t : F) (ht : t ≠ 0) : t = 1 := by
  fin_cases t
  · exact False.elim (ht rfl)
  · rfl

variable {V : Type*} [AddCommGroup V] [Module F V]

/-- The explicit replacement vectors for a unit line plus a hyperbolic plane. -/
def absorbed (w a b : V) : Fin 3 → V := ![w + a, w + b, w + a + b]

/-- The absorption has identity Gram matrix, including all three unit norms. -/
theorem absorbed_gram (B : LinearMap.BilinForm F V) (hsym : B.IsSymm) (w a b : V)
    (hww : B w w = 1) (haa : B a a = 0) (hbb : B b b = 0)
    (hwa : B w a = 0) (hwb : B w b = 0) (hab : B a b = 1) :
    ∀ i j, B (absorbed w a b i) (absorbed w a b j) = if i = j then 1 else 0 := by
  have haw : B a w = 0 := (hsym.eq a w).trans hwa
  have hbw : B b w = 0 := (hsym.eq b w).trans hwb
  have hba : B b a = 1 := (hsym.eq b a).trans hab
  intro i j
  fin_cases i <;> fin_cases j <;>
    norm_num [absorbed, map_add, LinearMap.add_apply, hww, haa, hbb, hwa, hwb, hab, haw, hbw, hba] <;> decide

/-- Orthogonality to a unit line can be checked against its generator alone. -/
theorem mem_unitComplement (B : LinearMap.BilinForm F V) (w v : V) :
    v ∈ B.orthogonal (F ∙ w) ↔ B w v = 0 := by
  constructor
  · exact fun hv => hv w (Submodule.mem_span_singleton_self w)
  · intro h z hz
    obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.mp hz
    simp [map_smul, LinearMap.smul_apply, h]

/-- A unit vector can be chosen so that its orthogonal complement is either
zero or remains nonalternating. If the first complement is alternating, one
hyperbolic plane is absorbed to obtain a better unit vector. -/
theorem exists_good_unit (B : LinearMap.BilinForm F V) (hsym : B.IsSymm)
    (hnd : B.Nondegenerate) (w : V) (hw : B w w = 1) :
    ∃ u : V, B u u = 1 ∧
      (B.orthogonal (F ∙ u) = ⊥ ∨ ∃ v : B.orthogonal (F ∙ u), B v v = 1) := by
  classical
  let W := B.orthogonal (F ∙ w)
  by_cases hzero : W = ⊥
  · exact ⟨w, hw, Or.inl hzero⟩
  by_cases hone : ∃ v : W, B v v = 1
  · exact ⟨w, hw, Or.inr hone⟩
  have hnorm (v : W) : B v v = 0 := by
    by_contra h
    exact hone ⟨v, eq_one_of_ne_zero _ h⟩
  obtain ⟨a, ha, ha0⟩ := (Submodule.ne_bot_iff W).mp hzero
  have hW : (B.restrict W).Nondegenerate :=
    B.restrict_nondegenerate_orthogonal_spanSingleton hnd hsym.isRefl (by rw [hw]; exact one_ne_zero)
  have hpartner : ∃ b : W, (B.restrict W) ⟨a, ha⟩ b ≠ 0 := by
    by_contra! h
    have hz := hW.1 ⟨a, ha⟩ h
    exact ha0 (congrArg (fun v : W => (v : V)) hz)
  obtain ⟨b, hab⟩ := hpartner
  have hg := absorbed_gram B hsym w a b hw (hnorm ⟨a, ha⟩) (hnorm b)
    ((mem_unitComplement B w a).mp ha) ((mem_unitComplement B w b).mp b.property)
    (eq_one_of_ne_zero _ hab)
  refine ⟨w + a, ?_, Or.inr ⟨⟨w + b, ?_⟩, ?_⟩⟩
  · simpa [absorbed] using hg 0 0
  · apply (mem_unitComplement B (w + a) (w + b)).mpr
    simpa [absorbed] using hg 0 1
  · simpa [absorbed] using hg 1 1

/-- Every finite-dimensional symmetric nondegenerate binary form which contains
a unit vector admits an orthonormal basis. No division by two is used. -/
theorem exists_orthonormal_basis [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hsym : B.IsSymm) (hnd : B.Nondegenerate)
    (hone : ∃ w : V, B w w = 1) :
    ∃ b : Basis (Fin (finrank F V)) F V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  classical
  suffices ∀ d, finrank F V = d → (d = 0 ∨ ∃ w : V, B w w = 1) →
      ∃ b : Basis (Fin d) F V, ∀ i j, B (b i) (b j) = if i = j then 1 else 0 by
    exact this _ rfl (Or.inr hone)
  intro d hd hon
  clear hone
  induction d generalizing V with
  | zero => exact ⟨basisOfFinrankZero hd, fun i => Fin.elim0 i⟩
  | succ d ih =>
    obtain ⟨w, hw⟩ := hon.resolve_left (by omega)
    obtain ⟨u, hu, hgood⟩ := exists_good_unit B hsym hnd w hw
    have huu : B u u ≠ 0 := by rw [hu]; exact one_ne_zero
    have hu0 : u ≠ 0 := by
      intro hz
      simp only [hz, map_zero] at hu
      exact zero_ne_one hu
    let W := B.orthogonal (F ∙ u)
    have hdim : finrank F W = d := by
      have hdims := Submodule.finrank_add_eq_of_isCompl
        (LinearMap.BilinForm.isCompl_span_singleton_orthogonal huu)
      rw [finrank_span_singleton hu0, hd] at hdims
      change finrank F (B.orthogonal (F ∙ u)) = d
      omega
    have hW : (B.restrict W).Nondegenerate :=
      B.restrict_nondegenerate_orthogonal_spanSingleton hnd hsym.isRefl huu
    have hWunit : d = 0 ∨ ∃ v : W, (B.restrict W) v v = 1 := by
      rcases hgood with hzero | hunit
      · left
        have hz : finrank F W = 0 := Submodule.finrank_eq_zero.mpr hzero
        omega
      · exact Or.inr hunit
    obtain ⟨b, hb⟩ := ih (B.restrict W) (hsym.restrict W) hW hdim hWunit
    have hli : ∀ (t : F), ∀ x ∈ W, t • u + x = 0 → t = 0 := by
      intro t x hx he
      have hx0 := (mem_unitComplement B u x).mp hx
      have hh := congrArg (fun z => B u z) he
      simpa only [map_add, map_smul, hu, hx0, smul_eq_mul, mul_one, add_zero, map_zero] using hh
    have hsp : ∀ z : V, ∃ t : F, z + t • u ∈ W := by
      intro z
      refine ⟨-B u z, (mem_unitComplement B u _).mpr ?_⟩
      simp only [map_add, map_smul, hu, smul_eq_mul, mul_one, add_neg_cancel]
    let basis := Basis.mkFinCons u b hli hsp
    refine ⟨basis, ?_⟩
    change ∀ i j, B (Basis.mkFinCons u b hli hsp i) (Basis.mkFinCons u b hli hsp j) = _
    rw [Basis.coe_mkFinCons]
    intro i j
    refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simpa using hu
    · simpa [Ne.symm (Fin.succ_ne_zero j)] using (mem_unitComplement B u (b j)).mp (b j).property
    · simpa [hsym.eq (b i) u] using (mem_unitComplement B u (b i)).mp (b i).property
    · simpa using hb i j

/-- Equivalent formulation in terms of nonalternation, as used for binary
orthogonal residuals in the manuscript. -/
theorem exists_orthonormal_basis_of_not_alternating [FiniteDimensional F V]
    (B : LinearMap.BilinForm F V) (hsym : B.IsSymm) (hnd : B.Nondegenerate)
    (hnonalt : ¬ B.IsAlt) :
    ∃ b : Basis (Fin (finrank F V)) F V,
      ∀ i j, B (b i) (b j) = if i = j then 1 else 0 := by
  apply exists_orthonormal_basis B hsym hnd
  by_contra! h
  apply hnonalt
  intro w
  by_contra hw
  exact h w (eq_one_of_ne_zero _ hw)

end IntegerMultBounds.Networks.BinaryOrthonormal
