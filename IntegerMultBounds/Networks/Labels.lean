import IntegerMultBounds.Networks.Scalar
import Mathlib.LinearAlgebra.BilinearForm.Properties
import Mathlib.Data.ZMod.Basic

/-! The degree-one bilinear label spaces of the two finite motifs. These are
label fields, distinct from the scalar rings on the circuit wires. Tensor-cube
labels, nested gate labels, and the total residual-rank saving remain separate. -/

namespace IntegerMultBounds.Networks.Labels

variable {h : ℕ} {R : Type*} [CommRing R]

/-- Dot product with a constant all-one rank-one correction. -/
def form (weight : R) : LinearMap.BilinForm R (Fin h → R) :=
  LinearMap.mk₂ R
    (fun x y => (∑ i, x i * y i) - weight * (∑ i, x i) * (∑ i, y i))
    (by intros; simp only [Pi.add_apply, add_mul, Finset.sum_add_distrib, mul_add]; ring)
    (by intro c x y
        simp only [Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum]
        ring)
    (by intros; simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]; ring)
    (by intro c x y
        have ht (i : Fin h) : x i * (c * y i) = c * (x i * y i) := by ring
        simp only [Pi.smul_apply, smul_eq_mul, ht, ← Finset.mul_sum]
        ring)

theorem form_apply (weight : R) (x y : Fin h → R) :
    form weight x y = (∑ i, x i * y i) - weight * (∑ i, x i) * (∑ i, y i) := rfl

theorem form_symm (weight : R) (x y : Fin h → R) : form weight x y = form weight y x := by
  simp only [form_apply]
  congr 1
  · apply Finset.sum_congr rfl; intros; ring
  · ring

def indicator (S : Finset (Fin h)) : Fin h → R := fun i => if i ∈ S then 1 else 0

theorem sum_indicator (S : Finset (Fin h)) : ∑ i, (indicator S i : R) = S.card := by
  simp [indicator]

theorem indicator_dot (S T : Finset (Fin h)) :
    (∑ i, (indicator S i : R) * indicator T i) = (S ∩ T).card := by
  have ht (i : Fin h) : (indicator S i : R) * indicator T i = indicator (S ∩ T) i := by
    simp only [indicator, Finset.mem_inter]
    split_ifs <;> simp_all
  simp_rw [ht]
  exact sum_indicator _

theorem form_indicator (weight : R) (S T : Finset (Fin h)) :
    form weight (indicator S) (indicator T) =
      ((S ∩ T).card : R) - weight * S.card * T.card := by
  rw [form_apply, indicator_dot, sum_indicator, sum_indicator]

/-- The rational labels for the bit-valued network use I minus J/9. -/
def rational (h : ℕ) : LinearMap.BilinForm ℚ (Fin h → ℚ) := form (1 / 9)

/-- The binary labels for the complex-valued network use ordinary dot product. -/
def binary (h : ℕ) : LinearMap.BilinForm (ZMod 2) (Fin h → ZMod 2) := form 0

theorem rational_triples (S T : Finset (Fin h)) (hs : S.card = 3) (ht : T.card = 3) :
    rational h (indicator S) (indicator T) = ((S ∩ T).card : ℚ) - 1 := by
  rw [rational, form_indicator, hs, ht]
  norm_num

theorem binary_subsets (S T : Finset (Fin h)) :
    binary h (indicator S) (indicator T) = ((S ∩ T).card : ZMod 2) := by
  simp [binary, form_indicator]

theorem rational_self (S : Finset (Fin h)) (hs : S.card = 3) :
    rational h (indicator S) (indicator S) = 2 := by
  rw [rational_triples S S hs hs]
  norm_num [hs]

theorem binary_self (S : Finset (Fin h)) (hs : S.card = 3) :
    binary h (indicator S) (indicator S) = 1 := by
  rw [binary_subsets]
  norm_num [hs]
  decide

theorem rational_neighbors (S T : Finset (Fin h)) (hs : S.card = 3) (ht : T.card = 3)
    (hneighbors : (S ∩ T).card = 1) : rational h (indicator S) (indicator T) = 0 := by
  rw [rational_triples S T hs ht, hneighbors]
  norm_num

theorem binary_neighbors (S T : Finset (Fin h)) (hneighbors : Even (S ∩ T).card) :
    binary h (indicator S) (indicator T) = 0 := by
  rw [binary_subsets]
  obtain ⟨k, hk⟩ := hneighbors
  rw [hk, Nat.cast_add]
  exact add_eq_zero_iff_eq_neg.mpr (ZMod.neg_eq_self_mod_two _).symm

theorem form_single (weight : R) (x : Fin h → R) (i : Fin h) :
    form weight x (Pi.single i 1) = x i - weight * ∑ j, x j := by
  simp [form_apply, Pi.single_apply]

theorem rational_separating (hh : h ≠ 9) (x : Fin h → ℚ)
    (hx : ∀ y, rational h x y = 0) : x = 0 := by
  have he (i : Fin h) : x i = (1 / 9 : ℚ) * ∑ j, x j := by
    have hi := hx (Pi.single i 1)
    rw [rational, form_single] at hi
    exact sub_eq_zero.mp hi
  have hs : (∑ i, x i) = (h : ℚ) * ((1 / 9 : ℚ) * ∑ i, x i) := by
    calc
      (∑ i, x i) = ∑ _ : Fin h, ((1 / 9 : ℚ) * ∑ i, x i) := Finset.sum_congr rfl (fun i _ => he i)
      _ = _ := by simp
  have hh' : (h : ℚ) ≠ 9 := by exact_mod_cast hh
  have hz : (∑ i, x i) = 0 := by
    have hp : ((h : ℚ) - 9) * (∑ i, x i) = 0 := by nlinarith [hs]
    exact (mul_eq_zero.mp hp).resolve_left (sub_ne_zero.mpr hh')
  funext i
  simp [he i, hz]

theorem rational_nondegenerate (hh : h ≠ 9) : (rational h).Nondegenerate := by
  constructor
  · exact rational_separating hh
  · intro x hx
    apply rational_separating hh x
    intro y
    rw [rational, form_symm]
    exact hx y

theorem binary_nondegenerate : (binary h).Nondegenerate := by
  have hl : (binary h).SeparatingLeft := by
    intro x hx
    funext i
    have hi := hx (Pi.single i 1)
    simpa [binary, form_single] using hi
  refine ⟨hl, ?_⟩
  intro x hx
  apply hl x
  intro y
  rw [binary, form_symm]
  exact hx y

/-- A vector with nonzero self-pairing spans a nondegenerate line. -/
theorem line_nondegenerate {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (B : LinearMap.BilinForm K E) (v : E) (hv : B v v ≠ 0) :
    (B.domRestrict₁₂ (Submodule.span K {v}) (Submodule.span K {v})).Nondegenerate := by
  constructor
  · rintro ⟨x, hx⟩ horth
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ht := horth ⟨v, Submodule.subset_span (by simp)⟩
    change B (a • v) v = 0 at ht
    rw [LinearMap.BilinForm.smul_left] at ht
    have ha := (mul_eq_zero.mp ht).resolve_right hv
    apply Subtype.ext
    simp [ha]
  · rintro ⟨x, hx⟩ horth
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hx
    have ht := horth ⟨v, Submodule.subset_span (by simp)⟩
    change B v (a • v) = 0 at ht
    rw [LinearMap.BilinForm.smul_right] at ht
    have ha := (mul_eq_zero.mp ht).resolve_right hv
    apply Subtype.ext
    simp [ha]

theorem rational_line_nondegenerate (S : Finset (Fin h)) (hs : S.card = 3) :
    ((rational h).domRestrict₁₂ (Submodule.span ℚ {indicator S})
      (Submodule.span ℚ {indicator S})).Nondegenerate := by
  apply line_nondegenerate
  rw [rational_self S hs]
  norm_num

theorem binary_line_nondegenerate (S : Finset (Fin h)) (hs : S.card = 3) :
    ((binary h).domRestrict₁₂ (Submodule.span (ZMod 2) {indicator S})
      (Submodule.span (ZMod 2) {indicator S})).Nondegenerate := by
  apply line_nondegenerate
  rw [binary_self S hs]
  exact one_ne_zero

end IntegerMultBounds.Networks.Labels
