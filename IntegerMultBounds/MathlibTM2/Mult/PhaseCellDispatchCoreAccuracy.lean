module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFamilyDispatchInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedWindows

/-! # Cropping actual dispatch results

The Forall₂ relation retains the pairing between each production input and its
returned output. Arithmetic error and locality error are charged on that same
output, rather than choosing a separate approximate solver.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

variable {s A : ℕ} [NeZero s]

/-- Locality for the real and imaginary principal solutions turns the raw S3
trace into global accuracy on the owned core. -/
theorem FamilyDispatchApprox.core_accuracy {p l t : ℕ} (r : FamilyDispatchInput s A)
    (x y X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (Zs : List (ZMod s → GaussianInt)) (h : FamilyDispatchApprox p l t r x y Zs)
    (core : Finset (ZMod s)) (hcore : core ⊆ haloVertices s r.a r.b)
    (locality : ℝ)
    (hx : ∀ F ∈ r.inputs, ErrorOn core (x F) (X F) locality)
    (hy : ∀ F ∈ r.inputs, ErrorOn core (y F) (Y F) locality) :
    List.Forall₂ (fun F Z => ErrorOn core
      (pairedCellRead (r.precision p l t) (r.width p l t)
        (cstream A (r.width p l t) (chirpLine s Z)))
      (fun i => (⟨X F i,Y F i⟩ : ℂ)) (1/(2 : ℝ)^r.target+(locality+locality))) r.inputs Zs := by
  have hm := (List.forall₂_and_left r.inputs Zs).mpr
    ⟨fun _ hF => hF,h⟩
  apply List.Forall₂.imp _ hm
  intro F Z hpair
  apply (hpair.2.crop hcore).trans
  intro i hi
  have hr := hx F hpair.1 i hi
  have him := hy F hpair.1 i hi
  have hn := Complex.norm_le_abs_re_add_abs_im ((⟨x F i,y F i⟩ : ℂ)-⟨X F i,Y F i⟩)
  simp only [Real.norm_eq_abs] at hr him
  exact hn.trans (add_le_add hr him)

open IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.SchurDominance

/-- Generated-window specialization: both locality premises are discharged
against the actual rounded matrix and actual returned principal solutions. -/
theorem FamilyDispatchApprox.generated_core_accuracy {p l t : ℕ}
    (r : FamilyDispatchInput s A) (width target k : ℕ)
    (hst : s < t) {α d : ℝ} (hα : 0 < α) (hp : 2 ≤ p)
    (hwidth : 8*p ≤ 2^r.u) (hαu : α^2 = (r.u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hhalo : haloVertices s r.a r.b = (generatedWindow s width p r.u target k).halo)
    (x y X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (rhsRe rhsIm : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (hx : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (x F) (rhsRe F))
    (hy : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) (haloVertices s r.a r.b) (y F) (rhsIm F))
    (hX : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (X F) (rhsRe F))
    (hY : ∀ F ∈ r.inputs, Solves (realMatrix s t p r.u) Finset.univ (Y F) (rhsIm F))
    (hRe : ∀ F ∈ r.inputs, ∀ i, |rhsRe F i| ≤ 1/2)
    (hIm : ∀ F ∈ r.inputs, ∀ i, |rhsIm F i| ≤ 1/2)
    (Zs : List (ZMod s → GaussianInt)) (h : FamilyDispatchApprox p l t r x y Zs) :
    List.Forall₂ (fun F Z => ErrorOn (ownedCore s width k)
      (pairedCellRead (r.precision p l t) (r.width p l t)
        (cstream A (r.width p l t) (chirpLine s Z)))
      (fun i => (⟨X F i,Y F i⟩ : ℂ))
      (1/(2 : ℝ)^r.target+(1/(2 : ℝ)^target+1/(2 : ℝ)^target))) r.inputs Zs := by
  refine h.core_accuracy r x y X Y Zs (ownedCore s width k) ?_ (1/(2 : ℝ)^target) ?_ ?_
  · rw [hhalo]
    exact (generatedWindow s width p r.u target k).core_subset_halo
  · intro F hF
    exact generatedWindow_solution_error hst hα width p r.u target k hp hwidth hαu hθ hgap hbudget
      (X F) (x F) (rhsRe F) (hX F hF) (by rw [← hhalo]; exact hx F hF) (hRe F hF)
  · intro F hF
    exact generatedWindow_solution_error hst hα width p r.u target k hp hwidth hαu hθ hgap hbudget
      (Y F) (y F) (rhsIm F) (hY F hF) (by rw [← hhalo]; exact hy F hF) (hIm F hF)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
