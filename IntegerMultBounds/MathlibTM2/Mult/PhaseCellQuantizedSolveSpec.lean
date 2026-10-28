module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
public import IntegerMultBounds.NLogN.SchurPerturbSolve

/-! Lift an executed grid solver's arithmetic error through input quantization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
open IntegerMultBounds.NLogN.SchurDominance Finset

theorem SolveSpec.mono_error {ι : Type} {A : Matrix ι ι ℝ} {active core : Finset ι}
    {rhsBound error error' : ℝ} {solve : (ι → ℝ) → ι → ℝ}
    (h : SolveSpec A active core rhsBound solve error) (he : error ≤ error') :
    SolveSpec A active core rhsBound solve error' :=
  fun x b hx hb i hi => (h x b hx hb i hi).trans he

theorem SolveSpec.of_rhs_rounding {ι : Type} [DecidableEq ι] [Fintype ι]
    (A : Matrix ι ι ℝ) (active core : Finset ι) (hcore : core ⊆ active)
    (μ : ℝ) (hμ : 0 < μ) (hA : DominatesOn A active μ)
    (rhsBound δ error : ℝ) (quantize solve : (ι → ℝ) → ι → ℝ)
    (hquantize : ∀ b, (∀ i ∈ active, |b i| ≤ rhsBound) → ∀ i ∈ active, |quantize b i-b i| ≤ δ)
    (hsolve : ∀ b, (∀ i ∈ active, |b i| ≤ rhsBound) → ∀ y,
      Solves A active y (quantize b) → ErrorOn core (solve b) y error) :
    SolveSpec A active core rhsBound solve (error+δ/μ) := by
  intro x b hx hb
  obtain ⟨y,hy⟩ := solves_exists A active μ hμ hA (quantize b)
  have hd : Solves A active (fun i => y i-x i) (fun i => quantize b i-b i) := by
    intro i hi
    simp only [mul_sub,Finset.sum_sub_distrib,hy i hi,hx i hi]
  apply (hsolve b hb y hy).trans
  intro i hi
  simpa only [Real.norm_eq_abs] using
    solves_bound A active μ hμ hA _ _ hd δ (hquantize b hb) i (hcore hi)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
