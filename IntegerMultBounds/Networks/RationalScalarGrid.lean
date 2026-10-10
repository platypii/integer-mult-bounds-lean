import IntegerMultBounds.Networks.GaussianBoundedArithmetic
import IntegerMultBounds.Networks.CircuitCoefficients
import IntegerMultBounds.Networks.GroupedModuleFrames

/-! Numerator certificates apply to the same rational module gate rows on
complex arrays, preserving literal row order and source/target names. -/
namespace IntegerMultBounds.Networks.RationalScalarGrid
open Circuit GaussianPrecision
variable {ι Ω : Type*} [DecidableEq ι]

def castGate (g : Gate ι ℚ) : Gate ι ℂ := ⟨g.target,g.terms.map (fun p => (p.1,(p.2:ℂ)))⟩
def castRows (gs : Program ι ℚ) := gs.map castGate

omit [DecidableEq ι] in
theorem coefficients (gs : Program ι ℚ) (d B : ℕ)
    (h : CircuitCoefficients.All (fun c : ℚ => BoundedGrid d B (c:ℂ)) gs) :
    CircuitCoefficients.All (BoundedGrid d B) (castRows gs) := by
  intro g hg t ht
  obtain ⟨g0,hg0,rfl⟩ := List.mem_map.mp hg
  obtain ⟨t0,ht0,rfl⟩ := List.mem_map.mp ht
  exact h g0 hg0 t0 ht0

theorem gate_pointwise (g : Gate ι ℚ) (x : ι → Ω → ℂ) (i : ι) (ω : Ω) :
    FramedCircuit.moduleGate g x i ω=(castGate g).run (fun j => x j ω) i := by
  have hs : ((g.terms.map fun p => p.2 • x p.1).sum) ω=
      ((g.terms.map fun p => (p.2:ℂ)*x p.1 ω)).sum := by
    generalize g.terms=ps
    induction ps with
    | nil => rfl
    | cons p ps ih =>
      simp only [List.map_cons,List.sum_cons,Pi.add_apply,Pi.smul_apply,ih]
      congr 1
  by_cases hi : i=g.target
  · subst i
    simp only [FramedCircuit.moduleGate,Gate.run,castGate,Function.update_self,List.map_map,
      Function.comp_def,Pi.add_apply]
    rw [hs]
  · simp [FramedCircuit.moduleGate,Gate.run,castGate,Function.update_of_ne hi]

theorem run_pointwise (gs : Program ι ℚ) (x : ι → Ω → ℂ) (i : ι) (ω : Ω) :
    FramedCircuit.moduleRun gs x i ω=Circuit.run (castRows gs) (fun j => x j ω) i := by
  induction gs generalizing x with
  | nil => rfl
  | cons g gs ih =>
    rw [FramedCircuit.moduleRun_cons,ih]
    simp_rw [gate_pointwise]
    rfl

theorem bounded (gs : Program ι ℚ) (x : ι → Ω → ℂ) (n d M B : ℕ)
    (hx : ∀ i ω,BoundedGrid n M (x i ω))
    (hc : CircuitCoefficients.All (fun c : ℚ => BoundedGrid d B (c:ℂ)) gs) (i : ι) (ω : Ω) :
    BoundedGrid (n+gs.length*d) (scalarBound d B (castRows gs) M)
      (FramedCircuit.moduleRun gs x i ω) := by
  rw [run_pointwise]
  have h := bounded_run (castRows gs) (fun i => x i ω) n d M B (fun i => hx i ω)
    (coefficients gs d B hc) i
  simpa only [castRows,List.length_map] using h

end IntegerMultBounds.Networks.RationalScalarGrid
