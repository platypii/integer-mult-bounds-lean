module

public import IntegerMultBounds.NLogN.SchurSolve
public import Mathlib.Analysis.Normed.Group.Constructions
public import Mathlib.Analysis.Normed.Group.Real

/-! # Shared numerical endpoint for S3, S4 and S5

Windows retain ambient coordinates. Local solves concern a principal system on
`active`; passing from a halo solve to the global system requires a separate
locality estimate. Neither a particular rounding implementation nor a tape
execution/cost theorem is assumed by this numerical interface.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

open Finset

variable {ι E : Type*}

/-- The writable core and borrowed halo use the same ambient coordinate type. -/
structure Window (ι : Type*) where
  core : Finset ι
  halo : Finset ι
  core_subset_halo : core ⊆ halo

/-- Uniform coordinate error on the published core. -/
def ErrorOn [NormedAddCommGroup E] (core : Finset ι) (out target : ι → E) (error : ℝ) : Prop :=
  ∀ i ∈ core, ‖out i - target i‖ ≤ error

/-- Arithmetic and locality errors add once, independently of the core size. -/
theorem ErrorOn.trans [NormedAddCommGroup E] {core : Finset ι} {out localExact target : ι → E}
    {arithmetic locality : ℝ} (h : ErrorOn core out localExact arithmetic)
    (hlocal : ErrorOn core localExact target locality) :
    ErrorOn core out target (arithmetic + locality) := by
  intro i hi
  exact (norm_sub_le_norm_sub_add_norm_sub _ _ _).trans (add_le_add (h i hi) (hlocal i hi))

/-- Cropping can only reduce a uniform coordinate-error obligation. -/
theorem ErrorOn.crop [NormedAddCommGroup E] {core halo : Finset ι} {out target : ι → E}
    {error : ℝ} (h : ErrorOn halo out target error) (hcore : core ⊆ halo) :
    ErrorOn core out target error := fun i hi => h i (hcore hi)

/-- Publishing one owned result at each coordinate incurs no factor for the number of windows. -/
theorem norm_error_of_publish [Fintype ι] [NormedAddCommGroup E]
    (windows : List (Window ι)) (localOut : Window ι → ι → E) (out target : ι → E)
    (error : ℝ) (he : 0 ≤ error)
    (hlocal : ∀ w ∈ windows, ErrorOn w.core (localOut w) target error)
    (hpublish : ∀ i, ∃ w ∈ windows, i ∈ w.core ∧ out i = localOut w i) :
    ‖out - target‖ ≤ error := by
  apply (pi_norm_le_iff_of_nonneg he).mpr
  intro i
  obtain ⟨w, hw, hi, hvalue⟩ := hpublish i
  change ‖out i - target i‖ ≤ error
  rw [hvalue]
  exact hlocal w hw i hi

/-- Backend-independent real-solver endpoint. `active` selects a principal system
of the ambient matrix; only `core` is published. Internal recovery/boundary calls
may use a different right-hand-side bound from the outer value 1/2. -/
def SolveSpec (A : Matrix ι ι ℝ) (active core : Finset ι) (rhsBound : ℝ)
    (solve : (ι → ℝ) → ι → ℝ) (error : ℝ) : Prop :=
  ∀ x b, IntegerMultBounds.NLogN.SchurDominance.Solves A active x b →
    (∀ i ∈ active, |b i| ≤ rhsBound) → ErrorOn core (solve b) x error

/-- A halo solve gives global core accuracy only after an explicit locality
comparison with a solution of the same ambient global system. -/
theorem SolveSpec.with_locality [Fintype ι] (A : Matrix ι ι ℝ) (w : Window ι)
    (rhsBound arithmetic locality : ℝ) (solve : (ι → ℝ) → ι → ℝ)
    (hsolve : SolveSpec A w.halo w.core rhsBound solve arithmetic)
    (hlocal : ∀ x b, IntegerMultBounds.NLogN.SchurDominance.Solves A univ x b →
      (∀ i, |b i| ≤ rhsBound) →
      ∃ y, IntegerMultBounds.NLogN.SchurDominance.Solves A w.halo y b ∧
        ErrorOn w.core y x locality) :
    SolveSpec A univ w.core rhsBound solve (arithmetic + locality) := by
  intro x b hx hb
  obtain ⟨y, hy, herror⟩ := hlocal x b hx (fun i => hb i (mem_univ i))
  exact (hsolve y b hy (fun i _ => hb i (mem_univ i))).trans herror

/-- Once locality has been proved against the same global system, covering cores
supply the full solver contract. Halo-only solve contracts do not satisfy this premise. -/
theorem SolveSpec.of_windows [Fintype ι] (A : Matrix ι ι ℝ) (windows : List (Window ι))
    (rhsBound error : ℝ) (solve : (ι → ℝ) → ι → ℝ)
    (hcover : ∀ i, ∃ w ∈ windows, i ∈ w.core)
    (hsolve : ∀ w ∈ windows, SolveSpec A univ w.core rhsBound solve error) :
    SolveSpec A univ univ rhsBound solve error := by
  intro x b hx hb i _
  obtain ⟨w, hw, hi⟩ := hcover i
  exact hsolve w hw x b hx hb i hi

/-- The full endpoint is exactly the real-solver hypothesis consumed by
`FastB0.concrete_resampB₀_specX`; no equality with `pcSolve` is required. -/
theorem SolveSpec.full_error [Fintype ι] {A : Matrix ι ι ℝ} {rhsBound error : ℝ}
    {solve : (ι → ℝ) → ι → ℝ} (h : SolveSpec A univ univ rhsBound solve error)
    (x b : ι → ℝ) (hx : Matrix.mulVec A x = b) (hb : ∀ i, |b i| ≤ rhsBound) (i : ι) :
    |solve b i - x i| ≤ error := by
  have hsystem : IntegerMultBounds.NLogN.SchurDominance.Solves A univ x b := by
    intro k _
    simpa [Matrix.mulVec, dotProduct] using congrFun hx k
  simpa only [Real.norm_eq_abs] using h x b hsystem (fun k _ => hb k) i (mem_univ i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
