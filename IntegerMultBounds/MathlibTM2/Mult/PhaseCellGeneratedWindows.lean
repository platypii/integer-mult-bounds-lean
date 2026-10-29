module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWindowAssembly
public import IntegerMultBounds.NLogN.PhaseCellCoreWindows
public import IntegerMultBounds.NLogN.PhaseCellLocality
public import IntegerMultBounds.NLogN.SchurPerturbSolve

/-! # Generated windows and their global solver contract

Locality is discharged for the computed cores and halos. The remaining supplier
premise is numerical accuracy of the actual local solver; execution and cost
are separate obligations, not assumptions hidden in the window geometry.
-/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface

open Finset IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.SchurDominance
variable {s t : ℕ} [NeZero s]

def generatedWindow (s width p u target k : ℕ) [NeZero s] : Window (ZMod s) where
  core := ownedCore s width k
  halo := coreHalo s width k (PhaseCellBand.width p u) (localityDepth p target)
  core_subset_halo := ownedCore_subset_halo width k _ _

def generatedWindows (s width p u target : ℕ) [NeZero s] : List (Window (ZMod s)) :=
  (coreIndices s width).map (fun k => generatedWindow s width p u target k)

theorem generatedWindows_cover (width p u target : ℕ) (hw : 0 < width) (i : ZMod s) :
    ∃ w ∈ generatedWindows s width p u target, i ∈ w.core := by
  obtain ⟨k,hk,hi⟩ := ownedCore_cover width hw i
  exact ⟨generatedWindow s width p u target k,List.mem_map.mpr ⟨k,hk,rfl⟩,hi⟩

/-- Exact solutions on generated halos exist and have the selected locality
accuracy on their owned cores, including the full-system fallback. -/
theorem generatedWindow_locality (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (width p u target k : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (x rhs : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) univ x rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1/2) :
    ∃ y, Solves (realMatrix s t p u) (generatedWindow s width p u target k).halo y rhs ∧
      ErrorOn (generatedWindow s width p u target k).core y x (1/(2 : ℝ)^target) := by
  let : NeZero t := ⟨by omega⟩
  let H := (generatedWindow s width p u target k).halo
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hμ : (0 : ℝ) < 1/(8*p) := by positivity
  have hA := matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget
  obtain ⟨y,hy⟩ := solves_exists (realMatrix s t p u) H _ hμ
    (dominates_mono _ univ H _ (subset_univ _) hA) rhs
  refine ⟨y,hy,?_⟩
  intro i hi
  change |y i-x i| ≤ _
  by_cases hfit : localityDepth p target*PhaseCellBand.width p u ≤ coreStart width k ∧
      coreStart width k+coreLength s width k+localityDepth p target*PhaseCellBand.width p u ≤ s
  · have hy' : Solves (realMatrix s t p u)
        (PhaseCellDiscreteGeometry.haloVertices s
          (coreStart width k-localityDepth p target*PhaseCellBand.width p u)
          (coreStart width k+coreLength s width k+localityDepth p target*PhaseCellBand.width p u)) y rhs := by
      simpa only [H,generatedWindow,coreHalo,ite_eq_left hfit] using hy
    exact halo_locality_precision hst hα p u target hp hwidth hαu hθ hgap hbudget
      _ _ hfit.2 x y rhs hx hy' (fun j => (hrhs j).trans (by norm_num)) i
      (ownedCore_in_interval_layer width k _ _ hfit.1 i hi)
  · have hy' : Solves (realMatrix s t p u) univ y rhs := by
      simpa only [H,generatedWindow,coreHalo,ite_eq_right hfit] using hy
    rw [solves_unique _ univ _ hμ hA y x rhs hy' hx i (mem_univ i),sub_self,abs_zero]
    positivity

/-- The locality estimate applies to any exact local solution, including the
one used in a production dispatch trace. -/
theorem generatedWindow_solution_error (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (width p u target k : ℕ) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (x y rhs : ZMod s → ℝ) (hx : Solves (realMatrix s t p u) univ x rhs)
    (hy : Solves (realMatrix s t p u) (generatedWindow s width p u target k).halo y rhs)
    (hrhs : ∀ i, |rhs i| ≤ 1/2) :
    ErrorOn (generatedWindow s width p u target k).core y x (1/(2 : ℝ)^target) := by
  let : NeZero t := ⟨by omega⟩
  obtain ⟨z,hz,he⟩ := generatedWindow_locality hst hα width p u target k hp hwidth
    hαu hθ hgap hbudget x rhs hx hrhs
  have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
  have hμ : (0 : ℝ) < 1/(8*p) := by positivity
  have hA := dominates_mono (realMatrix s t p u) univ
    (generatedWindow s width p u target k).halo _ (subset_univ _)
    (matrix_gap s t hst hα p u hp hwidth hαu hθ hgap hbudget)
  intro i hi
  rw [solves_unique _ _ _ hμ hA y z rhs hy hz i
    ((generatedWindow s width p u target k).core_subset_halo hi)]
  exact he i hi

/-- Publishing the generated local solves yields global accuracy with no
window-count factor. Only the supplier's arithmetic tolerance remains a premise. -/
theorem generatedWindows_solve_spec (hst : s < t) {α d : ℝ} (hα : 0 < α)
    (width p u target : ℕ) (hw : 0 < width) (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u)
    (hαu : α^2 = (u : ℝ)) (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1)
    (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (solve : Window (ZMod s) → (ZMod s → ℝ) → ZMod s → ℝ)
    (initial : (ZMod s → ℝ) → ZMod s → ℝ) (arithmetic : ℝ)
    (hsolve : ∀ w ∈ generatedWindows s width p u target,
      SolveSpec (realMatrix s t p u) w.halo w.core (1/2) (solve w) arithmetic) :
    SolveSpec (realMatrix s t p u) univ univ (1/2)
      (fun rhs => publishWindows (fun w => solve w rhs)
        (generatedWindows s width p u target) (initial rhs))
      (arithmetic+1/(2 : ℝ)^target) := by
  apply SolveSpec.of_published_halos _ _ _ _ _ solve initial
    (generatedWindows_cover width p u target hw) hsolve
  intro w hw x rhs hx hrhs
  obtain ⟨k,_,rfl⟩ := List.mem_map.mp hw
  exact generatedWindow_locality hst hα width p u target k hp hwidth hαu hθ hgap hbudget
    x rhs hx hrhs

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellInterface
