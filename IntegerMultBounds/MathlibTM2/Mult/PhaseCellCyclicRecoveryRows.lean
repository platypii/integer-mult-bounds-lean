module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingCursor
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField

/-! Pair solved joint boundary rows with their original RHS before reversing
replica order. Projection and both retained RHS loaders then agree structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

noncomputable def cyclicBoundaryRecoveryRows (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt)) : List (CyclicRecoveryRow s) :=
  (solutions.zip Fs).reverse.map (fun row => (boundarySolutionField B row.1,(row.2,row.2)))

theorem cyclicBoundaryRecoveryRows_fields (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) :
    (cyclicBoundaryRecoveryRows B solutions Fs).map Prod.fst = solutions.reverse.map (boundarySolutionField B) := by
  have hz : (solutions.zip Fs).reverse.map Prod.fst = solutions.reverse := by
    simpa only [List.map_reverse] using congrArg List.reverse (List.map_fst_zip hlen.le)
  rw [← hz]
  simp only [cyclicBoundaryRecoveryRows,List.map_map,Function.comp_def]

theorem cyclicBoundaryRecoveryRows_rhs (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) :
    (cyclicBoundaryRecoveryRows B solutions Fs).map (fun row => row.2.1) = Fs.reverse ∧
      (cyclicBoundaryRecoveryRows B solutions Fs).map (fun row => row.2.2) = Fs.reverse := by
  have hz : (solutions.zip Fs).reverse.map Prod.snd = Fs.reverse := by
    simpa only [List.map_reverse] using congrArg List.reverse (List.map_snd_zip hlen.ge)
  constructor <;> simpa only [cyclicBoundaryRecoveryRows,List.map_map,Function.comp_def] using hz

theorem cyclicBoundaryRecoveryRows_length (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) :
    (cyclicBoundaryRecoveryRows B solutions Fs).length = Fs.length := by
  have hh := congrArg List.length (cyclicBoundaryRecoveryRows_rhs B solutions Fs hlen).1
  simpa only [List.length_map,List.length_reverse] using hh

theorem cyclicBoundaryRecoveryRows_source (H K : ReplicaHaloProblem s) (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) :
    (cyclicBoundaryRecoveryRows B solutions Fs).flatMap
      (fun row => cyclicRecoveryField (A := A) H row.1++cyclicRecoveryField (A := A) K row.1) =
      solutions.reverse.flatMap (fun solution => cyclicRecoveryField (A := A) H (boundarySolutionField B solution)++
        cyclicRecoveryField (A := A) K (boundarySolutionField B solution)) := by
  have hh := congrArg (fun (xs : List (ZMod s → GaussianInt)) => xs.flatMap (fun C => cyclicRecoveryField (A := A) H C++cyclicRecoveryField (A := A) K C))
    (cyclicBoundaryRecoveryRows_fields B solutions Fs hlen)
  simpa only [List.flatMap_map] using hh

theorem cyclicBoundaryRecoveryRows_rhs_streams (H K : ReplicaHaloProblem s) (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hlen : solutions.length = Fs.length) :
    (cyclicBoundaryRecoveryRows B solutions Fs).flatMap (fun row => cyclicRecoveryField (A := A) H row.2.1) =
        Fs.reverse.flatMap (cyclicRecoveryField (A := A) H) ∧
      (cyclicBoundaryRecoveryRows B solutions Fs).flatMap (fun row => cyclicRecoveryField (A := A) K row.2.2) =
        Fs.reverse.flatMap (cyclicRecoveryField (A := A) K) := by
  obtain ⟨hL,hR⟩ := cyclicBoundaryRecoveryRows_rhs B solutions Fs hlen
  constructor
  · simpa only [List.flatMap_map] using congrArg (fun (xs : List (ZMod s → GaussianInt)) => xs.flatMap (cyclicRecoveryField (A := A) H)) hL
  · simpa only [List.flatMap_map] using congrArg (fun (xs : List (ZMod s → GaussianInt)) => xs.flatMap (cyclicRecoveryField (A := A) K)) hR

theorem cyclicBoundaryRecoveryRows_fits (w : ℕ) (B : Finset (ZMod s))
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hsolutions : ∀ solution ∈ solutions, solution.length = B.card ∧ ∀ z ∈ solution, Fits w z) :
    ∀ row ∈ cyclicBoundaryRecoveryRows B solutions Fs, ∀ j, Fits w (row.1 j) := by
  intro row hr j
  obtain ⟨pair,hpair,rfl⟩ := List.mem_map.mp hr
  have hsol : pair.1 ∈ solutions := (List.of_mem_zip (List.mem_reverse.mp hpair)).1
  exact boundarySolutionField_fits w B pair.1 (hsolutions pair.1 hsol).1 (hsolutions pair.1 hsol).2 j

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
