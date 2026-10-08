import IntegerMultBounds.Networks.Shared50ModularSchedule
import IntegerMultBounds.Networks.ModularProgramShape

/-! Canonical finite control for every modular edge in the actual signed
schedule. A single chosen prime works for every width, and the operation lists
are reductions of fixed rational lists. Counts here concern abstract shear
operations, including whole-matrix transformations, not tape transitions. -/

namespace IntegerMultBounds.Networks.Shared50ModularControl

noncomputable section
open IntegerMultBounds.Swap
open Shear ModularFrameSchedule
open Shared50ModularSchedule (Index pairs extra sourceMatrix sinkMatrix)

private theorem edge_denominator_mem {ι : Type*} [Fintype ι] [LinearOrder ι]
    (es : List (Edge ι)) (extra : Finset (Matrix ι ι ℚ)) {e : Edge ι} (he : e ∈ es)
    {d : ℕ} (hd : d ∈ edgeDenominators e) : d ∈ allDenominators es extra := by
  classical
  exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨e,List.mem_toFinset.mpr he,hd⟩)

private theorem extra_denominator_mem {ι : Type*} [Fintype ι] [LinearOrder ι]
    (es : List (Edge ι)) (extra : Finset (Matrix ι ι ℚ)) {A : Matrix ι ι ℚ}
    (hA : A ∈ extra) {d : ℕ} (hd : d ∈ Modular.denominators A) :
    d ∈ allDenominators es extra := by
  classical
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨A,hA,hd⟩)

/-- The actual ordered matrix edges at the selected parameter. -/
def edges : List (Edge Index) := pairs Shared50GlobalCircuit.enumeration

/-- All denominators needed by the fixed edge factorizations and endpoints. -/
def denominators : Finset ℕ := allDenominators edges extra

/-- An admissible prime is fixed once, independently of the radix width. -/
def prime : ℕ := Classical.choose Shared50ModularSchedule.exists_prime_actual

theorem prime_prime : prime.Prime :=
  (Classical.choose_spec Shared50ModularSchedule.exists_prime_actual).1

theorem prime_odd : 2 < prime :=
  (Classical.choose_spec Shared50ModularSchedule.exists_prime_actual).2.1

theorem prime_bound : ∀ d ∈ denominators, d < prime :=
  (Classical.choose_spec Shared50ModularSchedule.exists_prime_actual).2.2.1

/-- The exact ordered programs; there is no choice depending on the width. -/
def programs (m : ℕ) : List (List (Op Index (ZMod m))) :=
  edges.map (ModularFrameSchedule.program m)

/-- The fixed rational instruction lists from which all widths are generated. -/
def rationalPrograms : List (List (Op Index ℚ)) :=
  edges.map ModularProgramShape.rationalProgram

theorem programs_eq_map (m : ℕ) :
    programs m = rationalPrograms.map (List.map (ModularProgramShape.reduceOp m)) := by
  simp only [programs,rationalPrograms,List.map_map]
  apply List.map_congr_left
  intro e _
  exact ModularProgramShape.program_eq_map m e

-- Avoid unfolding a 125000-coordinate denominator finset in the naming linter.
set_option linter.constructorNameAsVariable false in
theorem edge_bound {q : ℕ} (hd : ∀ d ∈ denominators, d < q)
    {e : Edge Index} (he : e ∈ edges) : ∀ d ∈ edgeDenominators e, d < q := by
  classical
  intro d hde
  apply hd d
  change d ∈ allDenominators edges extra
  apply edge_denominator_mem edges extra (e := e) (d := d)
  · exact he
  · assumption

/-- Supplied primes and widths select these same canonical lists. -/
theorem edge_specs {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ denominators, d < q) (b : ℕ) :
    List.Forall₂ (EdgeSpec (q ^ b)) edges (programs (q ^ b)) := by
  rw [programs,List.forall₂_map_right_iff,List.forall₂_same]
  intro e he
  exact program_spec e hq (edge_bound hd he) b

theorem chosen_edge_specs (b : ℕ) :
    List.Forall₂ (EdgeSpec (prime ^ b)) edges (programs (prime ^ b)) :=
  edge_specs prime_prime prime_bound b

set_option linter.constructorNameAsVariable false in
theorem extra_admissible {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ denominators, d < q)
    (b : ℕ) {A : Shared50ModularSchedule.Mat} (hA : A ∈ extra) :
    Modular.Admissible (q ^ b) A := by
  classical
  apply Modular.admissible_of_lt hq _ b
  intro d hdA
  apply hd d
  change d ∈ allDenominators edges extra
  apply extra_denominator_mem edges extra (A := A) (d := d)
  · exact hA
  · assumption

theorem source_admissible {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ denominators, d < q)
    (b : ℕ) (i : Shared50GlobalBudget.World) : Modular.Admissible (q ^ b) (sourceMatrix i) :=
  extra_admissible hq hd b (Shared50ModularSchedule.sourceMatrix_mem i)

theorem sink_admissible {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ denominators, d < q)
    (b : ℕ) (i : Shared50GlobalBudget.World) : Modular.Admissible (q ^ b) (sinkMatrix i) :=
  extra_admissible hq hd b (Shared50ModularSchedule.sinkMatrix_mem i)

theorem endpoint {q : ℕ} (hq : q.Prime) (hd : ∀ d ∈ denominators, d < q)
    (b : ℕ) (i : Shared50GlobalBudget.World) :
    Modular.reduce (q ^ b) (sinkMatrix i) -
      Modular.reduce (q ^ b) (sourceMatrix (Shared50ShearEndpoints.route i)) = 1 :=
  Shared50ModularSchedule.reduced_endpoint _ (source_admissible hq hd b) (sink_admissible hq hd b) i

theorem chosen_endpoint (b : ℕ) (i : Shared50GlobalBudget.World) :
    Modular.reduce (prime ^ b) (sinkMatrix i) -
      Modular.reduce (prime ^ b) (sourceMatrix (Shared50ShearEndpoints.route i)) = 1 :=
  endpoint prime_prime prime_bound b i

/-- The exact pivot budget is independent even of modulus admissibility. -/
theorem interchanges_exact (m : ℕ) :
    ((programs m).map interchanges).sum = Shared50Parameters.s := by
  simp only [programs,List.map_map,Function.comp_def,ModularProgramShape.program_interchanges]
  exact Shared50ModularSchedule.rankSum50

/-- Exact abstract operation count; a matrix transformation is one list entry. -/
theorem operation_count (m : ℕ) :
    ((programs m).map List.length).sum = 3 * Shared50Parameters.s + 4 * edges.length := by
  have hh := ModularProgramShape.schedule_length m edges
  change ((programs m).map List.length).sum =
    3 * ((programs m).map interchanges).sum + 4 * edges.length at hh
  rw [interchanges_exact] at hh
  exact hh

/-- Only whole-group transformations need a triangularity certificate. -/
def TriangularOp {ι R : Type*} [LinearOrder ι] [CommRing R] : Op ι R → Prop
  | .transformH E => LowerTriangular E
  | .transformD E => LowerTriangular E
  | _ => True

private theorem pivots_triangular {ι R : Type*} [LinearOrder ι] [CommRing R]
    (L : List (ι × ι)) : ∀ op ∈ pivotsProgram (R := R) L, TriangularOp op := by
  induction L with
  | nil => simp [pivotsProgram]
  | cons p rest ih =>
    simpa [pivotsProgram,pivotProgram,TriangularOp] using ih

/-- Every transformation in the concrete generated program is lower triangular. -/
theorem program_triangular (m : ℕ) (e : Edge Index) :
    ∀ op ∈ ModularFrameSchedule.program m e, TriangularOp op := by
  have h₁ := Modular.reduce_lowerTriangular m (factors e).lower₁
  have h₁' := Modular.reduce_lowerTriangular m (factors e).lower₁'
  have h₂ := Modular.reduce_lowerTriangular m (factors e).lower₂
  have h₂' := Modular.reduce_lowerTriangular m (factors e).lower₂'
  intro op hop
  simp only [ModularFrameSchedule.program,shearProgram,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false] at hop
  rcases hop with (h | h) | h
  · rcases h with rfl | rfl
    · exact h₂
    · exact h₁'
  · exact pivots_triangular _ op h
  · rcases h with rfl | rfl
    · exact h₁
    · exact h₂'

theorem programs_triangular (m : ℕ) :
    ∀ p ∈ programs m, ∀ op ∈ p, TriangularOp op := by
  intro p hp
  obtain ⟨e,_,rfl⟩ := List.mem_map.mp hp
  exact program_triangular m e

end
end IntegerMultBounds.Networks.Shared50ModularControl
