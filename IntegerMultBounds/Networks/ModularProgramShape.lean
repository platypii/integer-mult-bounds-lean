import IntegerMultBounds.Networks.ModularFrameSchedule

/-! A fixed rational instruction list generates each modular edge program.
Only coefficient reduction depends on the modulus: operation order, pivots,
program length and interchange count are all fixed before choosing the width.
These are field-operation counts, not tape-transition costs. -/

namespace IntegerMultBounds.Networks.ModularProgramShape

noncomputable section
open IntegerMultBounds.Swap
open Shear ModularFrameSchedule

variable {ι : Type*} [Fintype ι] [LinearOrder ι]

/-- Specialize fixed rational coefficients without changing operation kinds. -/
def reduceOp (m : ℕ) : Op ι ℚ → Op ι (ZMod m)
  | .addToD i j => .addToD i j
  | .subFromD i j => .subFromD i j
  | .interchange i j => .interchange i j
  | .transformH E => .transformH (Modular.reduce m E)
  | .transformD E => .transformD (Modular.reduce m E)

/-- Fix the entire instruction list, including rational factors and pivots. -/
def rationalProgram (e : Edge ι) : List (Op ι ℚ) :=
  shearProgram (factors e).E₁ (factors e).E₁' (factors e).E₂ (factors e).E₂' (factors e).L

omit [Fintype ι] [LinearOrder ι] in
private theorem map_pivots (m : ℕ) (L : List (ι × ι)) :
    (pivotsProgram (R := ℚ) L).map (reduceOp m) = pivotsProgram L := by
  induction L with
  | nil => rfl
  | cons p rest ih =>
    simp only [pivotsProgram,List.map_append,pivotProgram,List.map_cons,List.map_nil,reduceOp,ih]

theorem program_eq_map (m : ℕ) (e : Edge ι) :
    ModularFrameSchedule.program m e = (rationalProgram e).map (reduceOp m) := by
  simp only [ModularFrameSchedule.program,rationalProgram,shearProgram,List.map_append,
    List.map_cons,List.map_nil,reduceOp,map_pivots]

omit [Fintype ι] [LinearOrder ι] in
private theorem pivots_length {R : Type*} (L : List (ι × ι)) :
    (pivotsProgram (R := R) L).length = 3 * L.length := by
  induction L with
  | nil => rfl
  | cons p rest ih =>
    simp only [pivotsProgram,List.length_append,pivotProgram,List.length_cons,List.length_nil,ih]
    omega

omit [Fintype ι] [LinearOrder ι] in
private theorem shear_length {R : Type*} (E₁ E₁' E₂ E₂' : Matrix ι ι R) (L : List (ι × ι)) :
    (shearProgram E₁ E₁' E₂ E₂' L).length = 3 * L.length + 4 := by
  simp only [shearProgram,List.length_append,List.length_cons,List.length_nil,pivots_length]
  omega

theorem rationalProgram_length (e : Edge ι) : (rationalProgram e).length = 3 * (e.2 - e.1).rank + 4 := by
  rw [rationalProgram,shear_length,PivotRank.length_eq_rank]

theorem program_length (m : ℕ) (e : Edge ι) :
    (ModularFrameSchedule.program m e).length = 3 * (e.2 - e.1).rank + 4 := by
  rw [program_eq_map,List.length_map,rationalProgram_length]

/-- Interchange count is independent of the modulus, even before admissibility
is used to prove that the generated program computes its specified shear. -/
theorem program_interchanges (m : ℕ) (e : Edge ι) :
    interchanges (ModularFrameSchedule.program m e) = (e.2 - e.1).rank := by
  rw [ModularFrameSchedule.program,shearProgram_interchanges,PivotRank.length_eq_rank]

/-- Total field operations in the fixed ordered schedule, including rank-zero edges. -/
theorem schedule_length (m : ℕ) (es : List (Edge ι)) :
    ((es.map (ModularFrameSchedule.program m)).map List.length).sum =
      3 * ((es.map (ModularFrameSchedule.program m)).map interchanges).sum + 4 * es.length := by
  induction es with
  | nil => rfl
  | cons e es ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,program_length,program_interchanges]
    rw [ih]
    omega

end
end IntegerMultBounds.Networks.ModularProgramShape
