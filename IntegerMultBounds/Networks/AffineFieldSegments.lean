import IntegerMultBounds.Networks.AffineFieldCoordinates

/-! Separate maximal nonrecursive runs from explicit recursive interchange
boundaries, retaining the complete original field program in order. Empty runs
are allowed at the ends and between adjacent recursive operations. -/
namespace IntegerMultBounds.Networks.AffineFieldSegments
open AffineFieldProgram AffineFieldCoordinates
variable {d : ℕ} {R : Type*}

inductive Segments (d : ℕ) (R : Type*) where
  | done : List (Op (Fin d) R) → Segments d R
  | boundary : List (Op (Fin d) R) → Fin d → Fin d → Segments d R → Segments d R

def flatten : Segments d R → List (Op (Fin d) R)
  | .done ops => ops
  | .boundary ops i j tail => ops ++ .interchange i j :: flatten tail

def runs : Segments d R → List (List (Op (Fin d) R))
  | .done ops => [ops]
  | .boundary ops _ _ tail => ops :: runs tail

def prepend (op : Op (Fin d) R) : Segments d R → Segments d R
  | .done ops => .done (op :: ops)
  | .boundary ops i j tail => .boundary (op :: ops) i j tail

/-- Every interchange is retained as a boundary; only the other operations are
coalesced into the preceding nonrecursive run. -/
def split : List (Op (Fin d) R) → Segments d R
  | [] => .done []
  | .interchange i j :: ops => .boundary [] i j (split ops)
  | op :: ops => prepend op (split ops)

@[simp] theorem flatten_prepend (op : Op (Fin d) R) (s : Segments d R) :
    flatten (prepend op s) = op :: flatten s := by
  cases s <;> rfl

/-- Splitting neither omits nor reorders any operation. -/
@[simp] theorem flatten_split (ops : List (Op (Fin d) R)) : flatten (split ops) = ops := by
  induction ops with
  | nil => rfl
  | cons op ops ih => cases op <;> simp [split,flatten,ih]

def NonrecursiveRuns (s : Segments d R) : Prop :=
  ∀ ops ∈ runs s, ∀ op ∈ ops, Nonrecursive op

private theorem prepend_nonrecursive (op : Op (Fin d) R) (h : Nonrecursive op)
    (s : Segments d R) (hs : NonrecursiveRuns s) : NonrecursiveRuns (prepend op s) := by
  cases s with
  | done ops =>
    intro run hr x hx
    simp only [prepend,runs,List.mem_singleton] at hr
    subst run
    rcases List.mem_cons.mp hx with rfl | hx
    · exact h
    · exact hs ops (by simp [runs]) x hx
  | boundary ops i j tail =>
    intro run hr x hx
    simp only [prepend,runs,List.mem_cons] at hr
    rcases hr with rfl | hr
    · rcases List.mem_cons.mp hx with rfl | hx
      · exact h
      · exact hs ops (by simp [runs]) x hx
    · exact hs run (by simp only [runs,List.mem_cons]; exact Or.inr hr) x hx

theorem split_nonrecursive (ops : List (Op (Fin d) R)) : NonrecursiveRuns (split ops) := by
  induction ops with
  | nil => simp [NonrecursiveRuns,split,runs]
  | cons op ops ih =>
    cases op with
    | interchange i j =>
      intro run hr x hx
      simp only [split,runs,List.mem_cons] at hr
      rcases hr with rfl | hr
      · exact (List.not_mem_nil hx).elim
      · exact ih run hr x hx
    | affineH op => exact prepend_nonrecursive (.affineH op) trivial _ ih
    | affineD op => exact prepend_nonrecursive (.affineD op) trivial _ ih
    | addToD i j => exact prepend_nonrecursive (.addToD i j) trivial _ ih
    | subFromD i j => exact prepend_nonrecursive (.subFromD i j) trivial _ ih

theorem run_member (s : Segments d R) (ops : List (Op (Fin d) R)) (hs : ops ∈ runs s)
    (op : Op (Fin d) R) (hop : op ∈ ops) : op ∈ flatten s := by
  induction s with
  | done xs =>
    simp only [runs,List.mem_singleton] at hs
    subst ops
    exact hop
  | boundary xs i j tail ih =>
    simp only [runs,List.mem_cons] at hs
    rcases hs with rfl | hs
    · exact List.mem_append_left _ hop
    · exact List.mem_append_right _ (List.mem_cons_of_mem _ (ih hs))

/-- Each extracted run has precisely the hypotheses required by the physical
nonrecursive segment compiler when the original list is an actual schedule. -/
theorem split_run_spec (p ops : List (Op (Fin d) R)) (hs : ops ∈ runs (split p)) :
    (∀ op ∈ ops, op ∈ p) ∧ (∀ op ∈ ops, Nonrecursive op) := by
  constructor
  · intro op hop
    simpa only [flatten_split] using run_member (split p) ops hs op hop
  · exact split_nonrecursive p ops hs

/-- Running the reconstructed program retains recursive interchange semantics. -/
theorem run_split [CommRing R] (p : List (Op (Fin d) R)) (s : Swap.Shear.State (Fin d) R) :
    AffineFieldProgram.run (flatten (split p)) s = AffineFieldProgram.run p s := by
  rw [flatten_split]

/-- Count literal recursive boundaries, independently of nonrecursive runs. -/
def recursiveCalls : Segments d R → ℕ
  | .done _ => 0
  | .boundary _ _ _ tail => recursiveCalls tail + 1

theorem recursiveCalls_prepend (op : Op (Fin d) R) (s : Segments d R) :
    recursiveCalls (prepend op s) = recursiveCalls s := by cases s <;> rfl

/-- Segmentation preserves the exact recursive-call count used in recurrences. -/
theorem split_recursiveCalls (p : List (Op (Fin d) R)) :
    recursiveCalls (split p) = AffineFieldProgram.interchanges p := by
  induction p with
  | nil => rfl
  | cons op p ih =>
    cases op <;> simp [split,recursiveCalls,recursiveCalls_prepend,ih,
      AffineFieldProgram.interchanges,AffineFieldProgram.isInterchange]
    rfl

/-- Include empty boundary runs, so every join is visible to later assembly. -/
theorem runs_length (s : Segments d R) : (runs s).length = recursiveCalls s + 1 := by
  induction s with
  | done ops => rfl
  | boundary ops i j tail ih => simp only [runs,List.length_cons,ih,recursiveCalls]

end IntegerMultBounds.Networks.AffineFieldSegments
