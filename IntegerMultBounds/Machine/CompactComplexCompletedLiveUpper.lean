import IntegerMultBounds.Machine.CompactComplexCompletedLiveLower

/-! The true denominator at every event prefix stays inside its counted ledger.
This complements the completed lower bound needed for exact nonleaf return.
Local scalar/child endpoint equalities remain execution obligations. -/
namespace IntegerMultBounds.Machine.CompactComplexCompletedLiveUpper
noncomputable section
open CompactComplexCompletedLiveLower
open CompactComplexScalarIntegerRows (GroupIndex RowIndex)
open CompactComplexScalarSegmentRows (block)
open CompactComplexRecursiveGeometry (arity)
open CompactComplexDenominatorCapacity (ledger scalarRows)
open CompactComplexRecursiveLiveProgress (Live Progress)
attribute [local irreducible] Networks.ComplexRank25.program
  CompactComplexScalarIntegerRows.gates Networks.ComplexFramedExecution.rows
  block

def childIncrement (stopped : Bool) (k : ℕ) :=
  if stopped then arity^k else 2*arity^k

theorem child_target_exact (stopped : Bool) (n k : ℕ) :
    childTarget stopped n k=n+childIncrement stopped k := by
  cases stopped <;> rfl

theorem child_increment_le (stopped : Bool) (k : ℕ) :
    childIncrement stopped k≤2*arity^k := by
  cases stopped <;> simp only [childIncrement,Bool.false_eq_true,ite_false,ite_true] <;> omega

private theorem completedWith_exact (rows : GroupIndex → List RowIndex) (gap : ℕ)
    (es : List Event) (n : ℕ) :
    completedWith rows (fun m => m+gap) es n=
      n+(scalarNamesWith rows es).length+(childNames es).length*gap := by
  induction es generalizing n with
  | nil => simp only [completedWith,scalarNamesWith,childNames,List.length_nil,
      Nat.add_zero,Nat.zero_mul]
  | cons e es ih =>
    cases e with
    | scalar g =>
      simp only [completedWith,scalarNamesWith,childNames,List.length_append,ih]
      omega
    | child c =>
      simp only [completedWith,scalarNamesWith,childNames,List.length_cons,ih,Nat.add_mul,Nat.one_mul]
      omega

/-- Exact prefix denominator from real row and child counts. -/
theorem completed_exact (stopped : Bool) (k : ℕ) (es : List Event) (n : ℕ) :
    completed stopped k es n=
      n+(scalarNames es).length+(childNames es).length*childIncrement stopped k := by
  have ht : (fun m => childTarget stopped m k)=(fun m => m+childIncrement stopped k) :=
    funext (fun m => child_target_exact stopped m k)
  unfold completed
  rw [ht]
  exact completedWith_exact block _ es n

/-- Both stopped and normalized nonleaf policies are covered by twice the
actual child volume; this holds at any prefix, not only node completion. -/
theorem completed_upper (stopped : Bool) (k : ℕ) (es : List Event) (n : ℕ) :
    completed stopped k es n≤
      n+(scalarNames es).length+2*((childNames es).length*arity^k) := by
  rw [completed_exact]
  have h := Nat.mul_le_mul_left (childNames es).length (child_increment_le stopped k)
  nlinarith

/-- The full actual schedule is bounded by its original scalar count and
literal call multiplicity, each paying at most twice the child volume. -/
theorem actual_completed_upper (d k n : ℕ) :
    completed (Networks.ComplexRecursiveCallSchema.stopped d k) k schedule n≤
      n+Networks.ComplexFramedExecution.rows.length+
        2*(Networks.ComplexRecursiveCallSchema.calls.length*arity^k) := by
  have h := completed_upper (Networks.ComplexRecursiveCallSchema.stopped d k) k schedule n
  rw [schedule_scalar_count,schedule_calls] at h
  exact h

private theorem names_lengths_append (rows : GroupIndex → List RowIndex)
    (xs ys : List Event) :
    (scalarNamesWith rows (xs++ys)).length=
      (scalarNamesWith rows xs).length+(scalarNamesWith rows ys).length ∧
    (childNames (xs++ys)).length=(childNames xs).length+(childNames ys).length := by
  induction xs with
  | nil => simp only [List.nil_append,scalarNamesWith,childNames,List.length_nil,Nat.zero_add,and_self]
  | cons e xs ih =>
    cases e with
    | scalar g =>
      simp only [List.cons_append,scalarNamesWith,childNames,List.length_append,ih.1,ih.2]
      exact ⟨by omega,by trivial⟩
    | child c =>
      simp only [List.cons_append,scalarNamesWith,childNames,List.length_cons,ih.1,ih.2]
      exact ⟨by trivial,by omega⟩

private theorem names_lengths_take_le (rows : GroupIndex → List RowIndex)
    (es : List Event) (j : ℕ) :
    (scalarNamesWith rows (es.take j)).length≤(scalarNamesWith rows es).length ∧
    (childNames (es.take j)).length≤(childNames es).length := by
  have h := names_lengths_append rows (es.take j) (es.drop j)
  rw [List.take_append_drop] at h
  exact ⟨by omega,by omega⟩

/-- Every physical event prefix counts at most the actual full node's scalar
rows and original child occurrences; no finite network is enumerated. -/
theorem actual_prefix_counts (j : ℕ) :
    (scalarNames (schedule.take j)).length≤scalarRows ∧
    (childNames (schedule.take j)).length≤Networks.ComplexRecursiveCallSchema.calls.length := by
  have h := names_lengths_take_le block schedule j
  change (scalarNames (schedule.take j)).length≤(scalarNames schedule).length ∧
    (childNames (schedule.take j)).length≤(childNames schedule).length at h
  rw [schedule_scalar_count,schedule_calls] at h
  exact h

/-- A node prefix propagates the inherited upper ledger with its genuine
completed scalar and child counters. No whole-node upper bound is assumed. -/
theorem completed_ledger (stopped : Bool) (k : ℕ) (es : List Event)
    (baseline levels frames returned usedRows n : ℕ)
    (h : n≤ledger scalarRows baseline levels frames returned usedRows) :
    completed stopped k es n≤ledger scalarRows baseline levels frames
      (returned+(childNames es).length*arity^k) (usedRows+(scalarNames es).length) := by
  have hc := completed_upper stopped k es n
  unfold ledger at *
  omega

universe u
/-- Local endpoint exponent equalities and a literal Live invariant produce
physical upper-ledger progress for every compiled event prefix. -/
theorem runEvents_progress {X : Type u} {t : ℕ}
    (common : X → Tapes t 2) (slot : Fin t) (next : Event → X → X)
    (exponent : X → ℕ) (stopped : Bool) (k : ℕ)
    (hs : ∀ g x,exponent (next (.scalar g) x)=exponent x+(block g).length)
    (hc : ∀ c x,exponent (next (.child c) x)=childTarget stopped (exponent x) k)
    (hlive : ∀ x,Live (common x) slot (exponent x))
    (baseline levels frames returned usedRows : ℕ) (es : List Event) (x : X)
    (h : exponent x≤ledger scalarRows baseline levels frames returned usedRows) :
    Progress (common (runEvents next es x)) slot baseline levels frames
      (returned+(childNames es).length*arity^k) (usedRows+(scalarNames es).length) := by
  refine ⟨exponent (runEvents next es x),hlive _,?_⟩
  exact (runEvents_exponent next exponent stopped k hs hc es x).trans_le
    (completed_ledger stopped k es baseline levels frames returned usedRows _ h)

end
end IntegerMultBounds.Machine.CompactComplexCompletedLiveUpper
