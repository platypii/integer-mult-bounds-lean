import IntegerMultBounds.Machine.CompactComplexRecursiveLiveProgress
import IntegerMultBounds.Machine.CompactComplexScalarSegmentRows

/-! The actual named group/call schedule counts completed physical denominator
advances. Header folds here are projections of completed scalar/child endpoints,
not a replacement for coefficient execution or its still-open recursive proof. -/
namespace IntegerMultBounds.Machine.CompactComplexCompletedLiveLower
noncomputable section
open Networks
open CompactComplexRecursiveGeometry (arity)
open CompactComplexScalarIntegerRows (GroupIndex RowIndex gates)
open CompactComplexScalarSegmentRows (block)
open CompactComplexRecursiveLiveProgress (Live liveSlot)
open RecursiveChildQuotientsConstant (bits)
attribute [local irreducible] ComplexRank25.program ComplexFramedExecution.rows
  ComplexRecursiveCallSchema.calls CompactRecursiveDependencyBudget.siteDimensions
  CompactComplexScalarIntegerRows.gates block

/-- Named scalar completion follows the alignment of this original group. -/
inductive Event where
  | scalar (group : GroupIndex)
  | child (call : ComplexRecursiveCallSchema.Call)

def groups : List GroupIndex := List.ofFn id

/-- True label-update incidence boundary in the original group compiler. -/
def siteBoundary (g : ℕ) := (GroupedFrames.updates (ComplexRank25.program.take g)).length

/-- Actual residual-coordinate calls in this group's own alignment interval. -/
def groupCalls (g : GroupIndex) :=
  ((CompactRecursiveDependencyBudget.siteDimensions.drop (siteBoundary g.val)).take
    (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length).sum

attribute [local irreducible] siteBoundary groupCalls

/-- The source of these boundaries is literally the original global trace. -/
theorem actual_update_schedule : ComplexPhaseBudget.updates=
    GroupedFrames.networkUpdates ComplexRank25.wires
      (GlobalLabels.sink (Labels.binary 25) ComplexRank25.vector) ComplexRank25.program := by
  unfold ComplexPhaseBudget.updates GlobalProjectionRank.trace ComplexRank25.program
  rfl

theorem siteBoundary_step (g : GroupIndex) :
    siteBoundary (g.val+1)=siteBoundary g.val+
      (GroupedFrames.touches (CompactFramedScalarGrid.vertex g)).length := by
  unfold siteBoundary GroupedFrames.updates
  rw [List.take_succ_eq_append_getElem g.isLt,List.flatMap_append]
  simp only [List.flatMap_singleton,List.length_append,CompactFramedScalarGrid.vertex]

def callBoundary (g : ℕ) := (CompactRecursiveDependencyBudget.siteDimensions.take (siteBoundary g)).sum

/-- A group's own alignment calls are exactly the difference between its
actual residual-coordinate prefix boundaries. -/
theorem groupCalls_prefix (g : GroupIndex) :
    callBoundary g.val+groupCalls g=callBoundary (g.val+1) := by
  unfold callBoundary groupCalls
  rw [siteBoundary_step,List.take_add,List.sum_append]

theorem siteBoundary_le (g : ℕ) : siteBoundary g≤ComplexRecursiveCallSchema.sites.length := by
  have hs := congrArg (fun vs => (GroupedFrames.updates vs).length)
    (List.take_append_drop g ComplexRank25.program)
  simp only [GroupedFrames.updates,List.flatMap_append,List.length_append] at hs
  have ht := congrArg List.length actual_update_schedule
  simp only [GroupedFrames.networkUpdates,GroupedFrames.updates,List.length_append,List.length_map] at ht
  have he : ComplexRecursiveCallSchema.sites.length=ComplexPhaseBudget.updates.length := by
    simp only [ComplexRecursiveCallSchema.sites,List.length_attach,ComplexRecursiveCallSchema.edge_length]
  unfold siteBoundary GroupedFrames.updates
  omega

theorem callBoundary_le (g : ℕ) : callBoundary g≤ComplexRecursiveCallSchema.calls.length := by
  have hs := List.sum_take_add_sum_drop CompactRecursiveDependencyBudget.siteDimensions (siteBoundary g)
  have ht := CompactRecursiveDependencyBudget.siteDimensions_sum
  unfold callBoundary
  omega

def callInterval (g : GroupIndex) :=
  (ComplexRecursiveCallSchema.calls.drop (callBoundary g.val)).take (groupCalls g)

theorem callBoundary_zero : callBoundary 0=0 := by
  simp only [callBoundary,siteBoundary,List.take_zero,GroupedFrames.updates,List.flatMap_nil,
    List.length_nil,List.sum_nil]

/-- The group interval contains its exact residual-coordinate count; it is
never silently truncated by the end of the actual call list. -/
theorem callInterval_length (g : GroupIndex) : (callInterval g).length=groupCalls g := by
  have h := callBoundary_le (g.val+1)
  rw [←groupCalls_prefix] at h
  unfold callInterval
  rw [List.length_take,List.length_drop]
  omega

/-- Advancing this exact interval reaches the next original group boundary. -/
theorem callInterval_next (g : GroupIndex) :
    (ComplexRecursiveCallSchema.calls.drop (callBoundary g.val)).drop (groupCalls g)=
      ComplexRecursiveCallSchema.calls.drop (callBoundary (g.val+1)) := by
  rw [List.drop_drop,groupCalls_prefix]

/-- Consume the actual calls site-major, align each group before its scalar
block, and retain all remaining sink-incidence calls in their original order. -/
def assembleWith (count : GroupIndex → ℕ) : List GroupIndex → List ComplexRecursiveCallSchema.Call → List Event
  | [],cs => cs.map Event.child
  | g::gs,cs => (cs.take (count g)).map Event.child++
      Event.scalar g::assembleWith count gs (cs.drop (count g))

def assemble := assembleWith groupCalls
def schedule := assemble groups ComplexRecursiveCallSchema.calls
attribute [local irreducible] groups schedule

def scalarNamesWith (rows : GroupIndex → List RowIndex) : List Event → List RowIndex
  | [] => []
  | Event.scalar g::es => rows g++scalarNamesWith rows es
  | Event.child _::es => scalarNamesWith rows es

def scalarNames := scalarNamesWith block

def childNames : List Event → List ComplexRecursiveCallSchema.Call
  | [] => []
  | Event.scalar _::es => childNames es
  | Event.child c::es => c::childNames es

private theorem names_append (rows : GroupIndex → List RowIndex) (xs ys : List Event) :
    scalarNamesWith rows (xs++ys)=scalarNamesWith rows xs++scalarNamesWith rows ys ∧
    childNames (xs++ys)=childNames xs++childNames ys := by
  induction xs with
  | nil => exact ⟨rfl,rfl⟩
  | cons e es ih =>
    cases e with
    | scalar g => exact ⟨(congrArg (fun zs => rows g++zs) ih.1).trans (List.append_assoc _ _ _).symm,ih.2⟩
    | child c => exact ⟨ih.1,congrArg (List.cons c) ih.2⟩

private theorem names_child_map (rows : GroupIndex → List RowIndex)
    (cs : List ComplexRecursiveCallSchema.Call) :
    scalarNamesWith rows (cs.map Event.child)=[] ∧ childNames (cs.map Event.child)=cs := by
  induction cs with
  | nil => exact ⟨rfl,rfl⟩
  | cons c cs ih => exact ⟨ih.1,congrArg (List.cons c) ih.2⟩

private theorem assembleWith_names (count : GroupIndex → ℕ) (rows : GroupIndex → List RowIndex)
    (gs : List GroupIndex) (cs : List ComplexRecursiveCallSchema.Call) :
    scalarNamesWith rows (assembleWith count gs cs)=gs.flatMap rows ∧
    childNames (assembleWith count gs cs)=cs := by
  induction gs generalizing cs with
  | nil => exact names_child_map rows cs
  | cons g gs ih =>
    have hp := names_child_map rows (cs.take (count g))
    have ht := ih (cs.drop (count g))
    have ha := names_append rows ((cs.take (count g)).map Event.child)
      (Event.scalar g::assembleWith count gs (cs.drop (count g)))
    constructor
    · exact ha.1.trans ((congrArg₂ List.append hp.1
        (congrArg (fun zs => rows g++zs) ht.1)).trans rfl)
    · exact ha.2.trans ((congrArg₂ List.append hp.2 ht.2).trans (List.take_append_drop _ _))

/-- Every real call is preserved once, regardless of equal role labels. -/
theorem assemble_names (gs : List GroupIndex) (cs : List ComplexRecursiveCallSchema.Call) :
    scalarNames (assemble gs cs)=gs.flatMap block ∧ childNames (assemble gs cs)=cs :=
  assembleWith_names groupCalls block gs cs

theorem schedule_calls : childNames schedule=ComplexRecursiveCallSchema.calls :=
  by unfold schedule; exact (assemble_names groups ComplexRecursiveCallSchema.calls).2

theorem schedule_scalars : scalarNames schedule=groups.flatMap block :=
  by unfold schedule; exact (assemble_names groups ComplexRecursiveCallSchema.calls).1

private theorem indexed_rows_length {α : Type*} {n : ℕ} (rows : Fin n → List α) :
    ((List.ofFn id).flatMap rows).length=(List.ofFn (fun i => (rows i).length)).sum := by
  rw [List.length_flatMap,List.map_ofFn]
  rfl

/-- The named scalar blocks retain the genuine complete finite row count. -/
theorem named_rows_length : (groups.flatMap block).length=ComplexFramedExecution.rows.length := by
  have he : (fun g => (block g).length)=(fun g => (gates g).length) :=
    funext CompactComplexScalarSegmentRows.block_length
  have h := List.ofFn_getElem_eq_map ComplexRank25.program
    (fun v => (GroupedCircuit.compile v.group).length)
  calc
    _ = (List.ofFn (fun g => (block g).length)).sum := by
      unfold groups
      exact indexed_rows_length block
    _ = (List.ofFn (fun g => (gates g).length)).sum := congrArg (fun f => (List.ofFn f).sum) he
    _ = (ComplexRank25.program.map (fun v => (GroupedCircuit.compile v.group).length)).sum :=
      by simpa only [gates,CompactFramedScalarGrid.vertex] using congrArg List.sum h
    _ = ComplexFramedExecution.rows.length := by
      unfold ComplexFramedExecution.rows GroupedCircuit.compileGroups
      rw [List.length_flatMap,List.map_map]
      rfl

theorem schedule_scalar_count : (scalarNames schedule).length=ComplexFramedExecution.rows.length := by
  rw [schedule_scalars,named_rows_length]

/-- Both actual leaf and normalized nonleaf return policies give at least
one complete child-volume advance. -/
def childTarget (stopped : Bool) (n k : ℕ) :=
  if stopped then CompactComplexDenominatorPolicy.leafTarget n k else n+2*arity^k

theorem child_target_lower (stopped : Bool) (n k : ℕ) : n+arity^k≤childTarget stopped n k := by
  cases stopped <;> simp only [childTarget,Bool.false_eq_true,ite_false,ite_true,
    CompactComplexDenominatorPolicy.leafTarget] <;> omega

theorem child_target_nonleaf (n k : ℕ) :
    childTarget false n (k+1)=CompactComplexDenominatorPolicy.networkTarget n k := rfl

variable {s : ℕ}

/-- The actual scalar-array lifecycle endpoint has exactly one real live-word
increment per row in this original named group. -/
theorem scalar_completed_live {N : ℕ} (hs : 7<s) (header : Fin s) (hh : header.val≠7)
    (g : GroupIndex) (v : Tapes (CompactComplexScalarCountLifecycle.publicTapes s) 2)
    (data : Fin CompactComplexScalarRowBlock.wireCount → Fin N → ButterflyStreamData.Coefficient)
    (n : ℕ) :
    Live (CompactComplexScalarCountLifecycle.output hs header v
      (CompactComplexScalarPolynomialSequence.execute (block g) data) (n+(block g).length))
      (liveSlot hs) (n+(block g).length) :=
  CompactComplexRecursiveLiveProgress.scalar_output_live hs header hh _ _ _

/-- Both real child policies install a word at least one child volume beyond
entry. The endpoint is the actual stopped/nonleaf commit storage transform. -/
theorem child_completed_live (storage : Tapes (10+s) 2) (stopped : Bool) (n k : ℕ) :
    Live (CompactComplexStoppedAlignedCall.committed storage (childTarget stopped n k))
      ⟨7,by omega⟩ (childTarget stopped n k) ∧ n+arity^k≤childTarget stopped n k :=
  ⟨CompactComplexRecursiveLiveProgress.committed_live storage _,child_target_lower stopped n k⟩

def advance (stopped : Bool) (k n : ℕ) : Event → ℕ
  | .scalar g => n+(block g).length
  | .child _ => childTarget stopped n k

/-- Compute only the true header projection of these completed endpoints. -/
def completedWith (rows : GroupIndex → List RowIndex) (target : ℕ → ℕ) : List Event → ℕ → ℕ
  | [],n => n
  | Event.scalar g::es,n => completedWith rows target es (n+(rows g).length)
  | Event.child _::es,n => completedWith rows target es (target n)

def completed (stopped : Bool) (k : ℕ) := completedWith block (fun n => childTarget stopped n k)

private theorem completedWith_lower (rows : GroupIndex → List RowIndex) (target : ℕ → ℕ)
    (width : ℕ) (ht : ∀ n,n+width≤target n) (es : List Event) (n : ℕ) :
    n+(scalarNamesWith rows es).length+(childNames es).length*width≤completedWith rows target es n := by
  induction es generalizing n with
  | nil => simp only [scalarNamesWith,childNames,List.length_nil,completedWith,Nat.add_zero,Nat.zero_mul]
           exact le_rfl
  | cons e es ih =>
    cases e with
    | scalar g =>
      have h := ih (n+(rows g).length)
      simpa only [scalarNamesWith,childNames,List.length_append,completedWith,
        Nat.add_assoc,Nat.add_comm,Nat.add_left_comm] using h
    | child c =>
      have h := ih (target n)
      have hstep := ht n
      simp only [scalarNamesWith,childNames,List.length_cons,completedWith] at *
      rw [Nat.add_mul,Nat.one_mul]
      omega

/-- Induction over real named events derives the entire completed-count lower
bound. No completed-count inequality is an input to this theorem. -/
theorem completed_lower (stopped : Bool) (k : ℕ) (es : List Event) (n : ℕ) :
    n+(scalarNames es).length+(childNames es).length*arity^k≤completed stopped k es n :=
  completedWith_lower block (fun n => childTarget stopped n k) (arity^k)
    (fun n => child_target_lower stopped n k) es n

/-- The actual named group/call schedule covers the minimum exponent in the
nonleaf denominator policy. -/
theorem actual_completed_lower (d k n : ℕ) :
    CompactComplexDenominatorPolicy.minimumCompletedExponent n k≤
      completed (ComplexRecursiveCallSchema.stopped d k) k schedule n := by
  have h := completed_lower (ComplexRecursiveCallSchema.stopped d k) k schedule n
  simpa only [schedule_scalar_count,schedule_calls,
    CompactComplexDenominatorPolicy.minimumCompletedExponent] using h

/-- The real target is covered by the actual counted completed endpoints. -/
theorem actual_network_target (d k n : ℕ) :
    CompactComplexDenominatorPolicy.networkTarget n k≤
      completed (ComplexRecursiveCallSchema.stopped d k) k schedule n :=
  CompactComplexDenominatorPolicy.network_target_le_current n k _ (actual_completed_lower d k n)

/-! Generic finite event execution charges all local programs and joins.
Concrete scalar/child program placement is in ScheduledEventExecution. -/
universe u
open SharedBankStageInput (raw)

def compileEvents {t : ℕ} (ht : 0<t) (machines : Event → Σ q,Program t q 2) :
    List Event → Σ q,Program t q 2
  | [] => ⟨1,skip t 2 ht⟩
  | e::es => ⟨_,seq (machines e).2 (compileEvents ht machines es).2⟩

def runEvents {X : Type u} (next : Event → X → X) : List Event → X → X
  | [],x => x
  | e::es,x => runEvents next es (next e x)

def runCost {X : Type u} (next : Event → X → X) (cost : Event → X → ℕ) : List Event → X → ℕ
  | [],_ => 0
  | e::es,x => cost e x+1+runCost next cost es (next e x)

theorem compile_events_runs {X : Type u} {permanent t : ℕ}
    (ht : 0<t) (machines : Event → Σ q,Program t q 2)
    (common : X → Tapes permanent 2) (next : Event → X → X) (cost : Event → X → ℕ)
    (hlocal : ∀ e x,HoareTime (machines e).2 (fun v => v=raw (common x) t)
      (fun v => v=raw (common (next e x)) t) (cost e x)) (es : List Event) (x : X) :
    HoareTime (compileEvents ht machines es).2 (fun v => v=raw (common x) t)
      (fun v => v=raw (common (runEvents next es x)) t) (runCost next cost es x) := by
  induction es generalizing x with
  | nil => exact skip_hoare ht (raw (common x) t)
  | cons e es ih => exact (hlocal e x).seq (ih (next e x))

private theorem runEvents_exponentWith {X : Type u}
    (rows : GroupIndex → List RowIndex) (target : ℕ → ℕ)
    (next : Event → X → X) (exponent : X → ℕ)
    (hs : ∀ g x,exponent (next (.scalar g) x)=exponent x+(rows g).length)
    (hc : ∀ c x,exponent (next (.child c) x)=target (exponent x))
    (es : List Event) (x : X) :
    exponent (runEvents next es x)=completedWith rows target es (exponent x) := by
  induction es generalizing x with
  | nil => rfl
  | cons e es ih =>
    cases e with
    | scalar g =>
      change exponent (runEvents next es (next (.scalar g) x))=
        completedWith rows target es (exponent x+(rows g).length)
      rw [ih,hs]
    | child c =>
      change exponent (runEvents next es (next (.child c) x))=
        completedWith rows target es (target (exponent x))
      rw [ih,hc]

/-- Every completed endpoint's exponent is computed by the actual event fold.
The scalar and child equalities are local endpoint statements, not a supplied
whole-node completed-count bound. -/
theorem runEvents_exponent {X : Type u} (next : Event → X → X) (exponent : X → ℕ)
    (stopped : Bool) (k : ℕ)
    (hs : ∀ g x,exponent (next (.scalar g) x)=exponent x+(block g).length)
    (hc : ∀ c x,exponent (next (.child c) x)=childTarget stopped (exponent x) k)
    (es : List Event) (x : X) :
    exponent (runEvents next es x)=completed stopped k es (exponent x) :=
  runEvents_exponentWith block (fun n => childTarget stopped n k) next exponent hs hc es x


end
end IntegerMultBounds.Machine.CompactComplexCompletedLiveLower
