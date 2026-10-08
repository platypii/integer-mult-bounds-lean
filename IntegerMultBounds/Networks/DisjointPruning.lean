import IntegerMultBounds.Networks.DisjointCircuit

/-! Execution with inactive DAG nodes omitted. A backwards pass computes the
actual ancestors of the requested outputs. The execution keeps node indices
stable using zero placeholders; only marked addition nodes perform additions.
This is an array execution theorem, not a tape-space allocation theorem. -/

namespace IntegerMultBounds.Networks.DisjointPruning

open DisjointCircuit

variable {ι A : Type*}

/-- Direct dependencies of a node. -/
def parents (node : Node ι) : Finset ℕ :=
  match node.kind with
  | .input _ => ∅
  | .add l r => {l, r}

/-- Mark ancestors by a single backwards pass through the topological list. -/
def markFrom (offset : ℕ) : List (Node ι) → Finset ℕ → Finset ℕ
  | [], roots => roots
  | node :: nodes, roots =>
    let marked := markFrom (offset + 1) nodes roots
    if offset ∈ marked then marked ∪ parents node else marked

def mark (nodes : List (Node ι)) (roots : Finset ℕ) : Finset ℕ :=
  markFrom 0 nodes roots

/-- Every marked node has all its parents marked. -/
def ClosedFrom (offset : ℕ) (active : Finset ℕ) : List (Node ι) → Prop
  | [] => True
  | node :: nodes =>
    (offset ∈ active → parents node ⊆ active) ∧ ClosedFrom (offset + 1) active nodes

theorem roots_subset_markFrom (offset : ℕ) (nodes : List (Node ι)) (roots : Finset ℕ) :
    roots ⊆ markFrom offset nodes roots := by
  induction nodes generalizing offset with
  | nil => exact Finset.Subset.refl _
  | cons node nodes ih =>
    simp only [markFrom]
    split_ifs
    · exact (ih _).trans Finset.subset_union_left
    · exact ih _

/-- The pass computes the least parent-closed set containing the roots. -/
theorem markFrom_subset (offset : ℕ) (nodes : List (Node ι)) (roots active : Finset ℕ)
    (hr : roots ⊆ active) (hc : ClosedFrom offset active nodes) :
    markFrom offset nodes roots ⊆ active := by
  induction nodes generalizing offset with
  | nil => exact hr
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hc
    have hs := ih (offset + 1) ht
    simp only [markFrom]
    split_ifs with ha
    · exact Finset.union_subset hs (hn (hs ha))
    · exact hs

variable [DecidableEq ι]

theorem parents_lt (prior : List (Finset ι)) (node : Node ι) (hv : node.Valid prior)
    (p : ℕ) (hp : p ∈ parents node) : p < prior.length := by
  cases node with
  | mk kind support =>
    cases kind with
    | input i => simp [parents] at hp
    | add l r =>
      simp only [Node.Valid] at hv
      split at hv
      next hl =>
        split at hv
        next hr =>
          simp only [parents, Finset.mem_insert, Finset.mem_singleton] at hp
          rcases hp with rfl | rfl <;> assumption
        next => contradiction
      next => contradiction

omit [DecidableEq ι] in
/-- Adding indices strictly before a suffix does not activate any new nodes
in that suffix. -/
theorem closedFrom_union_earlier (offset : ℕ) (nodes : List (Node ι))
    (active extra : Finset ℕ) (hc : ClosedFrom offset active nodes)
    (he : ∀ i ∈ extra, i < offset) : ClosedFrom offset (active ∪ extra) nodes := by
  induction nodes generalizing offset with
  | nil => trivial
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hc
    constructor
    · intro ha
      have ha' : offset ∈ active := by
        rcases Finset.mem_union.mp ha with h | h
        · exact h
        · have := he offset h; omega
      exact (hn ha').trans Finset.subset_union_left
    · exact ih (offset + 1) ht (fun i hi => by have := he i hi; omega)

/-- For a valid DAG, the computed backwards marking is parent closed. -/
theorem markFrom_closed (prior : List (Finset ι)) (nodes : List (Node ι))
    (roots : Finset ℕ) (hv : ValidFrom prior nodes) :
    ClosedFrom prior.length (markFrom prior.length nodes roots) nodes := by
  induction nodes generalizing prior with
  | nil => trivial
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hv
    have hi := ih (prior ++ [node.support]) ht
    simp only [List.length_append, List.length_singleton] at hi
    change (prior.length ∈ markFrom prior.length (node :: nodes) roots →
      parents node ⊆ markFrom prior.length (node :: nodes) roots) ∧ _
    simp only [markFrom]
    split_ifs with ha
    · constructor
      · intro _; exact Finset.subset_union_right
      · exact closedFrom_union_earlier _ _ _ _ hi
          (fun i hi => by have := parents_lt prior node hn i hi; omega)
    · exact ⟨fun h => False.elim (ha h), hi⟩

section Execution
variable [AddCommMonoid A]

/-- Equality of the stored values at the active indices, including absent
indices. The latter makes the evaluator total even for malformed DAGs. -/
def Agree (active : Finset ℕ) (xs ys : List A) : Prop :=
  ∀ i ∈ active, xs[i]? = ys[i]?

omit [AddCommMonoid A] in
theorem agree_append (active : Finset ℕ) (xs ys : List A) (x y : A)
    (hlen : xs.length = ys.length) (ha : Agree active xs ys)
    (hxy : xs.length ∈ active → x = y) : Agree active (xs ++ [x]) (ys ++ [y]) := by
  intro i hi
  by_cases hlt : i < xs.length
  · simpa only [List.getElem?_append_left hlt,
      List.getElem?_append_left (hlen ▸ hlt)] using ha i hi
  · by_cases he : i = xs.length
    · subst i
      simpa [← hlen] using hxy hi
    · have hgt : xs.length < i := by omega
      rw [List.getElem?_eq_none (by simp; omega), List.getElem?_eq_none (by simp; omega)]

/-- Execute only marked nodes, retaining zero placeholders for the others. -/
def evalFrom (active : Finset ℕ) (input : ι → A) : List A → List (Node ι) → List A
  | prior, [] => prior
  | prior, node :: nodes =>
    let value := if prior.length ∈ active then node.eval input prior else 0
    evalFrom active input (prior ++ [value]) nodes

def eval (active : Finset ℕ) (input : ι → A) (nodes : List (Node ι)) : List A :=
  evalFrom active input [] nodes

omit [DecidableEq ι] in
/-- Closed marking preserves every active value throughout actual execution. -/
theorem evalFrom_agree (active : Finset ℕ) (input : ι → A)
    (nodes : List (Node ι)) (xs ys : List A) (hlen : xs.length = ys.length)
    (ha : Agree active xs ys) (hc : ClosedFrom xs.length active nodes) :
    Agree active (evalFrom active input xs nodes) (DisjointCircuit.evalFrom input ys nodes) := by
  induction nodes generalizing xs ys with
  | nil => exact ha
  | cons node nodes ih =>
    obtain ⟨hn, ht⟩ := hc
    apply ih
    · simp [hlen]
    · apply agree_append active xs ys _ _ hlen ha
      intro hactive
      simp only [hactive, ↓reduceIte]
      have hp := hn hactive
      cases node with
      | mk kind support =>
        cases kind with
        | input i => rfl
        | add l r =>
          simp only [Node.eval]
          rw [ha l (hp (by simp [parents])), ha r (hp (by simp [parents]))]
    · simpa using ht

/-- Backwards-marked execution returns the exact sum at every requested
output of a valid DAG, while omitting all inactive additions. -/
theorem eval_output (input : ι → A) (nodes : List (Node ι))
    (roots : Finset ℕ) (hv : Valid nodes) (i : ℕ) (hi : i ∈ roots) :
    (eval (mark nodes roots) input nodes)[i]? =
      (nodes.map (fun node => supportSum input node.support))[i]? := by
  have hc := markFrom_closed [] nodes roots hv
  have ha := evalFrom_agree (mark nodes roots) input nodes [] [] rfl (by intro _ _; rfl) hc
  have hm : i ∈ mark nodes roots := roots_subset_markFrom 0 nodes roots hi
  have he := ha i hm
  change (eval (mark nodes roots) input nodes)[i]? = (DisjointCircuit.eval input nodes)[i]? at he
  rw [DisjointCircuit.eval_eq input nodes hv] at he
  exact he

end Execution

/-- The exact number of additions performed by marked execution. Input
copies and skipped nodes do not contribute to this arithmetic count. -/
def additionCountFrom (offset : ℕ) (active : Finset ℕ) : List (Node ι) → ℕ
  | [] => 0
  | node :: nodes =>
    (if offset ∈ active then match node.kind with | .input _ => 0 | .add _ _ => 1 else 0) +
      additionCountFrom (offset + 1) active nodes

/-- Instrumented execution counts precisely the additions it performs. -/
def runFrom [AddCommMonoid A] (active : Finset ℕ) (input : ι → A) :
    List A → List (Node ι) → List A × ℕ
  | prior, [] => (prior, 0)
  | prior, node :: nodes =>
    let value := if prior.length ∈ active then node.eval input prior else 0
    let cost := if prior.length ∈ active then
      match node.kind with | .input _ => 0 | .add _ _ => 1 else 0
    let rest := runFrom active input (prior ++ [value]) nodes
    (rest.1, cost + rest.2)

omit [DecidableEq ι] in
theorem runFrom_eq [AddCommMonoid A] (active : Finset ℕ) (input : ι → A)
    (prior : List A) (nodes : List (Node ι)) :
    runFrom active input prior nodes =
      (evalFrom active input prior nodes, additionCountFrom prior.length active nodes) := by
  induction nodes generalizing prior with
  | nil => rfl
  | cons node nodes ih => simp [runFrom, evalFrom, additionCountFrom, ih]

/-- The marked run has the certified output and exactly its marked addition
count. Placeholder writes and input copies are not charged as additions. -/
theorem run_correct [AddCommMonoid A] (input : ι → A) (nodes : List (Node ι))
    (roots : Finset ℕ) (hv : Valid nodes) :
    (∀ i ∈ roots, (runFrom (mark nodes roots) input [] nodes).1[i]? =
      (nodes.map (fun node => supportSum input node.support))[i]?) ∧
    (runFrom (mark nodes roots) input [] nodes).2 =
      additionCountFrom 0 (mark nodes roots) nodes := by
  rw [runFrom_eq]
  exact ⟨fun i hi => eval_output input nodes roots hv i hi, rfl⟩

omit [DecidableEq ι] in
theorem additionCountFrom_le_length (offset : ℕ) (active : Finset ℕ) (nodes : List (Node ι)) :
    additionCountFrom offset active nodes ≤ nodes.length := by
  induction nodes generalizing offset with
  | nil => simp [additionCountFrom]
  | cons node nodes ih =>
    have hh := ih (offset + 1)
    simp only [additionCountFrom, List.length_cons]
    split_ifs <;> cases node.kind <;> (try simp only) <;> omega

end IntegerMultBounds.Networks.DisjointPruning
