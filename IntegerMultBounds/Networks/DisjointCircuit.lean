import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.Basic
import Mathlib.Tactic

/-! Finite cancellation-free addition DAGs with explicit source supports.
A structural checker validates backward references and disjoint unions.
Evaluation executes the listed additions; support sums describe its proved
semantics, and equal-support interning safely shares previously built nodes.
No generated circuit certificate or tape-runtime claim is made here. -/

namespace IntegerMultBounds.Networks.DisjointCircuit

variable {ι A : Type*} [DecidableEq ι]

inductive Kind (ι : Type*) where
  | input (source : ι)
  | add (left right : ℕ)
  deriving DecidableEq

structure Node (ι : Type*) where
  kind : Kind ι
  support : Finset ι
  deriving DecidableEq

/-- Input nodes certify singleton supports. Addition nodes refer only to
previous nodes, whose disjoint supports must have exactly the stated union. -/
def Node.Valid (prior : List (Finset ι)) (node : Node ι) : Prop :=
  match node.kind with
  | .input i => node.support = {i}
  | .add l r =>
    if hl : l < prior.length then
      if hr : r < prior.length then
        Disjoint prior[l] prior[r] ∧ node.support = prior[l] ∪ prior[r]
      else False
    else False

instance (prior : List (Finset ι)) (node : Node ι) : Decidable (node.Valid prior) := by
  unfold Node.Valid
  split <;> infer_instance

/-- The recursion records each newly built support in topological order. -/
def ValidFrom (prior : List (Finset ι)) : List (Node ι) → Prop
  | [] => True
  | node :: nodes => node.Valid prior ∧ ValidFrom (prior ++ [node.support]) nodes

def Valid (nodes : List (Node ι)) : Prop := ValidFrom [] nodes

def checkFrom (prior : List (Finset ι)) : List (Node ι) → Bool
  | [] => true
  | node :: nodes => decide (node.Valid prior) && checkFrom (prior ++ [node.support]) nodes

def check (nodes : List (Node ι)) : Bool := checkFrom [] nodes

/-- The computable checker accepts exactly the structural validity predicate. -/
theorem checkFrom_eq_true (prior : List (Finset ι)) (nodes : List (Node ι)) :
    checkFrom prior nodes = true ↔ ValidFrom prior nodes := by
  induction nodes generalizing prior with
  | nil => simp [checkFrom, ValidFrom]
  | cons node nodes ih => simp [checkFrom, ValidFrom, ih]

theorem check_eq_true (nodes : List (Node ι)) : check nodes = true ↔ Valid nodes :=
  checkFrom_eq_true [] nodes

/-- Concatenating finite construction lists preserves the exact prior support
bank passed to the second construction. -/
theorem validFrom_append (prior : List (Finset ι)) (p q : List (Node ι)) :
    ValidFrom prior (p ++ q) ↔ ValidFrom prior p ∧ ValidFrom (prior ++ p.map Node.support) q := by
  induction p generalizing prior with
  | nil => simp [ValidFrom]
  | cons node p ih => simp [ValidFrom, ih, List.append_assoc, and_assoc]

section Evaluation

variable [AddCommMonoid A]

def supportSum (input : ι → A) (support : Finset ι) : A := ∑ i ∈ support, input i

/-- Actual node evaluation uses earlier computed values. The default value
only totalizes invalid references, which accepted circuits never use. -/
def Node.eval (input : ι → A) (prior : List A) (node : Node ι) : A :=
  match node.kind with
  | .input i => input i
  | .add l r => prior[l]?.getD 0 + prior[r]?.getD 0

def evalFrom (input : ι → A) : List A → List (Node ι) → List A
  | prior, [] => prior
  | prior, node :: nodes => evalFrom input (prior ++ [node.eval input prior]) nodes

def eval (input : ι → A) (nodes : List (Node ι)) : List A := evalFrom input [] nodes

/-- One checked addition is exactly the sum over its certified support. -/
theorem Node.eval_eq (input : ι → A) (prior : List (Finset ι)) (node : Node ι)
    (hv : node.Valid prior) :
    node.eval input (prior.map (supportSum input)) = supportSum input node.support := by
  rcases node with ⟨kind, support⟩
  cases kind with
  | input i =>
    change support = {i} at hv
    subst support
    simp [Node.eval, supportSum]
  | add l r =>
    simp only [Node.Valid] at hv
    split at hv
    next hl =>
      split at hv
      next hr =>
        obtain ⟨hd, hs⟩ := hv
        simp only [Node.eval, List.getElem?_map, List.getElem?_eq_getElem hl,
          List.getElem?_eq_getElem hr, Option.map_some, Option.getD_some]
        rw [hs]
        exact (Finset.sum_union hd).symm
      next hr => contradiction
    next hl => contradiction

/-- Recursive finite-list evaluation preserves support semantics at every
stored node, including all nodes that predate the current construction. -/
theorem evalFrom_eq (input : ι → A) (prior : List (Finset ι)) (nodes : List (Node ι))
    (hv : ValidFrom prior nodes) :
    evalFrom input (prior.map (supportSum input)) nodes =
      (prior ++ nodes.map Node.support).map (supportSum input) := by
  induction nodes generalizing prior with
  | nil => simp [evalFrom]
  | cons node nodes ih =>
    obtain ⟨hn, htail⟩ := hv
    simp only [evalFrom, Node.eval_eq input prior node hn]
    rw [show prior.map (supportSum input) ++ [supportSum input node.support] =
      (prior ++ [node.support]).map (supportSum input) by simp]
    rw [ih _ htail]
    simp [List.append_assoc]

/-- Every accepted DAG evaluates to its actual support sums, for arbitrary
commutative additive monoids; no subtraction or cancellation is assumed. -/
theorem eval_eq (input : ι → A) (nodes : List (Node ι)) (hv : Valid nodes) :
    eval input nodes = nodes.map (fun node => supportSum input node.support) := by
  simpa [eval, List.map_map, Function.comp_def] using evalFrom_eq input [] nodes hv

omit [DecidableEq ι] in
theorem eval_append (input : ι → A) (prior : List A) (p q : List (Node ι)) :
    evalFrom input prior (p ++ q) = evalFrom input (evalFrom input prior p) q := by
  induction p generalizing prior with
  | nil => rfl
  | cons node p ih => exact ih _

theorem eval_length (input : ι → A) (nodes : List (Node ι)) (hv : Valid nodes) :
    (eval input nodes).length = nodes.length := by rw [eval_eq input nodes hv]; simp

/-- The value at each valid node identifier is its certified support sum. -/
theorem eval_getElem (input : ι → A) (nodes : List (Node ι)) (hv : Valid nodes)
    (i : ℕ) (hi : i < nodes.length) :
    (eval input nodes)[i]'(by rw [eval_length input nodes hv]; exact hi) =
      supportSum input nodes[i].support := by
  simp [eval_eq input nodes hv]

/-- Equal supports suffice to replace one already computed node by another,
even if their recursive constructions and node identifiers differ. -/
theorem equal_support_eval (input : ι → A) (nodes : List (Node ι)) (hv : Valid nodes)
    (i j : ℕ) (hi : i < nodes.length) (hj : j < nodes.length)
    (hs : nodes[i].support = nodes[j].support) :
    (eval input nodes)[i]'(by rw [eval_length input nodes hv]; exact hi) =
      (eval input nodes)[j]'(by rw [eval_length input nodes hv]; exact hj) := by
  rw [eval_getElem input nodes hv i hi, eval_getElem input nodes hv j hj, hs]

end Evaluation

/-- A simple executable support lookup, sufficient to justify optimized
hash-table implementations separately without assuming their correctness. -/
def findSupport (support : Finset ι) : List (Finset ι) → Option ℕ
  | [] => none
  | s :: ss => if s = support then some 0 else (findSupport support ss).map Nat.succ

theorem findSupport_sound (support : Finset ι) (prior : List (Finset ι)) (i : ℕ)
    (hf : findSupport support prior = some i) : prior[i]? = some support := by
  induction prior generalizing i with
  | nil => simp [findSupport] at hf
  | cons s ss ih =>
    by_cases hs : s = support
    · simp [findSupport, hs] at hf
      subst i
      simp [hs]
    · simp only [findSupport, hs, ↓reduceIte] at hf
      obtain ⟨j, hj, hij⟩ := Option.map_eq_some_iff.mp hf
      subst i
      simpa using ih j hj

/-- Reuse an existing node with equal support, otherwise append the proposed
node. The result includes its concrete index in the resulting finite DAG. -/
def intern (nodes : List (Node ι)) (node : Node ι) : List (Node ι) × ℕ :=
  match findSupport node.support (nodes.map Node.support) with
  | some i => (nodes, i)
  | none => (nodes ++ [node], nodes.length)

/-- Interning preserves validity; even the append branch checks actual prior
references and disjointness through the supplied structural proof. -/
theorem intern_valid (nodes : List (Node ι)) (node : Node ι) (hv : Valid nodes)
    (hn : node.Valid (nodes.map Node.support)) : Valid (intern nodes node).1 := by
  unfold intern
  split
  · exact hv
  · apply (validFrom_append [] nodes [node]).mpr
    simpa [Valid, ValidFrom] using And.intro hv hn

/-- The returned index always exists and has exactly the requested support. -/
theorem intern_support (nodes : List (Node ι)) (node : Node ι) :
    ((intern nodes node).1.map Node.support)[(intern nodes node).2]? = some node.support := by
  unfold intern
  split
  next i hi => exact findSupport_sound node.support (nodes.map Node.support) i hi
  next hi => simp

/-- Actual evaluation of the interned reference equals the proposed node's
support sum, covering both reuse and newly appended construction. -/
theorem intern_eval [AddCommMonoid A] (input : ι → A) (nodes : List (Node ι)) (node : Node ι)
    (hv : Valid nodes) (hn : node.Valid (nodes.map Node.support)) :
    (eval input (intern nodes node).1)[(intern nodes node).2]? = some (supportSum input node.support) := by
  rw [eval_eq input _ (intern_valid nodes node hv hn)]
  have hs := intern_support nodes node
  have hm := congrArg (Option.map (supportSum input)) hs
  simpa only [← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some] using hm

/-- A successful support lookup permits immediate reuse without constructing
or validating a new addition node. -/
theorem reuse_eval [AddCommMonoid A] (input : ι → A) (nodes : List (Node ι))
    (hv : Valid nodes) (support : Finset ι) (i : ℕ)
    (hf : findSupport support (nodes.map Node.support) = some i) :
    (eval input nodes)[i]? = some (supportSum input support) := by
  rw [eval_eq input nodes hv]
  have hs := congrArg (Option.map (supportSum input)) (findSupport_sound support _ i hf)
  simpa only [← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some] using hs

end IntegerMultBounds.Networks.DisjointCircuit
