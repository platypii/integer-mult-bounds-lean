import IntegerMultBounds.Networks.SharedPointKey
import IntegerMultBounds.Networks.DisjointCircuit

/-! Executable compressed-key sharing across common-point DAG copies. Lookup
is enabled precisely when at least two points belong to every source triple.
The key test is proved to reuse only an exactly equal support. -/

namespace IntegerMultBounds.Networks.SharedPointIntern

open NeighborCounts SharedPointKey DisjointCircuit
variable {h : ℕ}

/-- Only addition nodes enter the upstream sharing dictionary. -/
def nodeKey (node : Node (Triple h)) : Finset (Finset (Fin h) × Finset (Fin h)) :=
  match node.kind with
  | .input _ => ∅
  | .add _ _ => {key node.support}

/-- Upstream's shared dictionary lookup, represented by a linear list scan.
The one-common-point branch always allocates a fresh node. -/
def find (support : Finset (Triple h)) (nodes : List (Node (Triple h))) : Option ℕ :=
  if 2 ≤ (core support).card then
    findSupport {key support} (nodes.map nodeKey)
  else none

theorem find_sound (support : Finset (Triple h)) (nodes : List (Node (Triple h)))
    (i : ℕ) (hi : find support nodes = some i) :
    (nodes.map Node.support)[i]? = some support := by
  unfold find at hi
  split at hi
  next hc =>
    have hs := findSupport_sound {key support} (nodes.map nodeKey) i hi
    rw [List.getElem?_map] at hs
    obtain ⟨node, hn, hk⟩ := Option.map_eq_some_iff.mp hs
    have hk' : key node.support = key support := by
      cases he : node.kind <;> simp_all [nodeKey]
    have he : support = node.support := key_injective support node.support hc hk'.symm
    simp [List.getElem?_map, hn, ← he]
  next => simp at hi

/-- Reuse the compressed-key match, or append the proposed node. -/
def intern (nodes : List (Node (Triple h))) (node : Node (Triple h)) :
    List (Node (Triple h)) × ℕ :=
  match find node.support nodes with
  | some i => (nodes, i)
  | none => (nodes ++ [node], nodes.length)

theorem intern_valid (nodes : List (Node (Triple h))) (node : Node (Triple h))
    (hv : Valid nodes) (hn : node.Valid (nodes.map Node.support)) :
    Valid (intern nodes node).1 := by
  unfold intern
  split
  · exact hv
  · apply (validFrom_append [] nodes [node]).mpr
    simpa [Valid, ValidFrom] using And.intro hv hn

theorem intern_support (nodes : List (Node (Triple h))) (node : Node (Triple h)) :
    ((intern nodes node).1.map Node.support)[(intern nodes node).2]? = some node.support := by
  unfold intern
  split
  next i hi => exact find_sound node.support nodes i hi
  next => simp

/-- Compressed sharing preserves the actual addition-DAG value over every
commutative additive monoid, including the newly allocated case. -/
theorem intern_eval {A : Type*} [AddCommMonoid A] (input : Triple h → A)
    (nodes : List (Node (Triple h))) (node : Node (Triple h))
    (hv : Valid nodes) (hn : node.Valid (nodes.map Node.support)) :
    (eval input (intern nodes node).1)[(intern nodes node).2]? =
      some (supportSum input node.support) := by
  rw [eval_eq input _ (intern_valid nodes node hv hn)]
  have hs := congrArg (Option.map (supportSum input)) (intern_support nodes node)
  simpa only [← List.getElem?_map, List.map_map, Function.comp_def, Option.map_some] using hs

/-- A key match never consumes a new node in the addition DAG. -/
theorem intern_length_le (nodes : List (Node (Triple h))) (node : Node (Triple h)) :
    (intern nodes node).1.length ≤ nodes.length + 1 := by
  unfold intern
  split <;> simp

end IntegerMultBounds.Networks.SharedPointIntern
