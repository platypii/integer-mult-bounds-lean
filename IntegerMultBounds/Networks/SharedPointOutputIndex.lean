import IntegerMultBounds.Networks.SharedPointExecution

/-! Arithmetic output addressing for the actual shared-point program. The
common-point/pair output index requires no search through the output list. -/

namespace IntegerMultBounds.Networks.SharedPointOutputIndex

open DisjointCircuit NeighborCounts SharedPointReplay SharedPointExecution

attribute [local irreducible] SharedPointReplay.circuit

private theorem flatMap_product_lookup {α β : Type*} (xs : List α) (ys : List β)
    (i j : ℕ) (hi : i < xs.length) (hj : j < ys.length) :
    (xs.flatMap (fun a => ys.map (fun b => (a,b))))[ys.length * i + j]? =
      some (xs[i], ys[j]) := by
  induction xs generalizing i with
  | nil => simp at hi
  | cons x xs ih =>
    cases i with
    | zero =>
      simp only [List.flatMap_cons, Nat.mul_zero, Nat.zero_add, List.getElem_cons_zero]
      rw [List.getElem?_append_left (by simpa using hj), List.getElem?_map,
        List.getElem?_eq_getElem hj, Option.map_some]
    | succ i =>
      simp only [List.flatMap_cons, List.getElem_cons_succ]
      rw [List.getElem?_append_right (by simp only [List.length_map, Nat.mul_succ]; omega)]
      simp only [List.length_map]
      have he : ys.length * (i+1) + j - ys.length = ys.length * i + j := by rw [Nat.mul_succ]; omega
      rw [he]
      exact ih i (by simpa using hi)

/-- Fixed-width row-major addressing of every common-point/pair request. -/
def index (c : Fin 50) (j : Fin 1176) : ℕ := 1176 * c.val + j.val

theorem index_bound (c : Fin 50) (j : Fin 1176) : index c j < 58800 := by
  have hc := c.isLt
  have hj := j.isLt
  unfold index
  omega

theorem index_eq_iff (c d : Fin 50) (i j : Fin 1176) :
    index c i = index d j ↔ c = d ∧ i = j := by
  constructor
  · intro he
    have hi := i.isLt
    have hj := j.isLt
    unfold index at he
    have hc : c.val = d.val := by omega
    have hp : i.val = j.val := by omega
    exact ⟨Fin.ext hc, Fin.ext hp⟩
  · rintro ⟨rfl, rfl⟩
    rfl

theorem index_output_bound (c : Fin 50) (j : Fin 1176) : index c j < circuit.outputs.length := by
  rw [output_count]
  exact index_bound c j

/-- The actual ordered output list has precisely the requested key at the
computed index. -/
theorem output_key (c : Fin 50) (j : Fin 1176) :
    key (circuit.outputs[index c j]'(index_output_bound c j)) = (c, PairMask.pairAt 49 j) := by
  have hc : c.val < (List.finRange 50).length := by simp
  have hj : j.val < (PairedCircuit.pairs (List.range 49)).length := by
    rw [PairMask.pairs_range_length]
    exact j.isLt
  have hh := flatMap_product_lookup (List.finRange 50) (PairedCircuit.pairs (List.range 49))
    c.val j.val hc hj
  have he : (List.finRange 50)[c.val] = c := by ext; simp
  rw [he] at hh
  have hn : (PairedCircuit.pairs (List.range 49)).length = 1176 := PairMask.pairs_range_length 49
  rw [hn, ← output_keys, List.getElem?_map] at hh
  change Option.map key circuit.outputs[index c j]? = some (c, PairMask.pairAt 49 j) at hh
  rw [List.getElem?_eq_getElem (index_output_bound c j), Option.map_some] at hh
  exact Option.some.inj hh

/-- Direct execution semantics at the arithmetic address, without existential
selection of an output port. -/
theorem run_partial_at (input : Triple 50 → ZMod 2) (c : Fin 50) (j : Fin 1176) :
    Circuit.run code.program (SharedPointExecution.initial input) (code.outputSlot (index c j)) =
      supportSum input (Finset.univ.filter (fun T : Triple 50 =>
        T.val ∩ (embedding c j).val = {c})) := by
  have hk := output_key c j
  have hc := congrArg Prod.fst hk
  have hp := congrArg Prod.snd hk
  simp only [key] at hc hp
  rw [run_output input _ (index_output_bound c j), expected, hc, hp]
  exact congrArg (supportSum input) (SharedPointOutputMap.lifted_exclusion 49 c j)

end IntegerMultBounds.Networks.SharedPointOutputIndex
