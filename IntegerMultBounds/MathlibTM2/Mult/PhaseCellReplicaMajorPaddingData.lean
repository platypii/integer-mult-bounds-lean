module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPaddedArchiveTileData

/-! Whole dummy rows prefix each replica independently. The finite row view
is read from that padded list, preserving every real row at its shifted index. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {α : Type*} {N B : ℕ}

def prefixPaddedRows (capacity L : ℕ) (hN : N ≤ capacity) (fill : α)
    (rows : Fin N → Fin B → List α) (i : Fin capacity) (j : Fin B) : List α :=
  (List.replicate (capacity-N) (List.replicate L fill)++List.ofFn (fun k => rows k j))[i.val]'(by
    simp only [List.length_append,List.length_replicate,List.length_ofFn]
    have := i.isLt
    omega)

theorem prefixPaddedRows_list (capacity L : ℕ) (hN : N ≤ capacity) (fill : α)
    (rows : Fin N → Fin B → List α) (j : Fin B) :
    List.ofFn (fun i => prefixPaddedRows capacity L hN fill rows i j) =
      List.replicate (capacity-N) (List.replicate L fill)++List.ofFn (fun k => rows k j) := by
  apply List.ext_getElem (by simp; omega)
  intro i hi hi'
  simp only [List.getElem_ofFn,prefixPaddedRows]

theorem prefixPaddedRows_length (capacity L : ℕ) (hN : N ≤ capacity) (fill : α)
    (rows : Fin N → Fin B → List α) (hlen : ∀ i j, (rows i j).length = L)
    (i : Fin capacity) (j : Fin B) : (prefixPaddedRows capacity L hN fill rows i j).length = L := by
  let xs := List.replicate (capacity-N) (List.replicate L fill)++List.ofFn (fun k => rows k j)
  have hi : i.val < xs.length := by simp only [xs,List.length_append,List.length_replicate,List.length_ofFn]; have := i.isLt; omega
  have hm : xs[i.val] ∈ xs := List.getElem_mem hi
  change (xs[i.val]'hi).length = L
  rcases List.mem_append.mp hm with hm | hm
  · have he := List.eq_of_mem_replicate hm
    rw [he,List.length_replicate]
  · obtain ⟨k,hk⟩ := List.mem_ofFn.mp hm
    rw [←hk]
    exact hlen k j

theorem prefixPaddedRows_real (capacity L : ℕ) (hN : N ≤ capacity) (fill : α)
    (rows : Fin N → Fin B → List α) (i : Fin N) (j : Fin B) :
    prefixPaddedRows capacity L hN fill rows (paddedCoreIndex hN i) j = rows i j := by
  simp only [prefixPaddedRows,paddedCoreIndex]
  rw [List.getElem_append_right (by simp)]
  simp

theorem prefixPaddedRows_flatten (capacity L : ℕ) (hN : N ≤ capacity) (fill : α)
    (rows : Fin N → Fin B → List α) (hlen : ∀ i j, (rows i j).length = L) (j : Fin B) :
    (List.ofFn (fun i => prefixPaddedRows capacity L hN fill rows i j)).flatten =
      tilePrefixPad (capacity*L) fill (List.ofFn (fun i => rows i j)).flatten := by
  have hlenFlat : (List.ofFn (fun i => rows i j)).flatten.length = N*L := by
    simp only [List.length_flatten,List.map_ofFn,Function.comp_def,hlen,List.ofFn_const,
      List.sum_replicate,smul_eq_mul]
  rw [prefixPaddedRows_list,List.flatten_append,List.flatten_replicate_replicate]
  simp only [tilePrefixPad,hlenFlat,←Nat.sub_mul]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
