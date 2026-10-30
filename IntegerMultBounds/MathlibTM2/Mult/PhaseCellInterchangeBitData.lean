module

public import IntegerMultBounds.MathlibTM2.Host.ChunkSwap

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Host

/-- The machine's finite-array view is derived from the actual bit list. -/
theorem bitArray_of_length {V : ℕ} (xs : List Bool) (hlen : xs.length = V) :
    ∃ x : Fin V → Bool, List.ofFn x = xs := by
  subst V
  exact ⟨xs.get,List.ofFn_get xs⟩

/-- Full rectangular interchanges never use the default symbol. Thus routing
encoded bits with machine blank is exactly encoding the routed Boolean list. -/
theorem swapList_bitSymbols {P H G D B A : ℕ} (xs : List Bool)
    (hlen : xs.length = BinaryAdjacentWidthInterchange.volume P H G D B) :
    swapList P H G D B (blank : Fin (A+4)) (xs.map bitSymbol) =
      (swapList P H G D B false xs).map bitSymbol := by
  obtain ⟨x,hx⟩ := bitArray_of_length xs hlen
  simp only [←hx,List.map_ofFn,Function.comp_def]
  rw [←transpose_bits_eq_swapList,←ofFn_transpose x false,List.map_ofFn]
  rfl

theorem swapList_bitSymbols_length {P H G D B : ℕ} (xs : List Bool)
    (hlen : xs.length = BinaryAdjacentWidthInterchange.volume P H G D B) :
    (swapList P H G D B false xs).length = xs.length := by
  simp only [swapList,List.length_map,List.length_range,hlen,
    BinaryAdjacentWidthInterchange.volume]
  ac_rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
