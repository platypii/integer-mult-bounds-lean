module

public import IntegerMultBounds.MathlibTM2.Fast.BandFactor
public import IntegerMultBounds.MathlibTM2.Fast.CMulStream

/-! Factor page volumes depend on the window shape, not on matrix entries. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast

theorem factorTableVolumes (A w q K W N : ℕ) (rows inputs : List (List ℤ))
    (hrows : rows.length = W+1) (hrl : ∀ row ∈ rows, row.length = 2*W+1)
    (hin : ∀ row ∈ inputs, row.length = 2*W+1) (hN : inputs.length = N) :
    (cstream A w ((facLf q K rows inputs N).map fun z => (⟨z,0⟩ : GaussianInt))).length = N*W*w ∧
    (cstream A w ((List.range N).reverse.map fun m =>
      colC (Mult.BandFactor.ucolZ W (facUr q K rows inputs N) m)).flatten).length = N*W*w ∧
    (cstream A w ((List.range N).reverse.map fun j =>
      (⟨Mult.BandFactor.newtonZ q (facPiv (facState q K rows inputs j)) K,0⟩ : GaussianInt))).length = N*w := by
  refine ⟨?_,?_,?_⟩
  · rw [length_cstream,List.length_map,length_facLf q K W N rows inputs hrows hrl hin (by omega)]
  · rw [length_cstream,List.length_flatten,List.map_map]
    rw [List.map_congr_left (g := fun _ => W) (fun _ _ => by simp [colC,Mult.BandFactor.ucolZ])]
    simp
  · simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
