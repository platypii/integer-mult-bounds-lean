module

public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFoldData

/-! Reuse the ordinary boundary streams and tape fold for one joint cyclic page. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def cyclicBoundaryIndexWords (s t band a n : ℕ) : List GaussianInt :=
  boundaryIndexWords s t band 0 (n-min n (s-a)) ++
    boundaryIndexWords s t band a (a+min n (s-a))

theorem cyclicBoundaryIndexWords_order {s t : ℕ} [NeZero s] (hst : s < t)
    (band a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    cyclicBoundaryIndexWords s t band a n =
      (bOrder s (cyclicPrincipalBoundary s t band a n)).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)) := by
  rw [cyclicBoundaryIndexWords,boundaryIndexWords_order hst band 0 _ (by omega),
    boundaryIndexWords_order hst band a _ (by omega),← List.map_append,
    ← cyclicPrincipalBoundary_order t band a n ha hn]

theorem cyclicBoundaryIndexWords_length {s t : ℕ} [NeZero s] (hst : s < t)
    (band a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    (cyclicBoundaryIndexWords s t band a n).length = (cyclicPrincipalBoundary s t band a n).card := by
  rw [cyclicBoundaryIndexWords_order hst band a n ha hn,List.length_map]
  rw [← List.toFinset_card_of_nodup (bOrder_nodup s _),bOrder_toFinset]

theorem cyclicBoundaryIndexWords_fold {s t : ℕ} [NeZero s] (hst : s < t)
    (band a n : ℕ) (ha : a < s) (hn : n ≤ s) :
    foldList (cyclicBoundaryIndexWords s t band a n) =
      (bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
        (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)) := by
  rw [cyclicBoundaryIndexWords_order hst band a n ha hn,foldList_map,foldList_bOrder]

theorem cyclicBoundaryOrderSymbols_cstream (A w s t band a n : ℕ) :
    boundaryOrderSymbols A w s t band 0 (n-min n (s-a)) ++
      boundaryOrderSymbols A w s t band a (a+min n (s-a)) =
        cstream A w (cyclicBoundaryIndexWords s t band a n) := by
  rw [boundaryOrderSymbols_cstream,boundaryOrderSymbols_cstream]
  simp [cyclicBoundaryIndexWords,cstream,List.flatMap_append]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
