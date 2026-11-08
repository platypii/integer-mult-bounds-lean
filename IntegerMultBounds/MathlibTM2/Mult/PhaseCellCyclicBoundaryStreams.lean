module

public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundarySolutionField
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellScalarStream

/-! The one natural-order joint boundary row splits into right then left piece
prefixes. Each piece sees zero at its nonboundary window coordinates. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {s : ℕ} [NeZero s]

theorem cyclicBoundaryStream_split (A w t band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (G : ZMod s → GaussianInt) :
    cstream A w ((bOrder s (cyclicPrincipalBoundary s t band a n)).map G) =
      cstream A w ((bOrder s (haloBoundary s t band 0 (n-min n (s-a)))).map G) ++
        cstream A w ((bOrder s (haloBoundary s t band a (a+min n (s-a)))).map G) := by
  rw [cyclicPrincipalBoundary_order t band a n ha hn,List.map_append,cstream_append]

theorem cyclicBoundary_window_left (t band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i : ZMod s) (hi : a ≤ i.val) :
    i ∈ cyclicPrincipalBoundary s t band a n ↔ i ∈ haloBoundary s t band a (a+min n (s-a)) := by
  have hoff : i ∉ haloBoundary s t band 0 (n-min n (s-a)) := by
    intro hm
    have hv := (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hm).1
    omega
  rw [cyclicPrincipalBoundary_eq t band a n ha hn,Finset.mem_union]
  simp only [hoff,or_false]

theorem cyclicBoundary_window_right (t band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (i : ZMod s) (hi : i.val < n-min n (s-a)) :
    i ∈ cyclicPrincipalBoundary s t band a n ↔ i ∈ haloBoundary s t band 0 (n-min n (s-a)) := by
  have hoff : i ∉ haloBoundary s t band a (a+min n (s-a)) := by
    intro hm
    have hv := (mem_haloVertices _ _ i).mp (Finset.mem_sdiff.mp hm).1
    omega
  rw [cyclicPrincipalBoundary_eq t band a n ha hn,Finset.mem_union]
  simp only [hoff,false_or]

theorem cyclicBoundaryField_piece_zero (t band a n : ℕ) (ha : a < s) (hn : n ≤ s)
    (solution : List GaussianInt) :
    (∀ i : ZMod s, a ≤ i.val → i ∉ haloBoundary s t band a (a+min n (s-a)) →
      boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution i = 0) ∧
    (∀ i : ZMod s, i.val < n-min n (s-a) → i ∉ haloBoundary s t band 0 (n-min n (s-a)) →
      boundarySolutionField (cyclicPrincipalBoundary s t band a n) solution i = 0) := by
  constructor
  · intro i hi hoff
    exact boundarySolutionField_off _ _ i (fun hm => hoff ((cyclicBoundary_window_left t band a n ha hn i hi).mp hm))
  · intro i hi hoff
    exact boundarySolutionField_off _ _ i (fun hm => hoff ((cyclicBoundary_window_right t band a n ha hn i hi).mp hm))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
