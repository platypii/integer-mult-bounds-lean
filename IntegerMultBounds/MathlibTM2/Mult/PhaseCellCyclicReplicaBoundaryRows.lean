module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder

/-! A common row language for the packed cyclic producer and shared Schur solver. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

def cyclicReplicaBoundaryRow {s : ℕ} [NeZero s] (t band a n : ℕ)
    (C D : ZMod s → GaussianInt) : List GaussianInt :=
  (bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
    (fun i => realPartWord (if i ∈ haloVertices s a (a+min n (s-a)) then C i else D i))

@[simp] theorem cyclicReplicaBoundaryRow_length {s : ℕ} [NeZero s] (t band a n : ℕ)
    (C D : ZMod s → GaussianInt) :
    (cyclicReplicaBoundaryRow t band a n C D).length = (cyclicPrincipalBoundary s t band a n).card := by
  simp [cyclicReplicaBoundaryRow,bFoldOrder]

theorem cyclicReplicaBoundaryRow_real {s : ℕ} [NeZero s] (t band a n : ℕ)
    (C D : ZMod s → GaussianInt) :
    ∀ z ∈ cyclicReplicaBoundaryRow t band a n C D, z.im = 0 := by
  intro z hz
  obtain ⟨i,_,rfl⟩ := List.mem_map.mp hz
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
