module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealPrefix
public import IntegerMultBounds.NLogN.PhaseCellCyclicBoundaryOrder

/-! A common row language for the packed cyclic producer and shared Schur solver. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Fast
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

theorem cyclicReplicaBoundaryRows_stream {A s : ℕ} [NeZero s] (t band a n w : ℕ)
    (pairs : List ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))) :
    pairs.flatMap (fun z => cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2)) =
      cstream A w ((pairs.map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)).flatten) := by
  induction pairs with
  | nil => rfl
  | cons z pairs ih =>
    simpa only [List.flatMap_cons,List.map_cons,List.flatten_cons,cstream_append] using
      congrArg (cstream A w (cyclicReplicaBoundaryRow t band a n z.1 z.2) ++ ·) ih

theorem cyclicReplicaBoundaryRows_getD {s : ℕ} [NeZero s] (t band a n j : ℕ)
    (Cs Ds : List (ZMod s → GaussianInt)) (hC : j < Cs.length) (hD : j < Ds.length) :
    ((Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)).getD j [] =
      cyclicReplicaBoundaryRow t band a n (Cs.getD j (fun _ => 0)) (Ds.getD j (fun _ => 0)) := by
  have hj : j < ((Cs.zip Ds).map (fun z => cyclicReplicaBoundaryRow t band a n z.1 z.2)).length := by
    simp only [List.length_map,List.length_zip]
    exact Nat.lt_min.mpr ⟨hC,hD⟩
  rw [List.getD_eq_getElem _ _ hj,List.getElem_map,List.getElem_zip]
  rw [List.getD_eq_getElem _ _ hC,List.getD_eq_getElem _ _ hD]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
