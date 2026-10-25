module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Fast.ResampASem

/-! A physical slice of the ambient line is the solver's original-coordinate
RHS row. Concatenating natural windows therefore constructs its exact batch ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem ambientLine_window {s : ℕ} (C : ZMod s → GaussianInt) (p L : ℕ) (hp : p+L ≤ s) :
    ((chirpLine s C).drop p).take L =
      cellSourceRows L (fun _ => (p : ZMod s)) (fun _ => C) 0 := by
  apply List.ext_getElem
  · simp [List.length_take, List.length_drop, Nat.min_eq_left (show L ≤ s-p by omega)]
  · intro i hi hj
    simp only [List.getElem_take, List.getElem_drop, chirpLine, List.getElem_map,
      List.getElem_range, cellSourceRows]
    simp [Nat.cast_add]

theorem ambientStream_window {A s : ℕ} (w : ℕ) (C : ZMod s → GaussianInt) (p L : ℕ)
    (hp : p+L ≤ s) :
    ((cstream A w (chirpLine s C)).drop (p*w)).take (L*w) =
      cstream A w (cellSourceRows L (fun _ => (p : ZMod s)) (fun _ => C) 0) := by
  rw [rsa_cstream_drop, rsa_cstream_take, ambientLine_window C p L hp]

def naturalGatherRows {A s : ℕ} (t band L w : ℕ) (C : ZMod s → GaussianInt) : List (Fin (A+4)) :=
  (naturalSymbolOrigins s t band L w).flatMap
    (fun p => ((cstream A w (chirpLine s C)).drop p).take (L*w))

theorem naturalGatherRows_eq_rhs {A s : ℕ} [NeZero s] (t band L w : ℕ)
    (C : ZMod s → GaussianInt) :
    naturalGatherRows (A := A) t band L w C =
      cstream A w ((List.range (naturalLengthGroup s t band L).length).flatMap
        (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C))) := by
  have hflat {K : Type} (xs : List ℕ) (F : ℕ → List K) :
      (List.range xs.length).flatMap (fun n => F (xs.getD n 0)) = xs.flatMap F := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [List.range_succ_eq_map, List.flatMap_map] using congrArg (F x ++ ·) ih
  unfold naturalGatherRows naturalSymbolOrigins naturalOrigins
  rw [List.flatMap_map, List.flatMap_map]
  rw [← hflat (naturalLengthGroup s t band L) (fun phase =>
    ((cstream A w (chirpLine s C)).drop (naturalStart s t band phase*w)).take (L*w))]
  simp only [cstream, List.flatMap_assoc]
  apply List.flatMap_congr
  intro n hn
  have hn' : n < (naturalLengthGroup s t band L).length := List.mem_range.mp hn
  have hmem := naturalGroupPhase_mem s t band L ⟨n, hn'⟩
  have hfit := naturalOrigins_fit s t band L (naturalStart s t band (naturalGroupPhase s t band L n))
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hw := ambientStream_window (A := A) w C
    (naturalStart s t band (naturalGroupPhase s t band L n)) L hfit
  change _ = cstream A w (cellSourceRows L (naturalGroupOrigin s t band L) (fun _ => C) n)
  simpa only [naturalGroupPhase, cstream, cellSourceRows, naturalGroupOrigin] using hw

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
