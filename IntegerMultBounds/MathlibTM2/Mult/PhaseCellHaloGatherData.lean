module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherData
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Fast.ResampASem

/-! A physical slice of the ambient line is the solver's original-coordinate
RHS row. Concatenating natural windows therefore constructs its exact batch ABI. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.ResampA
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloGatherRows {A s : ℕ} (t band a b L w : ℕ) (C : ZMod s → GaussianInt) : List (Fin (A+4)) :=
  (haloSymbolOrigins s t band a b L w).flatMap
    (fun p => ((cstream A w (chirpLine s C)).drop p).take (L*w))

theorem haloGatherRows_eq_rhs {A s : ℕ} [NeZero s] (t band a b L w : ℕ)
    (C : ZMod s → GaussianInt) :
    haloGatherRows (A := A) t band a b L w C =
      cstream A w ((List.range (haloLengthGroup s t band a b L).length).flatMap
        (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C))) := by
  have hflat {K : Type} (xs : List ℕ) (F : ℕ → List K) :
      (List.range xs.length).flatMap (fun n => F (xs.getD n 0)) = xs.flatMap F := by
    induction xs with
    | nil => simp
    | cons x xs ih => simpa [List.range_succ_eq_map, List.flatMap_map] using congrArg (F x ++ ·) ih
  unfold haloGatherRows haloSymbolOrigins haloOrigins
  rw [List.flatMap_map, List.flatMap_map]
  rw [← hflat (haloLengthGroup s t band a b L) (fun phase =>
    ((cstream A w (chirpLine s C)).drop (haloStart s t band a phase*w)).take (L*w))]
  simp only [cstream, List.flatMap_assoc]
  apply List.flatMap_congr
  intro n hn
  have hn' : n < (haloLengthGroup s t band a b L).length := List.mem_range.mp hn
  have hmem := haloGroupPhase_mem s t band a b L ⟨n, hn'⟩
  have hfit := haloOrigins_fit s t band a b L (haloStart s t band a (haloGroupPhase s t band a b L n))
    (List.mem_map.mpr ⟨_, hmem, rfl⟩)
  have hw := ambientStream_window (A := A) w C
    (haloStart s t band a (haloGroupPhase s t band a b L n)) L hfit
  change _ = cstream A w (cellSourceRows L (haloGroupOrigin s t band a b L) (fun _ => C) n)
  simpa only [haloGroupPhase, cstream, cellSourceRows, haloGroupOrigin] using hw

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
