module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpS1DimensionSetup

/-! # Exact unary S1 dimensions and their conversion cost -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

def chirpS1DimensionSlot : Fin 7 → Fin 10 := ![5, 4, 3, 6, 7, 8, 2]

def chirpS1DimensionCount (q t m w l : ℕ) : Fin 7 → ℕ :=
  ![q + 1, l, w, 3 * m + 1, 4 * m, chirpBlockCount t m, m]

/-- Every installed dimension has the exact value consumed by the shared caller. -/
theorem chirpS1Dimensions_at {T A : ℕ} (dst : Fin 7 → Fin T) (hdst : Function.Injective dst)
    (q t m w l : ℕ) (R : Regs T A) (i : Fin 7) :
    unaryCopiesR (chirpS1DimensionValues q t m w l) R (chirpS1Assignments dst) (dst i) =
      List.replicate (chirpS1DimensionCount q t m w l i) tick ++ R (dst i) := by
  have hnd : ((chirpS1Assignments dst).map Prod.snd).Nodup := by
    simp [chirpS1Assignments, List.nodup_cons, hdst.eq_iff]
  have hmem : (chirpS1DimensionSlot i, dst i) ∈ chirpS1Assignments dst := by
    fin_cases i <;> simp [chirpS1DimensionSlot, chirpS1Assignments]
  have hval : chirpS1DimensionValues q t m w l (chirpS1DimensionSlot i) =
      chirpS1DimensionCount q t m w l i := by
    fin_cases i <;> simp [chirpS1DimensionValues, chirpS1DimensionSlot, chirpS1DimensionCount]
  simpa only [hval] using unaryCopiesR_at (chirpS1DimensionValues q t m w l) R
    (chirpS1Assignments dst) hnd (chirpS1DimensionSlot i, dst i) hmem

/-- Registers outside the seven installed dimensions are retained. -/
theorem chirpS1Dimensions_off {T A : ℕ} (dst : Fin 7 → Fin T) (q t m w l : ℕ)
    (R : Regs T A) (k : Fin T) (hk : ∀ i, k ≠ dst i) :
    unaryCopiesR (chirpS1DimensionValues q t m w l) R (chirpS1Assignments dst) k = R k := by
  apply unaryCopiesR_off
  intro p hp
  simp only [chirpS1Assignments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact (hk 0).symm
  · exact (hk 1).symm
  · exact (hk 2).symm
  · exact (hk 3).symm
  · exact (hk 4).symm
  · exact (hk 5).symm
  · exact (hk 6).symm

/-- Conversion pays once per emitted tick and once per each of the seven dimensions. -/
theorem chirpS1Dimensions_cost {T : ℕ} (dst : Fin 7 → Fin T) (W q t m w l : ℕ) :
    unaryCopiesCost W (chirpS1DimensionValues q t m w l) (chirpS1Assignments dst) =
      6 * ((q + 1) + l + w + (3 * m + 1) + 4 * m + chirpBlockCount t m + m) +
        77 * W + 43 := by
  simp [unaryCopiesCost, chirpS1DimensionValues, chirpS1Assignments]
  ring

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
