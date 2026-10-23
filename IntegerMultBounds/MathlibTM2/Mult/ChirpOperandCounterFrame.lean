module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpOperandCountSetup

/-! # Frames and exact values of generated operand counters -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

/-- Coordinates of the three geometry counters in their conversion order. -/
def chirpOperandCount (t m w : ℕ) : Fin 3 → ℕ :=
  ![chirpBlockCount t m, 3 * m + 1, (3 * m + 1) * w]

/-- Counter generation leaves every other right stack unchanged. -/
theorem chirpOperandCounters_off {T A : ℕ} (dst : Fin 3 → Fin T) (t m w : ℕ)
    (R : Regs T A) (k : Fin T) (hk : ∀ i, k ≠ dst i) :
    unaryCopiesR (chirpOperandCountValues t m w) R (chirpOperandAssignments dst) k = R k := by
  apply unaryCopiesR_off
  intro p hp
  simp only [chirpOperandAssignments, List.mem_cons, List.not_mem_nil, or_false] at hp
  rcases hp with rfl | rfl | rfl
  · exact (hk 0).symm
  · exact (hk 1).symm
  · exact (hk 2).symm

/-- Each distinct destination receives exactly its generated numeral. -/
theorem chirpOperandCounters_at {T A : ℕ} (dst : Fin 3 → Fin T) (hdst : Function.Injective dst)
    (t m w : ℕ) (R : Regs T A) (i : Fin 3) :
    unaryCopiesR (chirpOperandCountValues t m w) R (chirpOperandAssignments dst) (dst i) =
      List.replicate (chirpOperandCount t m w i) tick ++ R (dst i) := by
  have hnd : ((chirpOperandAssignments dst).map Prod.snd).Nodup := by
    simp [chirpOperandAssignments, List.nodup_cons, hdst.eq_iff]
  fin_cases i
  all_goals
    first
    | simpa [chirpOperandCountValues, chirpOperandCount] using
        unaryCopiesR_at (chirpOperandCountValues t m w) R (chirpOperandAssignments dst) hnd
          (4, dst 0) (by simp [chirpOperandAssignments])
    | simpa [chirpOperandCountValues, chirpOperandCount] using
        unaryCopiesR_at (chirpOperandCountValues t m w) R (chirpOperandAssignments dst) hnd
          (5, dst 1) (by simp [chirpOperandAssignments])
    | simpa [chirpOperandCountValues, chirpOperandCount] using
        unaryCopiesR_at (chirpOperandCountValues t m w) R (chirpOperandAssignments dst) hnd
          (6, dst 2) (by simp [chirpOperandAssignments])

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
