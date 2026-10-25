module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicArgs
public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies

/-! # The five generated cyclic-source counters and their total conversion cost -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM

def chirpCyclicAssignments {T : ℕ} (dst : Fin 5 → Fin T) : List (Fin 10 × Fin T) :=
  [(4, dst 0), (5, dst 1), (6, dst 2), (7, dst 3), (9, dst 4)]

/-- Only the five selected slots are read by the conversion list. -/
def chirpCyclicValues (s m w : ℕ) : Fin 10 → ℕ :=
  ![0, 0, 0, 0, chirpOffset s m * w, (s - chirpOffset s m) * w,
    chirpPeriods s m, (s + 3 * m) * w, 0, (3 * m + 1) * w]

def chirpCyclicCounterTotal (s m w : ℕ) : ℕ :=
  s * w + chirpPeriods s m + (s + 3 * m) * w + (3 * m + 1) * w

theorem chirpCyclicValues_slot (s m w : ℕ) (i : Fin 5) :
    chirpCyclicValues s m w (chirpCyclicSlot i) = chirpCyclicCount s m w i := by
  fin_cases i <;> simp [chirpCyclicValues, chirpCyclicSlot, chirpCyclicCount]

theorem chirpCyclicAssignments_mem {T : ℕ} (dst : Fin 5 → Fin T) (p : Fin 10 × Fin T) :
    p ∈ chirpCyclicAssignments dst ↔ ∃ i, p = (chirpCyclicSlot i, dst i) := by
  constructor
  · intro hp
    simp only [chirpCyclicAssignments, List.mem_cons, List.not_mem_nil, or_false] at hp
    rcases hp with rfl | rfl | rfl | rfl | rfl
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩
    · exact ⟨2, rfl⟩
    · exact ⟨3, rfl⟩
    · exact ⟨4, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [chirpCyclicSlot, chirpCyclicAssignments]

theorem chirpCyclicAssignments_values {T : ℕ} (dst : Fin 5 → Fin T) (s m w : ℕ)
    (σ : Fin 10 → ℕ) (hv : ∀ i, σ (chirpCyclicSlot i) = chirpCyclicCount s m w i) :
    ∀ p ∈ chirpCyclicAssignments dst, σ p.1 = chirpCyclicValues s m w p.1 := by
  intro p hp
  obtain ⟨i, rfl⟩ := (chirpCyclicAssignments_mem dst p).mp hp
  exact (hv i).trans (chirpCyclicValues_slot s m w i).symm

/-- Each distinct destination gains its designated counter, with arbitrary spectator suffixes. -/
theorem chirpCyclicCounters_at {T A : ℕ} (dst : Fin 5 → Fin T) (hdst : Function.Injective dst)
    (R : Regs T A) (s m w : ℕ) (i : Fin 5) :
    unaryCopiesR (chirpCyclicValues s m w) R (chirpCyclicAssignments dst) (dst i) =
      List.replicate (chirpCyclicCount s m w i) tick ++ R (dst i) := by
  have hnd : ((chirpCyclicAssignments dst).map Prod.snd).Nodup := by
    simp [chirpCyclicAssignments, hdst.eq_iff]
  have hp := (chirpCyclicAssignments_mem dst (chirpCyclicSlot i, dst i)).mpr ⟨i, rfl⟩
  simpa only [chirpCyclicValues_slot] using unaryCopiesR_at (chirpCyclicValues s m w) R _ hnd
    (chirpCyclicSlot i, dst i) hp

/-- Sum the actual count sizes; the two rotation intervals together have length `sw`. -/
theorem chirpCyclicCounters_cost {T : ℕ} (dst : Fin 5 → Fin T) (W s m w : ℕ) (hs : 0 < s)
    (σ : Fin 10 → ℕ) (hv : ∀ i, σ (chirpCyclicSlot i) = chirpCyclicCount s m w i) :
    unaryCopiesCost W σ (chirpCyclicAssignments dst) =
      6 * chirpCyclicCounterTotal s m w + 55 * W + 31 := by
  have h4 : σ 4 = chirpOffset s m * w := hv 0
  have h5 : σ 5 = (s - chirpOffset s m) * w := hv 1
  have h6 : σ 6 = chirpPeriods s m := hv 2
  have h7 : σ 7 = (s + 3 * m) * w := hv 3
  have h9 : σ 9 = (3 * m + 1) * w := hv 4
  have hrot : chirpOffset s m * w + (s - chirpOffset s m) * w = s * w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (chirpOffset_lt hs m).le]
  simp only [unaryCopiesCost, chirpCyclicAssignments, List.map_cons, List.map_nil,
    List.sum_cons, List.sum_nil, h4, h5, h6, h7, h9]
  calc _ = 6 * (chirpOffset s m * w + (s - chirpOffset s m) * w +
      chirpPeriods s m + (s + 3 * m) * w + (3 * m + 1) * w) + 55 * W + 31 := by ring
    _ = _ := by rw [hrot]; rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
