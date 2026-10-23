module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicSetup
public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicExec
public import IntegerMultBounds.MathlibTM2.Mult.ChirpGatherSetup
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! # One shared layout for raw-line chirp gathering -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

inductive ChirpRawReg where
  | counter (i : Fin 5)
  | raw | dst | extension | count | saved | control | advance | acc | current
  | savedSource | buf | tmp | front | back | expanded
  deriving DecidableEq

def chirpRawCounters {T : ℕ} (r : ChirpRawReg → Fin T) (i : Fin 5) : Fin T := r (.counter i)

def chirpRawCyclicRoles : List ChirpRawReg :=
  [.counter 0, .counter 1, .counter 2, .saved, .counter 3, .raw, .front, .back,
    .acc, .expanded, .extension, .buf, .tmp]

def chirpRawSweepRoles : List ChirpRawReg :=
  [.dst, .control, .saved, .advance, .counter 4, .extension, .acc, .current, .savedSource, .buf, .tmp, .count]

def chirpRawClearRoles : List ChirpRawReg :=
  [.counter 0, .counter 1, .counter 2, .counter 3, .counter 4, .extension]

theorem chirpRawCyclicRoles_nodup : chirpRawCyclicRoles.Nodup := by decide +kernel

theorem chirpRawSweepRoles_nodup : chirpRawSweepRoles.Nodup := by decide +kernel

theorem chirpRawClearRoles_nodup : chirpRawClearRoles.Nodup := by decide +kernel

theorem chirpRawCounters_injective {T : ℕ} {r : ChirpRawReg → Fin T} (hr : Function.Injective r) :
    Function.Injective (chirpRawCounters r) := fun _ _ h => ChirpRawReg.counter.inj (hr h)

theorem chirpRawClearRoles_mem (q : ChirpRawReg) :
    q ∈ chirpRawClearRoles ↔ (∃ i, q = .counter i) ∨ q = .extension := by
  constructor
  · intro h
    simp only [chirpRawClearRoles, List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl | rfl
    · exact Or.inl ⟨0, rfl⟩
    · exact Or.inl ⟨1, rfl⟩
    · exact Or.inl ⟨2, rfl⟩
    · exact Or.inl ⟨3, rfl⟩
    · exact Or.inl ⟨4, rfl⟩
    · exact Or.inr rfl
  · rintro (⟨i, rfl⟩ | rfl)
    · fin_cases i <;> simp [chirpRawClearRoles]
    · simp [chirpRawClearRoles]

def chirpRawSetupCost (W e s m w : ℕ) : ℕ :=
  25 * tblC W e + (4 * W + 2) * chirpCyclicCounterTotal s m w + 55 * W + 31

def chirpRawCopyCost (s m w : ℕ) : ℕ :=
  chirpPeriods s m * (8 * (s * w) + 9) + 10 * ((s + 3 * m) * w) + 10 * (s * w) + 38

def chirpRawSweepCost (W e s t m w M : ℕ) : ℕ :=
  M * (6 * tblC W e + 11 * W + 14 * ((3 * m + 1) * w) + 41) +
    (4 * W + 18) * (chirpCenter s t m M * w) + 6 * tblC W e + 16

def chirpRawGatherCost (W e s t m w M : ℕ) : ℕ :=
  chirpRawSetupCost W e s m w + chirpRawCopyCost s m w + chirpRawSweepCost W e s t m w M +
    (2 * (chirpCyclicCounterTotal s m w + (s + 3 * m) * w) + 13)

/-- The five generated words have total size `K`, including both rotation intervals. -/
theorem chirpCyclicCount_sum {s : ℕ} (hs : 0 < s) (m w : ℕ) :
    [chirpCyclicCount s m w 0, chirpCyclicCount s m w 1, chirpCyclicCount s m w 2,
      chirpCyclicCount s m w 3, chirpCyclicCount s m w 4].sum = chirpCyclicCounterTotal s m w := by
  have hrot : chirpOffset s m * w + (s - chirpOffset s m) * w = s * w := by
    rw [← Nat.add_mul, Nat.add_sub_of_le (chirpOffset_lt hs m).le]
  simp [chirpCyclicCount, chirpCyclicCounterTotal]
  omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
