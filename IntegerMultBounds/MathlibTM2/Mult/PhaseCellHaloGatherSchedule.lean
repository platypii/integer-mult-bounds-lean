module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGatherSchedule
public import IntegerMultBounds.NLogN.PhaseCellHaloGroups

/-! Clipped equal-length groups are ordered windows in the original ambient
line, so their forward differences permit one paid source sweep. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem haloStart_mono (s t band a : ℕ) : Monotone (haloStart s t band a) := by
  intro p q hpq
  exact max_le_max (naturalStart_mono s t band hpq) le_rfl

def haloOrigins (s t band a b L : ℕ) : List ℕ :=
  (haloLengthGroup s t band a b L).map (haloStart s t band a)

@[simp] theorem haloOrigins_length (s t band a b L : ℕ) :
    (haloOrigins s t band a b L).length = (haloLengthGroup s t band a b L).length := by
  simp [haloOrigins]

theorem haloOrigins_ordered (s t band a b L : ℕ) :
    (haloOrigins s t band a b L).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  have hh : (haloLengthGroup s t band a b L).Pairwise (· ≤ ·) :=
    List.Pairwise.filter _ List.pairwise_le_range
  exact hh.imp (fun hpq => haloStart_mono s t band a hpq)

theorem haloOrigins_fit (s t band a b L : ℕ) :
    ∀ p ∈ haloOrigins s t band a b L, p+L ≤ s := by
  intro p hp
  obtain ⟨phase, hphase, rfl⟩ := List.mem_map.mp hp
  obtain ⟨_, hL, he⟩ := (mem_haloLengthGroup s t band a b L phase).mp hphase
  have hh := haloStop_le s t band b phase
  unfold haloLength at he
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def haloSymbolOrigins (s t band a b L w : ℕ) : List ℕ :=
  (haloOrigins s t band a b L).map (·*w)

theorem haloSymbolOrigins_ordered (s t band a b L w : ℕ) :
    (haloSymbolOrigins s t band a b L w).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  exact (haloOrigins_ordered s t band a b L).imp (fun h => Nat.mul_le_mul_right w h)

theorem haloSymbolOrigins_fit (s t band a b L w : ℕ) :
    ∀ p ∈ haloSymbolOrigins s t band a b L w, p+L*w ≤ s*w := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (haloOrigins_fit s t band a b L q hq)

/-- The sweep's source movement never exceeds one encoded ambient line. -/
theorem haloGather_volume (s t band a b L w p : ℕ) (ps : List ℕ)
    (hps : haloSymbolOrigins s t band a b L w = p::ps) :
    p+(windowAdvances p ps).sum ≤ s*w := by
  have ho := haloSymbolOrigins_ordered s t band a b L w
  have hf := haloSymbolOrigins_fit s t band a b L w
  rw [hps] at ho hf
  let E : List (Fin 4) := List.replicate (s*w) 0
  simpa [E] using windowAdvances_volume (L*w) p ps E ho (by simpa [E] using hf)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
