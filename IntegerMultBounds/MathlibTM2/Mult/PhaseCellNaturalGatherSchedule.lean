module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherSchedule
public import IntegerMultBounds.NLogN.PhaseCellNaturalGroups

/-! Natural equal-length groups are ordered windows in the original ambient
line, so their forward differences admit one paid source sweep. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem naturalStart_mono (s t band : ℕ) : Monotone (naturalStart s t band) := by
  intro p q hpq
  unfold naturalStart phaseLower
  apply Nat.add_le_add_right
  apply Nat.div_le_div_right
  exact Nat.sub_le_sub_right (Nat.sub_le_sub_right
    (Nat.add_le_add_right (Nat.mul_le_mul_left (2*s) hpq) (2*(t-s))) 1) s

def naturalOrigins (s t band L : ℕ) : List ℕ :=
  (naturalLengthGroup s t band L).map (naturalStart s t band)

@[simp] theorem naturalOrigins_length (s t band L : ℕ) :
    (naturalOrigins s t band L).length = (naturalLengthGroup s t band L).length := by
  simp [naturalOrigins]

theorem naturalOrigins_ordered (s t band L : ℕ) :
    (naturalOrigins s t band L).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  have hh : (naturalLengthGroup s t band L).Pairwise (· ≤ ·) :=
    List.Pairwise.filter _ List.pairwise_le_range
  exact hh.imp (fun hpq => naturalStart_mono s t band hpq)

theorem naturalOrigins_fit (s t band L : ℕ) :
    ∀ p ∈ naturalOrigins s t band L, p+L ≤ s := by
  intro p hp
  obtain ⟨phase, hphase, rfl⟩ := List.mem_map.mp hp
  obtain ⟨_, hL, he⟩ := (mem_naturalLengthGroup s t band L phase).mp hphase
  have hlt := (naturalLength_pos_iff s t band phase).mp (show 0 < naturalLength s t band phase by omega)
  have hh := naturalStop_le s t band phase
  unfold naturalLength at he
  omega

end IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def naturalSymbolOrigins (s t band L w : ℕ) : List ℕ :=
  (naturalOrigins s t band L).map (·*w)

theorem naturalSymbolOrigins_ordered (s t band L w : ℕ) :
    (naturalSymbolOrigins s t band L w).Pairwise (· ≤ ·) := by
  apply List.pairwise_map.mpr
  exact (naturalOrigins_ordered s t band L).imp (fun h => Nat.mul_le_mul_right w h)

theorem naturalSymbolOrigins_fit (s t band L w : ℕ) :
    ∀ p ∈ naturalSymbolOrigins s t band L w, p+L*w ≤ s*w := by
  intro p hp
  obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
  simpa only [Nat.add_mul] using Nat.mul_le_mul_right w (naturalOrigins_fit s t band L q hq)

/-- The sweep's source movement never exceeds one encoded ambient line. -/
theorem naturalGather_volume (s t band L w p : ℕ) (ps : List ℕ)
    (hps : naturalSymbolOrigins s t band L w = p::ps) :
    p+(windowAdvances p ps).sum ≤ s*w := by
  have ho := naturalSymbolOrigins_ordered s t band L w
  have hf := naturalSymbolOrigins_fit s t band L w
  rw [hps] at ho hf
  let E : List (Fin 4) := List.replicate (s*w) 0
  simpa [E] using windowAdvances_volume (L*w) p ps E ho (by simpa [E] using hf)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
