module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNaturalGather

/-! Forward symbol advances from retained coordinate origins. The emitted
packets, including the terminal zero advance, are the natural sweep's controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def originAdvances (w : ℕ) : ℕ → List ℕ → List ℕ
  | _, [] => []
  | previous, origin::origins => (origin-previous)*w :: originAdvances w origin origins

@[simp] theorem originAdvances_length (w previous : ℕ) (origins : List ℕ) :
    (originAdvances w previous origins).length = origins.length := by
  induction origins generalizing previous with
  | nil => rfl
  | cons origin origins ih => simp [originAdvances, ih]

theorem originAdvances_symbols (w previous : ℕ) (origins : List ℕ) :
    originAdvances w previous origins = originAdvances 1 (previous*w) (origins.map (·*w)) := by
  induction origins generalizing previous with
  | nil => rfl
  | cons origin origins ih => simp [originAdvances, Nat.sub_mul, ih]

theorem originAdvances_window (p : ℕ) (ps : List ℕ) :
    originAdvances 1 p ps ++ [0] = windowAdvances p ps := by
  induction ps generalizing p with
  | nil => rfl
  | cons q qs ih => simp [originAdvances, windowAdvances, ih]

theorem originAdvances_natControls (A s t band L w : ℕ)
    (hgroup : 0 < (naturalLengthGroup s t band L).length) :
    gatherControls A (originAdvances w 0 (naturalOrigins s t band L) ++ [0]) =
      naturalGatherControls A s t band L w := by
  rw [originAdvances_symbols]
  change gatherControls A (originAdvances 1 (0*w) (naturalSymbolOrigins s t band L w) ++ [0]) = _
  have hn : (naturalSymbolOrigins s t band L w).length > 0 := by
    simpa [naturalSymbolOrigins] using hgroup
  cases he : naturalSymbolOrigins s t band L w with
  | nil => simp [he] at hn
  | cons p ps => simp [naturalGatherControls, he, originAdvances, originAdvances_window]

/-- Conversion emits at most one ambient line's worth of unary ticks in total. -/
theorem originAdvances_sum_le (w previous bound : ℕ) (origins : List ℕ)
    (hsorted : (previous::origins).Pairwise (· ≤ ·)) (hp : previous ≤ bound)
    (hb : ∀ origin ∈ origins, origin ≤ bound) :
    previous*w+(originAdvances w previous origins).sum ≤ bound*w := by
  induction origins generalizing previous with
  | nil => simpa [originAdvances] using Nat.mul_le_mul_right w hp
  | cons origin origins ih =>
    obtain ⟨hle, htail⟩ := List.pairwise_cons.mp hsorted
    have hpo := hle origin (by simp)
    have hh := ih origin htail (hb origin (by simp)) (fun q hq => hb q (by simp [hq]))
    simpa [originAdvances, ← Nat.add_assoc, ← Nat.add_mul, Nat.add_sub_of_le hpo] using hh

theorem naturalOriginAdvances_volume (s t band L w : ℕ) :
    (originAdvances w 0 (naturalOrigins s t band L)).sum ≤ s*w := by
  have ho : (0::naturalOrigins s t band L).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp, naturalOrigins_ordered s t band L⟩
  simpa using originAdvances_sum_le w 0 s (naturalOrigins s t band L) ho (by omega)
    (fun origin horigin => by have hh := naturalOrigins_fit s t band L origin horigin; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
