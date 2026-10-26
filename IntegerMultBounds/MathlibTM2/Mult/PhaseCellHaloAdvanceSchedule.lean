module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloGather

/-! The halo origin converter emits the restoring sweep's exact controls. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem originAdvances_haloControls (A s t band a b L w : ℕ)
    (hgroup : 0 < (haloLengthGroup s t band a b L).length) :
    gatherControls A (originAdvances w 0 (haloOrigins s t band a b L) ++ [0]) =
      haloGatherControls A s t band a b L w := by
  rw [originAdvances_symbols]
  change gatherControls A (originAdvances 1 (0*w) (haloSymbolOrigins s t band a b L w) ++ [0]) = _
  have hn : (haloSymbolOrigins s t band a b L w).length > 0 := by
    simpa [haloSymbolOrigins] using hgroup
  cases he : haloSymbolOrigins s t band a b L w with
  | nil => simp [he] at hn
  | cons p ps => simp [haloGatherControls, he, originAdvances, originAdvances_window]

theorem haloOriginAdvances_volume (s t band a b L w : ℕ) :
    (originAdvances w 0 (haloOrigins s t band a b L)).sum ≤ s*w := by
  have ho : (0::haloOrigins s t band a b L).Pairwise (· ≤ ·) :=
    List.pairwise_cons.mpr ⟨by simp, haloOrigins_ordered s t band a b L⟩
  simpa using originAdvances_sum_le w 0 s (haloOrigins s t band a b L) ho (by omega)
    (fun origin horigin => by have hh := haloOrigins_fit s t band a b L origin horigin; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
