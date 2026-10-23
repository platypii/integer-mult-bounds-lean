module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorArithmeticWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairLiveDescriptorBank
public import IntegerMultBounds.MathlibTM2.Routing.SelectiveCoordinates

/-! Logarithmic widths for complete canonical stages. One extra index bit
makes slot bounds strict and covers the entire physical record coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Layer.CompactGadget IntegerMultBounds.MathlibTM2.Layer.CompactDigits
noncomputable section

def canonicalScalarWidth (n : ℕ) : ℕ := Nat.clog 2 (n + 1)

theorem canonicalScalarWidth_fit (n : ℕ) : n < 2 ^ canonicalScalarWidth n :=
  (Nat.lt_succ_self n).trans_le (Nat.le_pow_clog (by decide) (n + 1))

def canonicalStageWidths (p : Par) : LiveDescriptorWidths :=
  let w := liveDescriptorArithmeticWidths p 0 repairLiveMode
  { indexBits := w.indexBits + 1, groupBits := w.groupBits, strideBits := w.strideBits,
    selectorBits := (w.indexBits + 1) + w.strideBits,
    widthBits := canonicalScalarWidth ((w.indexBits + 1) + w.strideBits) }

theorem canonicalStageWidths_selector (p : Par) :
    (canonicalStageWidths p).selectorBits = (canonicalStageWidths p).coordinateBits := rfl

theorem canonicalStageWidths_bounds (p : Par) (j : Fin 11) :
    LiveDescriptorBounds p 0 (canonicalStageWidths p) (repairLiveMode j) := by
  let w := liveDescriptorArithmeticWidths p 0 repairLiveMode
  have h := liveDescriptorArithmeticWidths_bounds p 0 repairLiveMode j
  have hc : w.coordinateBits ≤ (canonicalStageWidths p).coordinateBits := by
    dsimp [w, canonicalStageWidths, LiveDescriptorWidths.coordinateBits]; omega
  have hi : w.indexBits ≤ (canonicalStageWidths p).indexBits := Nat.le_succ _
  have hs : w.selectorBits ≤ (canonicalStageWidths p).selectorBits := by
    rw [liveDescriptorArithmeticWidths_selector]
    exact hc
  refine ⟨h.group_fits, h.stride_fits,
    h.coordinate_fits.trans_le (Nat.pow_le_pow_right (by decide) hc),
    h.group_width.trans hc, h.slots_fit.trans (Nat.pow_le_pow_right (by decide) hi),
    h.source_fits.trans_le (Nat.pow_le_pow_right (by decide) hs), ?_⟩
  exact canonicalScalarWidth_fit _

theorem canonicalStageWidths_key (p : Par) : p.K < 2 ^ (canonicalStageWidths p).strideBits := by
  exact (liveDescriptorArithmeticWidths_bounds p 0 repairLiveMode 1).stride_fits

theorem canonicalStageWidths_slots (p : Par) : p.n < 2 ^ (canonicalStageWidths p).indexBits := by
  have h := (liveDescriptorArithmeticWidths_bounds p 0 repairLiveMode 0).slots_fit
  have hp : 2 ^ (liveDescriptorArithmeticWidths p 0 repairLiveMode).indexBits <
      2 ^ ((liveDescriptorArithmeticWidths p 0 repairLiveMode).indexBits + 1) :=
    Nat.pow_lt_pow_right (by decide) (Nat.lt_succ_self _)
  exact h.trans_lt hp

theorem canonicalStageWidths_record (p : Par) :
    fieldsLen (selectiveLen p 0) < 2 ^ (canonicalStageWidths p).coordinateBits := by
  have h := (liveDescriptorArithmeticWidths_bounds p 0 repairLiveMode 0).source_fits
  have hsource : p.wy + 2 * p.wc + 0 + 1 <
      2 ^ (liveDescriptorArithmeticWidths p 0 repairLiveMode).coordinateBits := h
  have he : (canonicalStageWidths p).coordinateBits =
      (liveDescriptorArithmeticWidths p 0 repairLiveMode).coordinateBits + 1 := by
    dsimp [canonicalStageWidths, LiveDescriptorWidths.coordinateBits]; omega
  rw [he, pow_succ, selectiveFieldsLen]
  omega

theorem canonicalStageWidths_source (p : Par) :
    p.wy + 2 * p.wc + 0 < 2 ^ (canonicalStageWidths p).coordinateBits := by
  have h := canonicalStageWidths_record p
  rw [selectiveFieldsLen] at h
  omega

end
end IntegerMultBounds.MathlibTM2.Routing
