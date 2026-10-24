module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalLiveInput
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStageWidths

/-! Eleven repair descriptors share eleven scalar values. The static selection
map separates scalar arithmetic from repeated descriptor-bank installation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
noncomputable section

def repairDescriptorScalarPalette (p : Par) : Fin 11 → ℕ :=
  ![p.K,p.G,p.ρ,p.ρ + 1,0,p.wy,p.wc,p.wy - 1,p.wc - 1,2 * p.wc + 1,p.wy + 2 * p.wc + 1]

/-- Fields are stride, base, last row, row count and source width. -/
def repairDescriptorScalarSlot (j : Fin 11) : Fin 5 → Fin 11 :=
  ![(if j.val ≤ 4 then 0 else 1),
    (if j.val = 0 ∨ j.val = 3 ∨ j.val = 4 then 2 else if j.val ≤ 2 then 3 else 4),
    (if j.val ≤ 4 then 7 else 8), (if j.val ≤ 4 then 5 else 6),
    (if 1 ≤ j.val ∧ j.val ≤ 4 then 9 else 10)]

def repairDescriptorScalarValues (p : Par) (j : Fin 11) : Fin 5 → ℕ :=
  ![(repairLiveMode j).stride p, (repairLiveMode j).base p,
    repairCompactRows p (repairLiveMode j).key - 1,
    repairCompactRows p (repairLiveMode j).key,
    repairCompactSourceWidth p 0 (repairLiveMode j).key + 1]

theorem repairDescriptorScalarPalette_exact (p : Par) (j : Fin 11) (field : Fin 5) :
    repairDescriptorScalarPalette p (repairDescriptorScalarSlot j field) =
      repairDescriptorScalarValues p j field := by
  fin_cases j <;> fin_cases field <;>
    simp [repairDescriptorScalarPalette, repairDescriptorScalarSlot, repairDescriptorScalarValues,
      repairLiveMode, repairDescriptorKey, LiveDescriptorMode.ofKey, LiveDescriptorMode.stride,
      LiveDescriptorMode.base, LiveDescriptorMode.key, repairAffineStride, repairAffineOffset,
      repairCompactRows, repairCompactSourceWidth, selectiveTargetWidth, selectiveSourceWidth]

/-- The three coordinate operands share their output encoding width. -/
def repairDescriptorScalarWidth (w : LiveDescriptorWidths) : Fin 5 → ℕ :=
  ![w.strideBits,w.coordinateBits,w.coordinateBits,w.coordinateBits,w.selectorBits]

theorem repairDescriptorScalarPalette_words {A : ℕ} (p : Par) (w : LiveDescriptorWidths)
    (j : Fin 11) (field : Fin 5) :
    (binSyms (repairDescriptorScalarWidth w field)
      (repairDescriptorScalarPalette p (repairDescriptorScalarSlot j field)) : List (Fin (A + 4))) =
      binSyms (repairDescriptorScalarWidth w field) (repairDescriptorScalarValues p j field) := by
  rw [repairDescriptorScalarPalette_exact]

/-- The canonical coordinate encoding holds every shared scalar, including the
empty-row-safe predecessor and successor operands. -/
theorem repairDescriptorScalarPalette_fit (p : Par) (hρ : p.ρ < p.K) (j : Fin 11) :
    repairDescriptorScalarPalette p j < 2 ^ (canonicalStageWidths p).coordinateBits := by
  have hb := canonicalStageWidths_bounds p 0
  have hsource := hb.source_fits
  change p.wy + 2 * p.wc + 0 + 1 < 2 ^ (canonicalStageWidths p).selectorBits at hsource
  rw [canonicalStageWidths_selector] at hsource
  have hstride : (canonicalStageWidths p).strideBits ≤ (canonicalStageWidths p).coordinateBits := by
    change (canonicalStageWidths p).strideBits ≤
      (canonicalStageWidths p).indexBits + (canonicalStageWidths p).strideBits
    omega
  have hkey := (canonicalStageWidths_key p).trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hstride)
  have hgroup := hb.group_fits.trans_le (Nat.pow_le_pow_right (by decide : 1 ≤ 2) hb.group_width)
  fin_cases j <;> simp [repairDescriptorScalarPalette] <;> omega

end
end IntegerMultBounds.MathlibTM2.Routing
