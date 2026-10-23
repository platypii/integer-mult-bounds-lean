module

public import IntegerMultBounds.MathlibTM2.Routing.LiveDescriptorCanonicalWidths

/-! Logarithmic widths whose selector width equals the affine arithmetic width.
This permits direct profile generation without a word-width conversion pass. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.MathlibTM2.Layer.CompactGadget

noncomputable section

def liveDescriptorArithmeticWidths {J : ℕ} (p : Par) (X : ℕ) (mode : Fin J → LiveDescriptorMode) : LiveDescriptorWidths :=
  let w := liveDescriptorCanonicalWidths p X mode
  { w with selectorBits := w.coordinateBits, widthBits := Nat.clog 2 (w.coordinateBits + 1) }

theorem liveDescriptorArithmeticWidths_selector {J : ℕ} (p : Par) (X : ℕ) (mode : Fin J → LiveDescriptorMode) :
    (liveDescriptorArithmeticWidths p X mode).selectorBits = (liveDescriptorArithmeticWidths p X mode).coordinateBits := rfl

theorem liveDescriptorArithmeticWidths_bounds {J : ℕ} (p : Par) (X : ℕ)
    (mode : Fin J → LiveDescriptorMode) (j : Fin J) :
    LiveDescriptorBounds p X (liveDescriptorArithmeticWidths p X mode) (mode j) := by
  let w := liveDescriptorCanonicalWidths p X mode
  have h := liveDescriptorCanonicalWidths_bounds p X mode j
  have hle : w.selectorBits ≤ w.coordinateBits := by
    dsimp [w, liveDescriptorCanonicalWidths, LiveDescriptorWidths.coordinateBits]
    omega
  have hsource : repairCompactSourceWidth p X (mode j).key + 1 < 2 ^ w.coordinateBits :=
    h.source_fits.trans_le (Nat.pow_le_pow_right (by decide) hle)
  have hwidth : w.coordinateBits < 2 ^ Nat.clog 2 (w.coordinateBits + 1) :=
    lt_of_lt_of_le (Nat.lt_succ_self _) (Nat.le_pow_clog (by decide) _)
  exact ⟨h.group_fits, h.stride_fits, h.coordinate_fits, h.group_width, h.slots_fit, hsource, hwidth⟩

theorem liveDescriptorArithmeticBank_ready {N J A : ℕ} (p : Par) (X : ℕ)
    (hG : 0 < p.G) (hK : 0 < p.K) (active : Fin p.n → Bool)
    (s : Fin p.n → SlotSource p X) (mode : Fin J → LiveDescriptorMode)
    (core : Fin N → List (Fin (A + 4))) :
    LiveDescriptorReady p X hG hK active s mode (liveDescriptorArithmeticWidths p X mode)
      (liveDescriptorBank core (liveDescriptorData p X hG hK active s mode
        (liveDescriptorArithmeticWidths p X mode))) :=
  liveDescriptorBank_ready p X hG hK active s mode _ core (liveDescriptorArithmeticWidths_bounds p X mode)

end
end IntegerMultBounds.MathlibTM2.Routing
