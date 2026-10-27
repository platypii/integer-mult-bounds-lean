module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryGuardCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellZeroCouplingRow

/-! Computed guards certify a zero source window in either coupling direction. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingZeroRows (boundary : Bool) (s t band a b : ℕ) [NeZero s] : Finset (ZMod s) :=
  if boundary then recoveryZeroRows s t band a b else haloExterior s band a b

theorem recoveryGuardMaskAt_spec {s t : ℕ} [NeZero s] (hst : s < t)
    (boundary : Bool) (band a b i : ℕ) (hb : b ≤ s) (hi : i < s) :
    recoveryGuardMaskAt boundary s t (2*band) a b i = true ↔
      (i : ZMod s) ∈ couplingZeroRows boundary s t band a b := by
  have hdiv : 2*band/2 = band := by omega
  have hdeep := haloInteriorAt_spec hst (2*band) a b i hb hi
  cases boundary <;>
    simp [recoveryGuardMaskAt,couplingZeroRows,recoveryZeroRows,haloExterior,
      hdiv,ZMod.val_cast_of_lt hi,hdeep]

theorem couplingZeroRows_stencil_disjoint {s t : ℕ} [NeZero s] (hst : s ≤ t)
    (boundary : Bool) (band a b i : ℕ) (hi : (i : ZMod s) ∈ couplingZeroRows boundary s t band a b)
    {δ : ℤ} (hδ : δ ∈ spatialCouplingOffsets band) :
    (i : ZMod s)+(δ : ZMod s) ∉
      (if boundary then haloBoundary s t band a b else haloInterior s t band a b) := by
  cases boundary with
  | true => exact recoveryZeroRows_stencil_disjoint hst band a b _ hi hδ
  | false =>
    exact fun h => haloExterior_stencil_disjoint band a b _ hi hδ
      (haloInterior_subset s t band a b h)

theorem spatialCouplingInputWords_zero_window {s : ℕ} [NeZero s]
    (boundary : Bool) (t band a b i : ℕ) (C : ZMod s → GaussianInt)
    (hzero : ∀ δ ∈ spatialCouplingOffsets band, (i : ZMod s)+(δ : ZMod s) ∉
      (if boundary then haloBoundary s t band a b else haloInterior s t band a b)) :
    spatialCouplingInputWords boundary t band a b i C = List.replicate (2*band+1) 0 := by
  have hz : ∀ δ ∈ spatialCouplingOffsets band,
      (if (i : ZMod s)+(δ : ZMod s) ∈ (if boundary then haloBoundary s t band a b else haloInterior s t band a b)
        then C ((i : ZMod s)+(δ : ZMod s)) else 0) = 0 := by intro δ hδ; simp [hzero δ hδ]
  dsimp only [spatialCouplingInputWords]
  rw [List.map_congr_left hz]
  simp

theorem couplingRowWord_zero_window {s : ℕ} [NeZero s]
    (P q t u band a b i : ℕ) (boundary : Bool) (C : ZMod s → GaussianInt) (rhs : GaussianInt)
    (hzero : ∀ δ ∈ spatialCouplingOffsets band, (i : ZMod s)+(δ : ZMod s) ∉
      (if boundary then haloBoundary s t band a b else haloInterior s t band a b)) :
    couplingRowWord P q t u band a b i boundary C rhs = rhs := by
  rw [← couplingRowWord_spatial,spatialCouplingInputWords_zero_window boundary t band a b i C hzero]
  rw [coupling_dot_zero q _ _ (by intro x hx; simpa using (List.eq_of_mem_replicate hx))]
  simp

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
