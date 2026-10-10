import IntegerMultBounds.Machine.NativePolynomialStageShape
import IntegerMultBounds.Machine.CompactActualStageRuntime
import IntegerMultBounds.Machine.ActivePrefixStagePairData

/-! The real polynomial codec, rather than the reservation's one-symbol
payload, pays packed repair for every pair in a native phase basis word.
Original multiplier geometry and descendant row padding discharge readiness
and both repair densities at constant one. The stored signed-width allowance
remains an explicit scalar contract until controller propagation is assembled. -/
namespace IntegerMultBounds.Machine.CompactNativePolynomialStagePacked
noncomputable section
open Sizes
open CompactActualStageAllowance CompactActualStageGeometry CompactActualStageInputs
open CompactGlobalRowPadding CompactReservationCutoff
open ActivePrefixStageParameters (Stage)

/-- Expanding an actual reservation changes only its literal payload capacity. -/
theorem expanded_shape (n c m D ell p : ℕ) :
    NativePolynomialStageShape.shape (actualShape n c m D 1) ell p =
      actualShape n c m D (NativePolynomialStageShape.payload (actualShape n c m D 1) ell p) := rfl

/-- The genuine complete polynomial serialization pays the actual scalar
payload allowance as soon as its stored signed width covers the scalar bits. -/
theorem payload_allowance (n c m D p : ℕ)
    (hw : b n ≤ NativePolynomialStageShape.width (actualShape n c m D 1) p) :
    6*b n*2^ℓ n ≤ NativePolynomialStageShape.payload (actualShape n c m D 1) (ℓ n) p := by
  unfold NativePolynomialStageShape.payload ActivePrefixStageNativePolynomial.symbols
  nlinarith [Nat.zero_le (2^ℓ n)]

/-- All literal distinct-pair instructions receive actual packed readiness,
including rewritten source/target descriptors. No per-pair repair allowance
or density premise is supplied. -/
theorem eventually_packed (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D j p : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D 1))
      (_hw : b n≤NativePolynomialStageShape.width (actualShape n c m D 1) p)
      (hG : 1≤(actualShape n c m D 1).guard)
      (hGK : (actualShape n c m D 1).guard+1≤(actualShape n c m D 1).chunk)
      (hr : 0<rowsAt c m (d n) (K n) j),
      let input := NativePolynomialStageShape.inputs v (rowsAt c m (d n) (K n) j) (ℓ n) p hG hGK hr
      ∀ op, ActivePrefixStageRuntimeData.Packed (ActivePrefixStagePairData.changePair input op) 1 := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    CompactActualStageRuntime.eventually_packed c m hc hm] with n hready hpacked
  intro D j p hcut hD hj v hw hG hGK hr
  dsimp only
  intro op
  let capacity := NativePolynomialStageShape.payload (actualShape n c m D 1) (ℓ n) p
  have hpay : 6*b n*2^ℓ n≤capacity := payload_allowance n c m D p hw
  let expanded : Stage (actualShape n c m D capacity) := NativePolynomialStageShape.stage v (ℓ n) p
  let paired : Stage (actualShape n c m D capacity) :=
    {expanded with source:=op.source, target:=op.target, distinct:=op.distinct.symm}
  let h := hready D capacity j hcut hD hpay hj paired
  exact hpacked D capacity j hcut hD hpay paired h

/-- Original geometry also supplies positive descendant rows and guard room.
The only scalar contract here is the genuine stored-width allowance. -/
theorem eventually_ready_packed (c m : ℕ) (hc : 2≤c) (hm : 2≤m) :
    ∀ᶠ n : ℕ in Filter.atTop,
    ∀ (D j p : ℕ) (_hcut : cutoff c m n≤D) (_hD : D≤d n)
      (_hj : j≤depth m (d n))
      (v : Stage (actualShape n c m D 1))
      (_hw : b n≤NativePolynomialStageShape.width (actualShape n c m D 1) p),
      ∃ (hG : 1≤(actualShape n c m D 1).guard)
        (hGK : (actualShape n c m D 1).guard+1≤(actualShape n c m D 1).chunk)
        (hr : 0<rowsAt c m (d n) (K n) j),
        ∀ op, ActivePrefixStageRuntimeData.Packed
          (ActivePrefixStagePairData.changePair
            (NativePolynomialStageShape.inputs v (rowsAt c m (d n) (K n) j) (ℓ n) p hG hGK hr) op) 1 := by
  filter_upwards [CompactActualStageGeometry.eventually_ready c m hc hm,
    eventually_packed c m hc hm] with n hready hpacked
  intro D j p hcut hD hj v hw
  let capacity := NativePolynomialStageShape.payload (actualShape n c m D 1) (ℓ n) p
  have hpay : 6*b n*2^ℓ n≤capacity := payload_allowance n c m D p hw
  let expanded : Stage (actualShape n c m D capacity) := NativePolynomialStageShape.stage v (ℓ n) p
  let h := hready D capacity j hcut hD hpay hj expanded
  exact ⟨h.guardPositive,h.guardRoom,h.rowsPositive,
    hpacked D j p hcut hD hj v hw h.guardPositive h.guardRoom h.rowsPositive⟩

end
end IntegerMultBounds.Machine.CompactNativePolynomialStagePacked
