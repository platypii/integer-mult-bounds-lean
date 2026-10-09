import IntegerMultBounds.Machine.ArbitraryWidthHighExchangeSemantics
import IntegerMultBounds.Machine.RadixHighBlockJoinSemantics

/-! Exact serialized bridge between the paid high-prefix exchange, ordered
high-block movement, and the manuscript's joined-row view. The actual exchange
runs before joining. Every regrouping below is an explicit finite-index cast. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (volume)
open RecursiveInterchangeRows (pack pack_val)
open ArbitraryWidthHighLayout
variable {a : ℕ}

/-- The physical join's P/S/E parameters are P*q^rho, q^(e-rho)*G,
and q^(e-rho)*B, respectively. -/
theorem input_volume (q P e r G B : ℕ) (hr : r ≤ e) :
    (P*q^r)*(q^(e-r)*G)*q^r*(q^(e-r)*B) = volume q (originalDescriptor P e G B) := by
  rw [← original_volume q P e r G B hr]
  ring

theorem output_volume (q P e r G B : ℕ) :
    (P*q^r)*q^r*((q^(e-r)*G)*(q^(e-r)*B)) = volume q (joinedDescriptor q P e r G B) := by
  rw [← joined_volume q P e r G B]
  ring

/-- Grouping the untouched low fields and spectators into S and E preserves
the literal original serialized address. -/
theorem original_packed (q P e r G B : ℕ) (hr : r ≤ e)
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    Fin.cast (input_volume q P e r G B hr)
      (pack (pack (pack (pack c.pre c.highH) (pack c.lowH c.middle)) c.highD)
        (pack c.lowD c.after)) = originalEquiv q P e r G B hr c := by
  apply Fin.ext
  change _ = (originalRaw P (q^r) (q^(e-r)) G B c).val
  simp only [Fin.val_cast,pack_val,originalRaw_val]
  ring

/-- The leading joined row stores highD before highH; all remaining fields
keep their within-row order. -/
theorem joined_packed (q P e r G B : ℕ)
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    Fin.cast (output_volume q P e r G B)
      (pack (pack (pack c.pre c.highD) c.highH)
        (pack (pack c.lowH c.middle) (pack c.lowD c.after))) =
      joinedEquiv q P e r G B c := by
  apply Fin.ext
  change _ = (joinedRaw P (q^r) (q^(e-r)) G B c).val
  simp only [Fin.val_cast,pack_val,joinedRaw_val]
  ring

theorem original_cast (q P e r G B : ℕ) (hr : r ≤ e)
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    Fin.cast (input_volume q P e r G B hr).symm (originalEquiv q P e r G B hr c) =
      pack (pack (pack (pack c.pre c.highH) (pack c.lowH c.middle)) c.highD)
        (pack c.lowD c.after) := by
  rw [← original_packed q P e r G B hr c]
  simp only [Fin.cast_cast,Fin.cast_refl,id_eq]

theorem joined_cast (q P e r G B : ℕ)
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    Fin.cast (output_volume q P e r G B).symm (joinedEquiv q P e r G B c) =
      pack (pack (pack c.pre c.highD) c.highH)
        (pack (pack c.lowH c.middle) (pack c.lowD c.after)) := by
  rw [← joined_packed q P e r G B c]
  simp only [Fin.cast_cast,Fin.cast_refl,id_eq]

/-- Ordered physical block joining, with only explicit serialization casts.
Its argument is the array already produced by the high-prefix exchange. -/
def joinArray (q P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume q (originalDescriptor P e G B)) → Fin (a+4)) :
    Fin (volume q (joinedDescriptor q P e r G B)) → Fin (a+4) :=
  RadixHighBlockJoinSemantics.reindex (output_volume q P e r G B).symm
    (RadixHighBlockJoinSemantics.join q r (P*q^r) (q^(e-r)*G) (q^(e-r)*B)
      (RadixHighBlockJoinSemantics.reindex (input_volume q P e r G B hr) x))

/-- Pure inverse block movement, leaving the joined high-row order intact
until the physical separator crosses the entire low/spectator block. -/
def separateArray (q P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume q (joinedDescriptor q P e r G B)) → Fin (a+4)) :
    Fin (volume q (originalDescriptor P e G B)) → Fin (a+4) :=
  RadixHighBlockJoinSemantics.reindex (input_volume q P e r G B hr).symm
    (RadixDigitMoveBlockRows.move (RadixHighBlockJoinSemantics.reindex (output_volume q P e r G B) x))

theorem joinArray_entry (q P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume q (originalDescriptor P e G B)) → Fin (a+4))
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    joinArray q P e r G B hr x (joinedEquiv q P e r G B c) =
      x (originalEquiv q P e r G B hr (highSwap c)) := by
  unfold joinArray
  rw [RadixHighBlockJoinSemantics.join_eq_unmove]
  change RadixDigitMoveBlockRows.unmove _
    (Fin.cast (output_volume q P e r G B).symm (joinedEquiv q P e r G B c)) = _
  rw [joined_cast,RadixDigitMoveBlockRows.unmove_entry]
  exact congrArg x (original_packed q P e r G B hr (highSwap c))

theorem separateArray_entry (q P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume q (joinedDescriptor q P e r G B)) → Fin (a+4))
    (c : Coordinate P (q^r) (q^(e-r)) G B) :
    separateArray q P e r G B hr x (originalEquiv q P e r G B hr c) =
      x (joinedEquiv q P e r G B (highSwap c)) := by
  unfold separateArray
  change RadixDigitMoveBlockRows.move _
    (Fin.cast (input_volume q P e r G B hr).symm (originalEquiv q P e r G B hr c)) = _
  rw [original_cast,RadixDigitMoveBlockRows.move_entry]
  exact congrArg x (joined_packed q P e r G B (highSwap c))

/-- The real exchange followed by the ordered physical join has exactly the
manuscript's exchangeJoin semantics at every serialized cell. -/
theorem join_after_exchange (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → Fin (a+4)) :
    joinArray prime P e r G B hr
      (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr x) =
      exchangeJoin P e r G B hr x := by
  funext z
  obtain ⟨c,rfl⟩ := (joinedEquiv prime P e r G B).surjective z
  rw [joinArray_entry,ArbitraryWidthHighExchangeSemantics.array_highSwap,highSwap_twice,
    exchangeJoin_entry]

/-- The paid inverse separator realizes the full serialized separateExchange
view, including all low fields and spectators. -/
theorem separate_eq (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (joinedDescriptor prime P e r G B)) → Fin (a+4)) :
    separateArray prime P e r G B hr x = separateExchange P e r G B hr x := by
  funext z
  obtain ⟨c,rfl⟩ := (originalEquiv prime P e r G B hr).surjective z
  rw [separateArray_entry,separateExchange_entry]

/-- Serialized correctness of exchange, join, low transpose and separation. -/
theorem exchange_join_transpose_separate (P e r G B : ℕ) (hr : r ≤ e)
    (x : Fin (volume prime (originalDescriptor P e G B)) → Fin (a+4)) :
    separateArray prime P e r G B hr
      (Shared50RecursiveNodeRows.transpose (one_dvd _)
        (joinArray prime P e r G B hr
          (ArbitraryWidthHighExchangeSemantics.array (originalDescriptor P e G B) r hr x))) =
      Shared50RecursiveNodeRows.transpose (one_dvd _) x := by
  rw [join_after_exchange,separate_eq,exchange_transpose_separate]

end
end IntegerMultBounds.Machine.ArbitraryWidthHighMovementSemantics
