import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAssemblyOriginalLateAfter
import IntegerMultBounds.Machine.ActiveRepairLayoutDensityArithmetic

/-! Original canonical row headers pay the full-address repair width.
The dyadic bound uses the original layout size, rather than a separately
supplied repair address width or density constant. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAllowance
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData
variable {s : Shape} {p : Parameters s} {offset rows : ℕ}

theorem address_width (d : Inputs s p offset rows) :
    (geom d).addressBits=s.bits+rowBits d := rfl

theorem address_allowance (d : Inputs s p offset rows) :
    (geom d).addressBits+1≤s.bits+rows.log2+2 := by
  have h := row_log d
  rw [address_width]
  omega

theorem payload_allowance (d : Inputs s p offset rows)
    (hpad : s.bits+rows.log2+2≤s.payload) :
    (geom d).addressBits+1≤s.payload :=
  (address_allowance d).trans hpad

theorem early_payload_allowance (d : Inputs s p offset rows)
    (hpad : s.bits+rows.log2+2≤s.payload) :
    (repair d).geom.addressBits+1≤s.payload := payload_allowance d hpad

theorem late_payload_allowance (d : Inputs s p offset rows)
    (hpad : s.bits+rows.log2+2≤s.payload) :
    (ActiveRepairLayoutRecordsAssemblyOriginalLateAfter.repair d).geom.addressBits+1≤s.payload :=
  payload_allowance d hpad

theorem dyadic_allowances (d : Inputs s p offset rows) (P : ℝ) (ell : ℕ)
    (hP : 0<P) (hn : (p.n:ℝ)≤P) (hell : P≤(2:ℝ)^ell)
    (hK : 8*ell+16≤p.q) (hb : p.b=4*ell+6)
    (hsize : ((s.bits+rows.log2+2:ℕ):ℝ)≤P^3)
    (hpad : s.bits+rows.log2+2≤s.payload) :
    (geom d).addressBits+1≤s.payload ∧
      VaryingControlRepairDensity.earlyDensity p.q p.b p.n*
        ((geom d).addressBits+1)≤1 ∧
      VaryingControlRepairDensity.lateDensity p.q p.b p.n*
        ((geom d).addressBits+1)≤1 := by
  have hA : ((geom d).addressBits:ℝ)+1≤P^3 := by
    have hh : (((geom d).addressBits+1:ℕ):ℝ)≤((s.bits+rows.log2+2:ℕ):ℝ) :=
      Nat.cast_le.mpr (address_allowance d)
    simpa only [Nat.cast_add,Nat.cast_one] using hh.trans hsize
  refine ⟨payload_allowance d hpad,?_,?_⟩
  · rw [hb]
    exact ActiveRepairLayoutDensityArithmetic.dyadic_early_paid P p.n ell p.q
      (geom d).addressBits hP hn hell hK hA
  · rw [hb]
    exact ActiveRepairLayoutDensityArithmetic.dyadic_late_paid P p.n ell p.q
      (geom d).addressBits hP hn hell hK hA

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsAllowance
