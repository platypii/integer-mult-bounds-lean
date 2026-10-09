import IntegerMultBounds.Machine.CompactGlobalRowInitialBudget
import IntegerMultBounds.Machine.CompactGlobalReservation

/-! Original public-header and complete compact-field interfaces for the
once-only global row-padding machine. The numeric and physical widths agree
without an assumed derived row or record-width input. -/
namespace IntegerMultBounds.Machine.CompactGlobalRowInitialEndpoint
noncomputable section
open CompactGlobalRowHeaders (initial originalValues recordWidth)
open CompactGlobalRowInitialData (bank)
open CompactGlobalRowPadding
variable {a : ℕ}

theorem original_words (K d D P : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i)=originalValues K d D P i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i))
    (source dest : ℤ → Fin (a+4)) (p q : ℤ) (i : Fin 4) :
    (bank (initial K d D P) source dest p q).head (Fin.castAdd 41 i)=1 ∧
    (bank (initial K d D P) source dest p q).tape (Fin.castAdd 41 i)=
      RadixZeroFill.encodedBinary (hs i) := by
  have he := CompactGadgetReservationHeadersCore.canonical_bits (hs i) (originalValues K d D P i) (hc i) (hv i)
  rw [he]
  fin_cases i <;> exact ⟨rfl,rfl⟩

/-- The first forty-three tapes contain only the four original public words
at either end of the complete machine; generated and private tapes are blank. -/
theorem private_blank (K d D P : ℕ) (source dest : ℤ → Fin (a+4)) (p q : ℤ)
    (i : Fin 43) (hi : 4 ≤ i.val) :
    (bank (initial K d D P) source dest p q).head (Fin.castAdd 2 i)=0 ∧
    (bank (initial K d D P) source dest p q).tape (Fin.castAdd 2 i)=fun _ => blank := by
  simp only [bank,Tapes.append,Fin.addCases_left]
  induction i using (Fin.addCases (m := 28) (n := 15)) with
  | left j =>
    have hh : ¬j.val<4 := by simpa using (show ¬(Fin.castAdd 15 j).val<4 by omega)
    simp [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,
      ActiveRepairRankHeadersCommands.caller,initial,hh]
  | right j =>
    simp [ActiveRepairRankHeadersCommands.bank,CleanSubbank.bank,Tapes.append,SharedBank.empty]

/-- The physically computed record length contains the two complete fronts,
active middle, complete back, unused address bits and complete payload. -/
theorem recordWidth_eq_shape (c m d D G K P : ℕ) (hK : 0<K)
    (hD : CompactGlobalReservation.reservedAxes c m d G K≤D) :
    recordWidth c m d D K P=(CompactGlobalReservation.shape c m d D G K P).recordWidth := by
  have hbits := CompactGlobalReservation.original_bits c m d D G K P hK hD
  have hq : rowAxes c m d≤D := by
    unfold CompactGlobalReservation.reservedAxes at hD
    omega
  have he : (D-rowAxes c m d)*K=(CompactGlobalReservation.shape c m d D G K P).bits := by
    have hsplit := Nat.sub_add_cancel hq
    nlinarith
  unfold recordWidth CompactGadgetReservationShape.Shape.recordWidth
  rw [he]
  rfl

end
end IntegerMultBounds.Machine.CompactGlobalRowInitialEndpoint
