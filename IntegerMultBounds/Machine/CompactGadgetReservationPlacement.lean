import IntegerMultBounds.Machine.CompactGadgetReservationBudget
import IntegerMultBounds.Machine.CleanSubbank

/-! Concrete caller slots for a reserved role load: five retained original
shape/offset tapes follow the complete reservation bank; the native payload
port is the actual selected role. Every other role and original header is framed. -/
namespace IntegerMultBounds.Machine.CompactGadgetReservationPlacement
noncomputable section
open Networks.Shared50ModularControl (prime)
open CompactGadgetReservationShape
open CompactGadgetReservationData (roleSlot)
open SharedPlacementAlphabet (setTape)

abbrev ReservationTapes (c : ℕ) :=
  CompactRowReservationPlacement.CommonTapes c+CompactRowReservationPlacement.NativeTapes c
abbrev NativeTapes := (6+9)+BinaryPackedOffsetOriginalRun.count+12
abbrev CommonTapes (c : ℕ) := ReservationTapes c+5

def nativeSlots (i : Fin 6) : Fin NativeTapes :=
  Fin.castAdd 12 (Fin.castAdd BinaryPackedOffsetOriginalRun.count (Fin.castAdd 9 i))
def commonSlots (c : ℕ) (j : Fin c) : Fin 6 → Fin (CommonTapes c) :=
  Fin.addCases (m := 5) (n := 1) (fun i : Fin 5 => Fin.natAdd (ReservationTapes c) i)
    (fun _ : Fin 1 => Fin.castAdd 5 (roleSlot c j))

theorem native_injective : Function.Injective nativeSlots := by
  intro i j h
  exact Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ (Fin.castAdd_injective _ _ h))

theorem common_injective (c : ℕ) (j : Fin c) : Function.Injective (commonSlots c j) := by
  intro i k h
  induction i using (Fin.addCases (m := 5) (n := 1)) with
  | left i =>
    induction k using (Fin.addCases (m := 5) (n := 1)) with
    | left k =>
      simp only [commonSlots,Fin.addCases_left] at h
      exact congrArg (Fin.castAdd 1) (Fin.natAdd_injective _ _ h)
    | right k =>
      simp only [commonSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      change ReservationTapes c+i.val = (roleSlot c j).val at hv
      have hlt : (roleSlot c j).val < ReservationTapes c := (roleSlot c j).isLt
      exact (Nat.not_le_of_lt hlt ((Nat.le_add_right _ _).trans_eq hv)).elim
  | right i =>
    induction k using (Fin.addCases (m := 5) (n := 1)) with
    | left k =>
      simp only [commonSlots,Fin.addCases_left,Fin.addCases_right] at h
      have hv := congrArg Fin.val h
      change (roleSlot c j).val = ReservationTapes c+k.val at hv
      have hlt : (roleSlot c j).val < ReservationTapes c := (roleSlot c j).isLt
      exact (Nat.not_le_of_lt hlt ((Nat.le_add_right _ _).trans_eq hv.symm)).elim
    | right k => exact congrArg (Fin.natAdd 5) (Subsingleton.elim i k)

theorem native_payload (caller : Tapes 6 prime) :
    SharedBank.payload (BinaryPackedOffsetOriginalRun.input caller) nativeSlots = caller := by
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

theorem native_clean (caller : Tapes 6 prime) :
    SharedBank.strip (BinaryPackedOffsetOriginalRun.input caller) nativeSlots =
      SharedBank.empty NativeTapes prime := by
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases with
  | left i =>
    induction i using Fin.addCases with
    | left i =>
      induction i using Fin.addCases with
      | left i =>
        simp [nativeSlots]
      | right i =>
        simp [nativeSlots,BinaryPackedOffsetOriginalRun.input,
          BinaryPackedOffsetRun.input,BinaryRadixEqualShared.input,
          BinaryPackedRowCountPlaced.input,Tapes.append,FixedHeaderBankCopy.empty]
    | right i =>
      simp [nativeSlots,BinaryPackedOffsetOriginalRun.input,
        BinaryPackedOffsetRun.input,BinaryRadixEqualShared.input,
        BinaryPackedRowCountPlaced.input,Tapes.append,FixedHeaderBankCopy.empty]
  | right i =>
    simp [nativeSlots,BinaryPackedOffsetOriginalRun.input,
      BinaryPackedOffsetRun.input,BinaryRadixEqualShared.input,
      BinaryPackedRowCountPlaced.input,Tapes.append,FixedHeaderBankCopy.empty]

theorem payload_set {k p a : ℕ} (caller : Tapes k a) (focus : Fin p → Fin k)
    (hi : Function.Injective focus) (i : Fin p) (tape : ℤ → Fin (a+4)) (pos : ℤ) :
    SharedBank.payload (setTape caller (focus i) tape pos) focus =
      setTape (SharedBank.payload caller focus) i tape pos := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : j = i
  all_goals first
    | (subst j; simp [SharedBank.payload,setTape])
    | (have hne : focus j ≠ focus i := fun h => hj (hi h)
       simp only [SharedBank.payload,setTape,Function.update_of_ne hne,Function.update_of_ne hj])

theorem strip_set {k p a : ℕ} (caller : Tapes k a) (focus : Fin p → Fin k)
    (i : Fin p) (tape : ℤ → Fin (a+4)) (pos : ℤ) :
    SharedBank.strip (setTape caller (focus i) tape pos) focus = SharedBank.strip caller focus := by
  apply congrArg₂ Tapes.mk <;> funext j
  all_goals by_cases hj : ∃ z, focus z = j
  all_goals first
    | (solve | simp only [hj,↓reduceIte])
    | (have hne : j ≠ focus i := by intro h; exact hj ⟨i,h.symm⟩
       simp only [hj,↓reduceIte,setTape,Function.update_of_ne hne])

def program (c : ℕ) (j : Fin c) :=
  Placement.placed BinaryPackedOffsetOriginalRun.program
    (CleanSubbank.placement nativeSlots (commonSlots c j) (common_injective c j))

/-- Concrete reserved-role placement of an actual root run. The selected
role changes; every other reservation cell/head, all original descriptors and
offset tapes, and every private native tape are retained/restored literally. -/
theorem realizes {c : ℕ} (j : Fin c) (common : Tapes (CommonTapes c) prime)
    (y : Fin (RadixRangePadding.volume P N G B) → Bool) (C : ℕ)
    (hr : HoareTime BinaryPackedOffsetOriginalRun.program
      (fun v => v = BinaryPackedOffsetOriginalRun.input (SharedBank.payload common (commonSlots c j)))
      (fun v => v = BinaryPackedOffsetOriginalRun.input
        (BinaryPackedFieldSwap.store (SharedBank.payload common (commonSlots c j)) 5 y)) C) :
    HoareTime (program c j)
      (fun v => v = CleanSubbank.bank (s := NativeTapes) common)
      (fun v => v = CleanSubbank.bank (s := NativeTapes)
        (setTape common (commonSlots c j 5)
          (BinaryRadixRangePrepareAlphabet.word (fun i => bitSymbol (y i))) 0)) C := by
  apply CleanSubbank.realizes _ nativeSlots (commonSlots c j) native_injective
    (common_injective c j) common _ _ _ C
  · exact native_payload _
  · rw [native_payload,payload_set common _ (common_injective c j)]
  · exact native_clean _
  · exact native_clean _
  · exact (strip_set common _ 5 _ 0).symm
  · exact hr

/-- The actual native payload is the selected physical reservation role. -/
theorem projected_role {c r : ℕ} (hc : 0 < c) (s : Shape)
    (x : Fin (1*r*s.recordWidth) → Bool) (rs ls : List Bool) (extra : Tapes 5 prime) (j : Fin c) :
    (SharedBank.payload ((CompactRowReservationEndpoint.final (a := prime) hc x rs ls).append extra)
      (commonSlots c j)).head 5 = 0 ∧
    (SharedBank.payload ((CompactRowReservationEndpoint.final (a := prime) hc x rs ls).append extra)
      (commonSlots c j)).tape 5 =
      (CompactRowReservationEndpoint.final (a := prime) hc x rs ls).tape (roleSlot c j) := by
  have h5 : (5 : Fin 6) = Fin.natAdd 5 (0 : Fin 1) := Fin.ext rfl
  rw [h5]
  constructor
  · simpa only [SharedBank.payload,commonSlots,Fin.addCases_right,Tapes.append,
      Fin.addCases_left,CompactGadgetReservationData.roleSlot] using
      (CompactRowReservationEndpoint.role_word (a := prime) hc x rs ls j).1
  · simp only [SharedBank.payload,commonSlots,Fin.addCases_right,Tapes.append,
      Fin.addCases_left]

end
end IntegerMultBounds.Machine.CompactGadgetReservationPlacement
