import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersSchedule

/-! Physical metadata bootstrap from the original fourteen early headers:
measure the original row word, initialize one, then run retained arithmetic.
All descriptor starts and field widths for the repair caller are generated. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersRun
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairRankHeadersCommands
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersSchedule
open RecursiveChildQuotientsConstant (bits)
variable {s : Shape} {p : Parameters s} {offset rows : ℕ} {a : ℕ}

def lengthFocus : Fin 2 → Fin 28 := ![12,14]
theorem length_injective : Function.Injective lengthFocus := by decide
def lengthProgram := extend (ActiveRepairLayoutRecordsHeadersLength.placed (a := a) lengthFocus length_injective) 15
def seedProgram := extend (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
  (FiniteReturnStackAt.placement (15 : Fin 28))) 15
def program := seq (seq (lengthProgram (a := a)) seedProgram) ActiveRepairLayoutRecordsHeadersSchedule.program

def cost (d : Inputs s p offset rows) := 9*rowBits d+17+scheduleCost schedule (seeded d)

theorem canonical_original (d : Inputs s p offset rows) (i : Fin 14) :
    d.hs i=bits (ActivePrefixLayoutHeadersData.originalValues (ActivePrefixLayoutHeadersGeometry.inputs s p offset rows) i) :=
  CompactGadgetReservationHeadersCore.canonical_bits _ _ (d.hc i) (d.hv i)

def originalInput (d : Inputs s p offset rows) : Tapes 43 a :=
  (⟨fun _ => 1,fun i => RadixZeroFill.encodedBinary (d.hs i)⟩ : Tapes 14 a).append
    (SharedBank.empty 29 a)

theorem input_eq (d : Inputs s p offset rows) : bank (a := a) (initial d)=originalInput d := by
  apply congrArg₂ Tapes.mk
  · funext i; fin_cases i <;> rfl
  · funext i
    fin_cases i
    · change _ = RadixZeroFill.encodedBinary (d.hs 0)
      rw [canonical_original d 0]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 1)
      rw [canonical_original d 1]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 2)
      rw [canonical_original d 2]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 3)
      rw [canonical_original d 3]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 4)
      rw [canonical_original d 4]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 5)
      rw [canonical_original d 5]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 6)
      rw [canonical_original d 6]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 7)
      rw [canonical_original d 7]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 8)
      rw [canonical_original d 8]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 9)
      rw [canonical_original d 9]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 10)
      rw [canonical_original d 10]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 11)
      rw [canonical_original d 11]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 12)
      rw [canonical_original d 12]
      rfl
    · change _ = RadixZeroFill.encodedBinary (d.hs 13)
      rw [canonical_original d 13]
      rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl
    · rfl

theorem length_runs (d : Inputs s p offset rows) :
    HoareTime (lengthProgram (a := a)) (fun v => v=bank (initial d))
      (fun v => v=bank (scanned d)) (9*rowBits d+6) := by
  have hi : SharedBank.payload (caller (a := a) (initial d)) lengthFocus=
      ActiveRepairLayoutRecordsHeadersLength.input a (d.hs 12) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    · rfl
    · rfl
    · rw [canonical_original d 12]
      rfl
    · rfl
  have hh := ActiveRepairLayoutRecordsHeadersLength.placed_runs (caller (a := a) (initial d))
    lengthFocus length_injective (d.hs 12) hi
  have hout : SharedPlacementAlphabet.setTape (caller (a := a) (initial d)) (lengthFocus 1)
      (RadixZeroFill.encodedBinary (bits (d.hs 12).length)) 1=caller (scanned d) := by
    rw [scanned,put_caller]
    rfl
  rw [hout] at hh
  exact hoare_extend_eq hh (SharedBank.empty 15 a)

theorem seed_runs (d : Inputs s p offset rows) :
    HoareTime (seedProgram (a := a)) (fun v => v=bank (scanned d))
      (fun v => v=bank (seeded d)) 9 := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) 1)
    (FiniteReturnStackAt.placement (15 : Fin 28)) (caller (a := a) (scanned d))
    (by rw [FiniteReturnStackAt.active_bank]; simp [caller,scanned,initial,put,Function.update])
  have h' : HoareTime (Placement.placed (RecursiveChildQuotientsConstant.program (a := a) 1)
      (FiniteReturnStackAt.placement (15 : Fin 28))) (fun v => v=caller (scanned d))
      (fun v => v=caller (seeded d)) 9 := by
    apply h.consequence (fun _ h => h) _ (by decide)
    rintro z ⟨small,rfl,rfl⟩
    rw [seeded,put_caller,FiniteReturnStackAt.replace_bank,BinaryDescriptorStackRoundtrip.descriptor_encoded]
  exact hoare_extend_eq h' (SharedBank.empty 15 a)

theorem runs (d : Inputs s p offset rows) :
    HoareTime (program (a := a)) (fun v => v=bank (initial d))
      (fun v => v=bank (finished d)) (cost d) := by
  exact (((length_runs d).seq (seed_runs d)).seq (ActiveRepairLayoutRecordsHeadersSchedule.runs d)).consequence
    (fun _ hv => hv) (fun _ hv => hv) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersRun
