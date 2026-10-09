import IntegerMultBounds.Machine.ActiveRepairLayoutRecordsHeadersCount

/-! The actual producer's fifteen retained descriptors are exactly the repair
caller's original geometry, source and radix metadata. Actual fixed-many copies
install them on blank output tapes, preserving the complete producer bank. -/
namespace IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankHeaders
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixLayoutShapes ActivePrefixEarlySequenceOriginalInputs
open ActiveRepairLayoutRecordsHeadersData ActiveRepairLayoutRecordsHeadersCount
open ActiveRepairLayoutRecordsHeadersSchedule ActiveRepairRankHeadersCommands
variable {s : Shape} {p : Parameters s} {offset rows : ℕ} {a : ℕ}

def words (d : Inputs s p offset rows) : Fin 15 → List Bool :=
  ![d.hs 0,d.hs 1,d.hs 2,d.hs 3,d.hs 4,d.hs 5,d.hs 6,d.hs 11,
    RecursiveChildQuotientsConstant.bits (p.n*p.q+p.q),RecursiveChildQuotientsConstant.bits (s.bits+rowBits d),
    d.hs 7,d.hs 9,d.hs 10,RecursiveChildQuotientsConstant.bits (p.n+1),d.hs 8]
def focus : Fin 15 → Fin 43 := ![0,1,2,3,4,5,6,11,17,18,7,9,10,16,8]

theorem source_heads (d : Inputs s p offset rows) :
    ∀ i, (bank (a := a) (ready d)).head (focus i)=1 := by
  intro i
  fin_cases i <;> rfl

theorem source_tapes (d : Inputs s p offset rows) :
    ∀ i, (bank (a := a) (ready d)).tape (focus i)=RadixZeroFill.encodedBinary (words d i) := by
  intro i
  fin_cases i
  · change _ = RadixZeroFill.encodedBinary (d.hs 0)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 0]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 1)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 1]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 2)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 2]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 3)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 3]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 4)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 4]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 5)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 5]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 6)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 6]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 11)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 11]
    rfl
  · rfl
  · rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 7)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 7]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 9)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 9]
    rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 10)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 10]
    rfl
  · rfl
  · change _ = RadixZeroFill.encodedBinary (d.hs 8)
    rw [ActiveRepairLayoutRecordsHeadersRun.canonical_original d 8]
    rfl

def copyProgram := FixedHeaderBankCopy.program (t := 43) (a := a) (by decide : 0<43+15) focus
def program := seq (extend (ActiveRepairLayoutRecordsHeadersCount.program (a := a)) 15) copyProgram
def input (d : Inputs s p offset rows) := (bank (a := a) (initial d)).append (FixedHeaderBankCopy.empty 15)
def output (d : Inputs s p offset rows) := (bank (a := a) (ready d)).append (FixedHeaderBankCopy.headerBank (words d))
def runtime (d : Inputs s p offset rows) := ActiveRepairLayoutRecordsHeadersCount.runtime d+1+
  FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (words d)

theorem copies (d : Inputs s p offset rows) :
    HoareTime (copyProgram (a := a))
      (fun v => v=(bank (a := a) (ready d)).append (FixedHeaderBankCopy.empty 15))
      (fun v => v=output d) (FixedHeaderBankCopy.cost (FixedHeaderBankCopy.ops 15) (words d)) :=
  FixedHeaderBankCopy.constructs (by decide) focus (words d) (bank (ready d)) (source_tapes d) (source_heads d)

theorem runs (d : Inputs s p offset rows) :
    HoareTime (program (a := a)) (fun v => v=input d) (fun v => v=output d) (runtime d) :=
  (hoare_extend_eq (ActiveRepairLayoutRecordsHeadersCount.prepares d)
    (FixedHeaderBankCopy.empty 15)).seq (copies d)

end
end IntegerMultBounds.Machine.ActiveRepairLayoutRecordsBankHeaders
