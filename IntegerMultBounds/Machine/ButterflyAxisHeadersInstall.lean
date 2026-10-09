import IntegerMultBounds.Machine.ButterflyAxisHeadersBudget
import IntegerMultBounds.Machine.ButterflyAxisHeadersGeometry

/-! Physically copy eight generated runtime descriptors into distinct axis
ports. Repeated constant-one headers receive separate real copies; no tape is
aliased across simultaneous routing controls. The source payload is framed. -/
namespace IntegerMultBounds.Machine.ButterflyAxisHeadersInstall
noncomputable section
open ButterflyAxisHeadersData ButterflyAxisHeadersGeometry ButterflyAxisHeadersBudget
open ActiveRepairRankHeadersCommands (State)
variable {a : ℕ}

def caller (st : State) (payload : ℤ → Fin (a+4)) :=
  (ActiveRepairRankHeadersCommands.bank st).append (CountedLoopReuseAlphabet.one payload 0)

def source : Fin 8 → Fin 44 := ![14,15,4,13,12,6,4,4]
def program := FixedHeaderBankCopy.program (a:=a) (by decide : 0<44+8) source
def cleanup := FixedHeaderBankCopy.cleanup (a:=a) (t:=44) (n:=8) (by decide)

def input (st : State) (payload : ℤ → Fin (a+4)) := (caller st payload).append (SharedBank.empty 8 a)
def prepared (D t R p : ℕ) (payload : ℤ → Fin (a+4)) :=
  (caller (output D t R p) payload).append (FixedHeaderBankCopy.headerBank (words D t R p))

theorem source_tape (D t R p : ℕ) (payload : ℤ → Fin (a+4)) (i : Fin 8) :
    (caller (output D t R p) payload).tape (source i)=RadixZeroFill.encodedBinary (words D t R p i) := by
  fin_cases i <;> rfl

theorem source_head (D t R p : ℕ) (payload : ℤ → Fin (a+4)) (i : Fin 8) :
    (caller (output D t R p) payload).head (source i)=1 := by
  fin_cases i <;> rfl

theorem volume_pos (D R p : ℕ) (hR : 0<R) : 0<logicalVolume D R p := by
  unfold logicalVolume recordLength
  positivity

theorem words_bounded (D t R p : ℕ) (ht : t<D) (hR : 0<R) (i : Fin 8) :
    Counter.value (words D t R p i)≤logicalVolume D R p := by
  obtain ⟨_,_,_,_,_,_,_,_,_,hB,hH,hP,hS⟩ := values_le D t R p ht hR
  have hV := volume_pos D R p hR
  fin_cases i <;> simp [words,headers,headerValues,Fin.addCases,
    RecursiveChildQuotientsConstant.bits_value]
  all_goals first | exact hP | exact hS | exact hB | omega

theorem runs (D t R p : ℕ) (ht : t<D) (hR : 0<R) (payload : ℤ → Fin (a+4)) :
    HoareTime program (fun v => v=input (output D t R p) payload)
      (fun v => v=prepared D t R p payload) (80*logicalVolume D R p) :=
  FixedHeaderBankCopy.constructs_linear (by decide) source (words D t R p) (caller (output D t R p) payload)
    (source_tape D t R p payload) (source_head D t R p payload)
    (logicalVolume D R p) (volume_pos D R p hR) (words_canonical D t R p) (words_bounded D t R p ht hR)

theorem cleans (D t R p : ℕ) (ht : t<D) (hR : 0<R) (payload : ℤ → Fin (a+4)) :
    HoareTime cleanup (fun v => v=prepared D t R p payload)
      (fun v => v=input (output D t R p) payload) (72*logicalVolume D R p) :=
  FixedHeaderBankCopy.cleans_linear (by decide) (caller (output D t R p) payload) (words D t R p)
    (logicalVolume D R p) (volume_pos D R p hR) (words_canonical D t R p) (words_bounded D t R p ht hR)

end
end IntegerMultBounds.Machine.ButterflyAxisHeadersInstall
