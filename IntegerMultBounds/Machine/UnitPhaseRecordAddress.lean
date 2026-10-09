import IntegerMultBounds.Machine.BinaryCurrentAddress
import IntegerMultBounds.Machine.UnitPhaseRecordIO

/-! The sixty-tape coefficient body reads its address from the live marked
counter, returns both heads, and increments the counter on actual tapes. The
previous equal-width raw readout is overwritten; all other tapes are framed. -/
namespace IntegerMultBounds.Machine.UnitPhaseRecordAddress
noncomputable section
open SharedPlacementAlphabet (setTape)
open BinaryAddressTableData (row)
open CountedLoopReuseAlphabet (binary)
abbrev count := 60

def program := TwoTapeAt.program (BinaryCurrentAddress.program (a := 2))
  (57 : Fin count) 43 (by decide)
def output (v : Tapes count 2) (W i : ℕ) :=
  TwoTapeAt.result v 57 43 (binary (row W (i+1)))
    (SelectedSourceBitsScan.word (row W i)) 1 0

theorem runs (v : Tapes count 2) (W i : ℕ) (old : List Bool) (hl : old.length=W)
    (hc : v.tape 57=binary (row W i) ∧ v.head 57=1)
    (ha : v.tape 43=SelectedSourceBitsScan.word old ∧ v.head 43=0) :
    HoareTime program (fun z => z=v) (fun z => z=output v W i) (5*W+10) := by
  exact TwoTapeAt.runs (BinaryCurrentAddress.program (a := 2))
    (57 : Fin count) 43 (by decide) v _ _ _ _ _ _ _ _ hc ha
      (BinaryCurrentAddress.next W i old hl)

theorem address (v : Tapes count 2) (W i : ℕ) :
    (output v W i).tape 43=SelectedSourceBitsScan.word (row W i) ∧
      (output v W i).head 43=0 := by
  simp [output,TwoTapeAt.result,setTape]

theorem counter (v : Tapes count 2) (W i : ℕ) :
    (output v W i).tape 57=binary (row W (i+1)) ∧ (output v W i).head 57=1 := by
  simp [output,TwoTapeAt.result,setTape]

theorem frame (v : Tapes count 2) (W i : ℕ) (j : Fin count) (hc : j ≠ 57) (ha : j ≠ 43) :
    (output v W i).tape j=v.tape j ∧ (output v W i).head j=v.head j := by
  simp [output,TwoTapeAt.result,setTape,hc,ha]

end
end IntegerMultBounds.Machine.UnitPhaseRecordAddress
