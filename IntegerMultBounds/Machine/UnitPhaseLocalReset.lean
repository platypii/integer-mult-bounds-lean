import IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle
import IntegerMultBounds.Machine.RawBitWordReset
import IntegerMultBounds.Machine.UnitPhaseCoreReset
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Paid reset of the sixty-tape phase record caller after emission. Numerator
sources, extracted controls, flags and all three generated sparse descriptors
are physically erased; every address, stream and controller tape is framed. -/
namespace IntegerMultBounds.Machine.UnitPhaseLocalReset
noncomputable section
open SharedPlacementAlphabet (setTape)
open MarkedWordCleanup (marked one)
abbrev count := 60
def real := Placement.placed (MarkedBinaryCleanup.program (q := 2)) (FiniteReturnStackAt.placement (50 : Fin count))
def imaginary := Placement.placed (MarkedBinaryCleanup.program (q := 2)) (FiniteReturnStackAt.placement (51 : Fin count))
def control := Placement.placed (RawBitWordReset.program (a := 2)) (FiniteReturnStackAt.placement (44 : Fin count))
def flags := TwoTapeAt.program UnitPhaseFlagsLifecycle.cleanup (48 : Fin count) 49 (by decide)
def headerSlots : List (Fin count) := [22,23,24]
def headers := BinaryDescriptorCleanupList.program (a := 2) (by decide : 0<count) headerSlots
def program := seq (seq (seq (seq real imaginary) control) flags) headers
def afterReal (v : Tapes count 2) := setTape v 50 (fun _ => blank) 0
def afterImaginary (v : Tapes count 2) := setTape (afterReal v) 51 (fun _ => blank) 0
def afterControl (v : Tapes count 2) := setTape (afterImaginary v) 44 (fun _ => blank) 0
def afterFlags (v : Tapes count 2) := setTape (setTape (afterControl v) 48 (fun _ => blank) 0) 49 (fun _ => blank) 0
def output (v : Tapes count 2) := BinaryDescriptorCleanupList.cleared headerSlots (afterFlags v)
def cost (xs : ℕ → List (Fin 2)) (bs : List Bool) (hs : Fin count → List Bool) :=
  2*(xs 0).length+2*(xs 1).length+bs.length+BinaryDescriptorCleanupList.cost headerSlots hs+15

private theorem radix_clears (slot : Fin count) (v : Tapes count 2) (xs : List (Fin 2))
    (ht : v.tape slot=marked (xs.map RadixDigits.digitSymbol)) (hh : v.head slot=1) :
    HoareTime (Placement.placed (MarkedBinaryCleanup.program (q := 2)) (FiniteReturnStackAt.placement slot))
      (fun z => z=v) (fun z => z=setTape v slot (fun _ => blank) 0) (2*xs.length+4) := by
  have h := Placement.hoare_at (RawLinearCombinationCleanup.marked_radix xs)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hh]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

theorem runs (v : Tapes count 2) (xs : ℕ → List (Fin 2)) (bs : List Bool) (p : Fin 4)
    (hs : Fin count → List Bool)
    (hr : v.tape 50=marked ((xs 0).map RadixDigits.digitSymbol) ∧ v.head 50=1)
    (hi : v.tape 51=marked ((xs 1).map RadixDigits.digitSymbol) ∧ v.head 51=1)
    (hc : v.tape 44=SelectedSourceBitsScan.word bs ∧ v.head 44=bs.length)
    (hl : v.tape 48=putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.low p)] ∧ v.head 48=0)
    (hh : v.tape 49=putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.high p)] ∧ v.head 49=0)
    (hd : ∀ i ∈ headerSlots,v.head i=1 ∧ v.tape i=BinaryDescriptorStack.descriptor (hs i)) :
    HoareTime program (fun z => z=v) (fun z => z=output v) (cost xs bs hs) := by
  have h0 := radix_clears 50 v (xs 0) hr.1 hr.2
  have h1 := radix_clears 51 (afterReal v) (xs 1)
    (by simpa [afterReal,setTape] using hi.1) (by simpa [afterReal,setTape] using hi.2)
  have ha : Placement.active (FiniteReturnStackAt.placement (44 : Fin count)) (afterImaginary v)=
      one (SelectedSourceBitsScan.word bs) bs.length := by
    rw [FiniteReturnStackAt.active_bank]
    simp [afterImaginary,afterReal,setTape,hc]
    rfl
  have hsmall := Placement.hoare_at (RawBitWordReset.runs (a := 2) bs)
    (FiniteReturnStackAt.placement (44 : Fin count)) (afterImaginary v) ha
  have h2 : HoareTime control (fun z => z=afterImaginary v) (fun z => z=afterControl v) (bs.length+2) := by
    apply hsmall.consequence (fun _ h => h) _ le_rfl
    rintro z ⟨small,rfl,rfl⟩
    exact FiniteReturnStackAt.replace_bank _ _ _ _
  have hflags := UnitPhaseFlagsLifecycle.cleans p
  have hfp : UnitPhaseNumerator.flags p=Copy.tapes
      (putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.low p)])
      (putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.high p)]) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  have he : SharedBank.empty 2 2=Copy.tapes (fun _ => blank) (fun _ => blank) 0 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hfp,he] at hflags
  have h3 := TwoTapeAt.runs UnitPhaseFlagsLifecycle.cleanup (48 : Fin count) 49 (by decide)
    (afterControl v) _ _ _ _ _ _ _ _
    (by simpa [afterControl,afterImaginary,afterReal,setTape] using hl)
    (by simpa [afterControl,afterImaginary,afterReal,setTape] using hh) hflags
  have h4 := BinaryDescriptorCleanupList.cleanup_hoare (a := 2) (by decide : 0<count)
    headerSlots (by decide) hs (afterFlags v) (by
      intro i hm
      have h := hd i hm
      simp only [headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals simpa [afterFlags,afterControl,afterImaginary,afterReal,setTape] using h)
  exact ((((h0.seq h1).seq h2).seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseLocalReset
