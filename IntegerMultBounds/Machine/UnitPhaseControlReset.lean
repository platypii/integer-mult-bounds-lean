import IntegerMultBounds.Machine.UnitPhaseFlagsLifecycle
import IntegerMultBounds.Machine.RawBitWordReset
import IntegerMultBounds.Machine.TwoTapeAt
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList

/-! Paid reset of the sixty-tape phase record caller after emission. Numerator
sources, extracted controls, flags and all three generated sparse descriptors
are physically erased; every address, stream and controller tape is framed. -/
namespace IntegerMultBounds.Machine.UnitPhaseControlReset
noncomputable section
open SharedPlacementAlphabet (setTape)
open MarkedWordCleanup (marked one)
abbrev count := 60
def control := Placement.placed (RawBitWordReset.program (a := 2)) (FiniteReturnStackAt.placement (44 : Fin count))
def flags := TwoTapeAt.program UnitPhaseFlagsLifecycle.cleanup (48 : Fin count) 49 (by decide)
def headerSlots : List (Fin count) := [22,23,24]
def headers := BinaryDescriptorCleanupList.program (a := 2) (by decide : 0<count) headerSlots
def program := seq (seq control flags) headers
def afterControl (v : Tapes count 2) := setTape v 44 (fun _ => blank) 0
def afterFlags (v : Tapes count 2) := setTape (setTape (afterControl v) 48 (fun _ => blank) 0) 49 (fun _ => blank) 0
def output (v : Tapes count 2) := BinaryDescriptorCleanupList.cleared headerSlots (afterFlags v)
def cost (bs : List Bool) (hs : Fin count → List Bool) :=
  bs.length+BinaryDescriptorCleanupList.cost headerSlots hs+5

theorem runs (v : Tapes count 2) (bs : List Bool) (p : Fin 4)
    (hs : Fin count → List Bool)
    (hc : v.tape 44=SelectedSourceBitsScan.word bs ∧ v.head 44=bs.length)
    (hl : v.tape 48=putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.low p)] ∧ v.head 48=0)
    (hh : v.tape 49=putWord (fun _ => blank) 0 [bitSymbol (UnitPhaseNumerator.high p)] ∧ v.head 49=0)
    (hd : ∀ i ∈ headerSlots,v.head i=1 ∧ v.tape i=BinaryDescriptorStack.descriptor (hs i)) :
    HoareTime program (fun z => z=v) (fun z => z=output v) (cost bs hs) := by
  have ha : Placement.active (FiniteReturnStackAt.placement (44 : Fin count)) v=
      one (SelectedSourceBitsScan.word bs) bs.length := by
    rw [FiniteReturnStackAt.active_bank]
    simp [hc]
    rfl
  have hsmall := Placement.hoare_at (RawBitWordReset.runs (a := 2) bs)
    (FiniteReturnStackAt.placement (44 : Fin count)) v ha
  have h2 : HoareTime control (fun z => z=v) (fun z => z=afterControl v) (bs.length+2) := by
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
    (by simpa [afterControl,setTape] using hl)
    (by simpa [afterControl,setTape] using hh) hflags
  have h4 := BinaryDescriptorCleanupList.cleanup_hoare (a := 2) (by decide : 0<count)
    headerSlots (by decide) hs (afterFlags v) (by
      intro i hm
      have h := hd i hm
      simp only [headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hm
      rcases hm with rfl | rfl | rfl
      all_goals simpa [afterFlags,afterControl,setTape] using h)
  exact ((h2.seq h3).seq h4).consequence
    (fun _ h => h) (fun _ h => h) (by unfold cost; omega)

end
end IntegerMultBounds.Machine.UnitPhaseControlReset
