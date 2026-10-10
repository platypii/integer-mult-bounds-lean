import IntegerMultBounds.Machine.AllAxisPhaseFlagsCaller
import IntegerMultBounds.Machine.UnitPhasePolynomialLoop
import IntegerMultBounds.Machine.UnitPhaseControlReset

/-! The aggregated phase bank shares the existing polynomial flags/core
layout, so one retained all-axis phase feeds the actual coefficient loop. -/
namespace IntegerMultBounds.Machine.AllAxisPhaseFlagsEndpoint
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open AllAxisPhaseFlagsCaller
variable {s : Shape}

private theorem head_slot (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (j : Fin 6) :
    (output order v rows m ws addr tail).head (scanSlots j)=
      (RepeatedWeightedPhaseHeader.boundary (phase v m ws addr)
        (SelectedSourceBitsScan.word (controls v m addr)) (m*v.f)
        (RecursiveChildQuotientsConstant.bits v.f)).head j :=
  InjectivePlacement.replace_head_slot scanSlots scanInjective (by decide : 6+50=56) _ _ j
private theorem tape_slot (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (j : Fin 6) :
    (output order v rows m ws addr tail).tape (scanSlots j)=
      (RepeatedWeightedPhaseHeader.boundary (phase v m ws addr)
        (SelectedSourceBitsScan.word (controls v m addr)) (m*v.f)
        (RecursiveChildQuotientsConstant.bits v.f)).tape j :=
  InjectivePlacement.replace_tape_slot scanSlots scanInjective (by decide : 6+50=56) _ _ j

/-- The actual aggregate flags occupy the unchanged coefficient-kernel ports. -/
theorem flags (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (z : Tapes 4 2) :
    UnitPhasePolynomialLoop.flagsAt ((output order v rows m ws addr tail).append z) (phase v m ws addr) := by
  intro i
  fin_cases i
  · exact ⟨head_slot order v rows m ws addr tail 0,tape_slot order v rows m ws addr tail 0⟩
  · exact ⟨head_slot order v rows m ws addr tail 1,tape_slot order v rows m ws addr tail 1⟩

private theorem head_other (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (k : Fin 56) (hk : ∀ j : Fin 6,scanSlots j≠k) :
    (output order v rows m ws addr tail).head k=(extracted order v rows m addr tail).head k := by
  exact Placement.replace_head_other scanPlacement _ _ k (by simpa only [scanPlacement,InjectivePlacement.active_slot] using hk)
private theorem tape_other (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (k : Fin 56) (hk : ∀ j : Fin 6,scanSlots j≠k) :
    (output order v rows m ws addr tail).tape k=(extracted order v rows m addr tail).tape k := by
  exact Placement.replace_tape_other scanPlacement _ _ k (by simpa only [scanPlacement,InjectivePlacement.active_slot] using hk)

theorem core (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (z : Tapes 4 2) :
    UnitPhasePolynomialLoop.coreBlank
      ((output order v rows m ws addr (SharedBank.empty 6 2)).append z) := by
  intro i
  have hk : ∀ j : Fin 6,scanSlots j≠(⟨50+i.val,by omega⟩ : Fin 56) := by
    intro j
    have hi := i.isLt
    fin_cases j <;> simp [scanSlots,Fin.ext_iff] <;> omega
  have hh := head_other order v rows m ws addr (SharedBank.empty 6 2) ⟨50+i.val,by omega⟩ hk
  have ht := tape_other order v rows m ws addr (SharedBank.empty 6 2) ⟨50+i.val,by omega⟩ hk
  fin_cases i <;> exact ⟨hh,ht⟩

theorem control (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) :
    (output order v rows m ws addr tail).head 44=(controls v m addr).length ∧
      (output order v rows m ws addr tail).tape 44=SelectedSourceBitsScan.word (controls v m addr) := by
  have hh := head_slot order v rows m ws addr tail 2
  have ht := tape_slot order v rows m ws addr tail 2
  simpa only [controls,SelectedSourceBitsData.selected_length] using ⟨hh,ht⟩

def headerWords (v : Stage s) (m : ℕ) (i : Fin 60) : List Bool :=
  if i=22 then RecursiveChildQuotientsConstant.bits s.chunk else
  if i=23 then RecursiveChildQuotientsConstant.bits (m*v.f-1) else
  if i=24 then RecursiveChildQuotientsConstant.bits (AllAxisPhaseHeadersData.offset v m) else []

theorem headers (order : Order) (v : Stage s) (rows m : ℕ) (ws : List (ZMod 4))
    (addr : List Bool) (tail : Tapes 6 2) (z : Tapes 4 2) :
    ∀ i ∈ UnitPhaseControlReset.headerSlots,
      ((output order v rows m ws addr tail).append z).head i=1 ∧
      ((output order v rows m ws addr tail).append z).tape i=
        BinaryDescriptorStack.descriptor (headerWords v m i) := by
  intro i hi
  simp only [UnitPhaseControlReset.headerSlots,List.mem_cons,List.not_mem_nil,or_false] at hi
  have hik : i.val<56 := by rcases hi with rfl | rfl | rfl <;> decide
  let k : Fin 56 := ⟨i.val,hik⟩
  have hk : ∀ j : Fin 6,scanSlots j≠k := by
    intro j
    rcases hi with rfl | rfl | rfl <;> fin_cases j <;> simp [k,scanSlots,Fin.ext_iff,UnitPhaseControlReset.count]
  have hh := head_other order v rows m ws addr tail k hk
  have ht := tape_other order v rows m ws addr tail k hk
  have hieq : Fin.castAdd 4 k=i := Fin.ext rfl
  rw [←hieq]
  simp only [Tapes.append,Fin.addCases_left]
  rw [hh,ht]
  rcases hi with rfl | rfl | rfl
  all_goals simp [k,headerWords,UnitPhaseControlReset.count,BinaryDescriptorStackRoundtrip.descriptor_encoded,extracted,AllAxisPhaseHeadersData.finished,AllAxisPhaseHeadersData.values,
    AllAxisPhaseHeadersData.initial,ActiveRepairRankHeadersCommands.bank,
    ActiveRepairRankHeadersCommands.put,ActiveRepairRankHeadersCommands.caller,
    CleanSubbank.bank,Tapes.append,Fin.addCases,Function.update]

end
end IntegerMultBounds.Machine.AllAxisPhaseFlagsEndpoint
