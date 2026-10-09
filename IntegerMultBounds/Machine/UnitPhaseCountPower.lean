import IntegerMultBounds.Machine.UnitPhaseAddressHeaders
import IntegerMultBounds.Machine.PackedOffsetPowerHeader
import IntegerMultBounds.Machine.PlacedDescriptorConstruction

/-! Construct the actual full-address power2^bits from the physically derived
width22. Output23 is the generated power; six temporary tapes28–33 are blank
again, and every original/header tape is retained. -/
namespace IntegerMultBounds.Machine.UnitPhaseCountPower
noncomputable section
open CompactGadgetReservationShape (Shape)
open ActivePrefixStageParameters
open ActivePrefixStageHeadersData (Order)
open ActiveRepairRankHeadersCommands (bank)
open SharedPlacementAlphabet (setTape)
variable {s : Shape}

def slots : Fin 8 → Fin 43 := ![28,29,30,31,32,23,33,22]
theorem injective : Function.Injective slots := by decide
def placement : Fin (8+35) ≃ Fin 43 := InjectivePlacement.placement slots injective (by decide)
def program := Placement.placed (FixedBasePowerDescriptor.program (q := 2) 2) placement
def input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  bank (a := 2) (UnitPhaseAddressHeaders.finished order v rows axis)
def output (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :=
  setTape (input order v rows axis) 23
    (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (2^s.bits))) 1

private theorem active_input (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    Placement.active placement (input order v rows axis)=
      FixedBasePowerDescriptor.input (RecursiveChildQuotientsConstant.bits s.bits) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first | rfl | exact CountedLoopReuseAlphabet.encoding_binary _

private theorem replaced (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    Placement.replace placement (input order v rows axis)
      (FixedBasePowerDescriptor.output 2 s.bits (RecursiveChildQuotientsConstant.bits s.bits))=
        output order v rows axis := by
  rw [FixedBasePowerDescriptor.output,PackedOffsetPowerHeader.power_bits,←active_input,
    PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot]
  rfl

theorem runs (order : Order) (v : Stage s) (rows : ℕ) (axis : Fin v.f) :
    HoareTime program (fun z => z=input order v rows axis) (fun z => z=output order v rows axis)
      (FixedBasePowerDescriptor.constant 2*2^s.bits) := by
  have hsmall := (FixedBasePowerDescriptor.constructs (q := 2) 2 s.bits (by decide)
    (RecursiveChildQuotientsConstant.bits s.bits) (RecursiveChildQuotientsConstant.bits_value _)).consequence
    (fun _ h => h) (fun _ h => h)
    (FixedBasePowerDescriptor.cost_linear 2 s.bits (by decide) _
      (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _))
  apply (Placement.hoare_at hsmall placement (input order v rows axis)
    (active_input order v rows axis)).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  exact replaced order v rows axis

end
end IntegerMultBounds.Machine.UnitPhaseCountPower
