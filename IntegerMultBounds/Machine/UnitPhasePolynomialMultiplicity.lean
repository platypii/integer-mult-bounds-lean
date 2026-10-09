import IntegerMultBounds.Machine.UnitPhaseCountPower

/-! Read immutable external ell65 and physically construct the polynomial
coefficient count2^ell on60. Six temporary tapes are restored blank, every
other tape (including ell) is retained, and no payload inference is used. -/
namespace IntegerMultBounds.Machine.UnitPhasePolynomialMultiplicity
noncomputable section
open SharedPlacementAlphabet (setTape)

def slots : Fin 8 → Fin 66 := ![28,29,30,31,32,60,33,65]
theorem injective : Function.Injective slots := by decide
def placement : Fin (8+58) ≃ Fin 66 := InjectivePlacement.placement slots injective (by decide)
def program := Placement.placed (FixedBasePowerDescriptor.program (q := 2) 2) placement

def output (v : Tapes 66 2) (ell : ℕ) :=
  setTape v 60 (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (2^ell))) 1

theorem runs (v : Tapes 66 2) (ell : ℕ)
    (he : v.tape 65=RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits ell) ∧ v.head 65=1)
    (hb : ∀ i : Fin 7,v.tape (slots i.castSucc)=(fun _ => blank) ∧ v.head (slots i.castSucc)=0) :
    HoareTime program (fun z => z=v) (fun z => z=output v ell)
      (FixedBasePowerDescriptor.constant 2*2^ell) := by
  have ha : Placement.active placement v=FixedBasePowerDescriptor.input (RecursiveChildQuotientsConstant.bits ell) := by
    rw [placement,InjectivePlacement.active_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first
      | exact (hb 0).2 | exact (hb 1).2 | exact (hb 2).2 | exact (hb 3).2
      | exact (hb 4).2 | exact (hb 5).2 | exact (hb 6).2 | exact he.2
      | exact (hb 0).1 | exact (hb 1).1 | exact (hb 2).1 | exact (hb 3).1
      | exact (hb 4).1 | exact (hb 5).1 | exact (hb 6).1
      | exact he.1.trans (CountedLoopReuseAlphabet.encoding_binary _)
  have hs := (FixedBasePowerDescriptor.constructs (q := 2) 2 ell (by decide)
    (RecursiveChildQuotientsConstant.bits ell) (RecursiveChildQuotientsConstant.bits_value _)).consequence
    (fun _ h => h) (fun _ h => h)
    (FixedBasePowerDescriptor.cost_linear 2 ell (by decide) _
      (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _))
  apply (Placement.hoare_at hs placement v ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [FixedBasePowerDescriptor.output,PackedOffsetPowerHeader.power_bits,← ha,
    PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot]
  rfl

end
end IntegerMultBounds.Machine.UnitPhasePolynomialMultiplicity
