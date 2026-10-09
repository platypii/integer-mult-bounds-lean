import IntegerMultBounds.Machine.UnitPhaseCountPower

/-! Polynomial multiplicity is physically constructed from an immutable
canonical ell scalar on port65. It is stored on60, and all six construction
scratch tapes are restored. No multiplicity descriptor is supplied for free. -/
namespace IntegerMultBounds.Machine.UnitPhaseMultiplicity
noncomputable section
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def slots : Fin 8 → Fin 66 := ![28,29,30,31,32,60,33,65]
theorem injective : Function.Injective slots := by decide
def placement : Fin (8+58) ≃ Fin 66 := InjectivePlacement.placement slots injective (by decide)
def program := Placement.placed (FixedBasePowerDescriptor.program (q := 2) 2) placement

def output (v : Tapes 66 2) (ell : ℕ) :=
  setTape v 60 (RadixZeroFill.encodedBinary (bits (2^ell))) 1

theorem active_input (v : Tapes 66 2) (ell : ℕ)
    (he : v.head 65=1 ∧ v.tape 65=CountedLoopReuseAlphabet.binary (bits ell))
    (hb : ∀ i : Fin 7,v.head (slots (Fin.castSucc i))=0 ∧
      v.tape (slots (Fin.castSucc i))=(fun _ => blank)) :
    Placement.active placement v=FixedBasePowerDescriptor.input (bits ell) := by
  rw [placement,InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
  all_goals first
    | exact (hb 0).1 | exact (hb 1).1 | exact (hb 2).1 | exact (hb 3).1
    | exact (hb 4).1 | exact (hb 5).1 | exact (hb 6).1 | exact he.1
    | exact (hb 0).2 | exact (hb 1).2 | exact (hb 2).2 | exact (hb 3).2
    | exact (hb 4).2 | exact (hb 5).2 | exact (hb 6).2 | exact he.2

theorem runs (v : Tapes 66 2) (ell : ℕ)
    (he : v.head 65=1 ∧ v.tape 65=CountedLoopReuseAlphabet.binary (bits ell))
    (hb : ∀ i : Fin 7,v.head (slots (Fin.castSucc i))=0 ∧
      v.tape (slots (Fin.castSucc i))=(fun _ => blank)) :
    HoareTime program (fun z => z=v) (fun z => z=output v ell)
      (FixedBasePowerDescriptor.constant 2*2^ell) := by
  have ha := active_input v ell he hb
  have hsmall := (FixedBasePowerDescriptor.constructs (q := 2) 2 ell (by decide)
    (bits ell) (RecursiveChildQuotientsConstant.bits_value _)).consequence
    (fun _ h => h) (fun _ h => h)
    (FixedBasePowerDescriptor.cost_linear 2 ell (by decide) _
      (RecursiveChildQuotientsConstant.bits_value _) (RecursiveChildQuotientsConstant.bits_canonical _))
  apply (Placement.hoare_at hsmall placement v ha).consequence (fun _ h => h) _ le_rfl
  rintro z ⟨small,rfl,rfl⟩
  rw [FixedBasePowerDescriptor.output,PackedOffsetPowerHeader.power_bits,←ha,
    PlacedDescriptorConstruction.replace_setTape]
  simp only [placement,InjectivePlacement.active_slot]
  rfl

end
end IntegerMultBounds.Machine.UnitPhaseMultiplicity
