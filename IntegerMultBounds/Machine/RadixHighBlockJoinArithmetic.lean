import IntegerMultBounds.Machine.RadixHighBlockJoinSetup
import IntegerMultBounds.Machine.RadixHighBlockJoinPlacement

/-! Reusable physical prefix/suffix arithmetic inside ordered high-digit
movement. Fixed-base multiplication and exact quotient share thirteen blank
tapes, preserve every spectator and retain the supplied base descriptor. -/
namespace IntegerMultBounds.Machine.RadixHighBlockJoinArithmetic
noncomputable section
open RadixHighBlockJoinBank
open SharedPlacementAlphabet (setTape)
variable {q a : ℕ}

def workingSlot (g : Bool) : Fin (count q) := if g then prefixSlot else suffixSlot

def shrinkSlots (g : Bool) : Fin 14 → Fin (count q) :=
  fun i => Fin.addCases (m := 1) (n := 13) (fun _ => workingSlot g) (scratchSlot (q := q)) i

theorem shrinkSlots_injective (g : Bool) : Function.Injective (shrinkSlots (q := q) g) := by
  intro i j he
  have hv := congrArg Fin.val he
  fin_cases i <;> fin_cases j
  all_goals cases g <;> simp [shrinkSlots,Fin.addCases,workingSlot,prefixSlot,suffixSlot,scratchSlot] at hv
  all_goals first | rfl | omega

def shrinkPlacement (g : Bool) : Fin (14+(count q-14)) ≃ Fin (count q) :=
  InjectivePlacement.placement (shrinkSlots g) (shrinkSlots_injective g)
    (by unfold count RadixDigitMoveCore.count; omega)
def shrinkProgram (g : Bool) := Placement.placed (FixedBaseDescriptorQuotient.program (a := a) q) (shrinkPlacement (q := q) g)

def growSlots (g : Bool) : Fin 6 → Fin (count q) :=
  ![scratchSlot 0,scratchSlot 1,scratchSlot 2,baseSlot,scratchSlot 3,workingSlot g]

theorem growSlots_injective (g : Bool) : Function.Injective (growSlots (q := q) g) := by
  intro i j he
  have hv := congrArg Fin.val he
  cases g <;> fin_cases i <;> fin_cases j
  all_goals simp [growSlots,workingSlot,prefixSlot,suffixSlot,baseSlot,scratchSlot] at hv
  all_goals first | rfl | omega

def growPlacement (g : Bool) : Fin (6+(count q-6)) ≃ Fin (count q) :=
  InjectivePlacement.placement (growSlots g) (growSlots_injective g)
    (by unfold count RadixDigitMoveCore.count; omega)
def growProgram (g : Bool) := Placement.placed (FixedBasePowerStep.program (q := a)) (growPlacement (q := q) g)

private def restrict (v : Tapes (count q+2) a) : Tapes (count q) a :=
  ⟨fun i => v.head (Fin.castAdd 2 i),fun i => v.tape (Fin.castAdd 2 i)⟩
private theorem restrict_append (v : Tapes (count q) a) (c : Tapes 2 a) : restrict (v.append c) = v := by
  apply congrArg₂ Tapes.mk <;> funext i <;> simp only [restrict,Tapes.append,Fin.addCases_left]

private theorem set_working (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe ps es ws bs : List Bool) :
    setTape (bank (q := q) source ss op oe (some ps) (some es) (some ws)) (workingSlot g)
      (RadixZeroFill.encodedBinary bs) 1 =
    bank (q := q) source ss op oe (some (if g then bs else ps)) (some (if g then es else bs)) (some ws) := by
  let c := SharedBank.empty 2 a
  cases g
  · have h := congrArg (restrict (q := q) (a := a)) (RadixHighBlockJoinSetup.set_suffix source ss op oe bs (some ps) (some es) (some ws) c)
    simp only [RadixHighBlockJoinSetup.bank,RadixHighBlockJoinSetup.suffixSlot] at h
    unfold RadixHighBlockJoinSetup.total at h
    rw [SharedPlacementAlphabet.setTape_append_left] at h
    simp only [restrict_append] at h
    exact h
  · have h := congrArg (restrict (q := q) (a := a)) (RadixHighBlockJoinSetup.set_prefix source ss op oe bs (some ps) (some es) (some ws) c)
    simp only [RadixHighBlockJoinSetup.bank,RadixHighBlockJoinSetup.prefixSlot] at h
    unfold RadixHighBlockJoinSetup.total at h
    rw [SharedPlacementAlphabet.setTape_append_left] at h
    simp only [restrict_append] at h
    exact h

private theorem grow_active (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe ps es ws : List Bool) :
    Placement.active (growPlacement (q := q) g) (bank (q := q) source ss op oe (some ps) (some es) (some ws)) =
      FixedBasePowerStep.input ws (if g then ps else es) := by
  unfold growPlacement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> cases g <;> fin_cases i
  all_goals simp (disch := omega) [growSlots,workingSlot,bank,prefixSlot,suffixSlot,baseSlot,scratchSlot,
    spectatorSlot,originalPrefixSlot,originalSuffixSlot,DimensionProductDescriptor.input,
    RadixHighBlockJoinSetup.encoded_binary]
  all_goals (try split_ifs) <;> first | contradiction | omega | rfl

private theorem shrink_active (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe ps es ws : List Bool) :
    Placement.active (shrinkPlacement (q := q) g) (bank (q := q) source ss op oe (some ps) (some es) (some ws)) =
      ArbitraryWidthPieceCounter.input (if g then ps else es) := by
  unfold shrinkPlacement
  rw [InjectivePlacement.active_bank]
  apply congrArg₂ Tapes.mk <;> funext i
  all_goals induction i using Fin.addCases (m := 1) (n := 13) with
  | left i =>
    simp only [shrinkSlots,Fin.addCases_left]
    fin_cases i
    all_goals cases g <;>
      simp (disch := omega) [workingSlot,bank,prefixSlot,suffixSlot,baseSlot,scratchSlot,
        spectatorSlot,originalPrefixSlot,originalSuffixSlot,ArbitraryWidthPieceCounter.input,
        SharedBank.empty,setTape,Function.update_apply,Fin.ext_iff,
        RadixHighBlockJoinSetup.encoded_binary,RadixHighBlockJoinSetup.encoded_descriptor] <;>
      (try split_ifs) <;> first | contradiction | omega | rfl | exact (RadixHighBlockJoinSetup.encoded_binary _).symm.trans (RadixHighBlockJoinSetup.encoded_descriptor _)
  | right i =>
    simp only [shrinkSlots,Fin.addCases_right]
    fin_cases i
    all_goals simp (disch := omega) [bank,prefixSlot,suffixSlot,baseSlot,scratchSlot,
      spectatorSlot,originalPrefixSlot,originalSuffixSlot,ArbitraryWidthPieceCounter.input,
      SharedBank.empty,setTape,Function.update_apply,Fin.ext_iff]
    all_goals (try split_ifs) <;> first | contradiction | omega | rfl

/-- The only modified tape is the chosen working header. Every arithmetic
scratch head and symbol returns exactly to its prior blank configuration. -/
theorem grow_hoare (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (N : ℕ) (hq : 2 ≤ q) (hN : 0 < N)
    (hw : Counter.value ws = q) (hn : Counter.value (if g then ps else es) = N)
    (cw : GrowingCounterData.Canonical ws) (cn : GrowingCounterData.Canonical (if g then ps else es)) :
    HoareTime (growProgram (q := q) (a := a) g)
      (fun v => v = bank (q := q) source ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) source ss op oe
        (some (if g then DimensionProductDescriptor.bits N q else ps))
        (some (if g then es else DimensionProductDescriptor.bits N q)) (some ws)) (110*(N*q)) := by
  have h := Placement.hoare_at (FixedBasePowerStep.step_linear ws (if g then ps else es) N q (by omega) hN hw hn cw cn)
    (growPlacement (q := q) g) (bank (q := q) source ss op oe (some ps) (some es) (some ws)) (grow_active g source ss op oe ps es ws)
  have he : FixedBasePowerStep.input ws (DimensionProductDescriptor.bits N q) =
      setTape (FixedBasePowerStep.input (q := a) ws (if g then ps else es)) 5
        (RadixZeroFill.encodedBinary (DimensionProductDescriptor.bits N q)) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  apply h.consequence (fun _ hh => hh) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [he,← grow_active g source ss op oe ps es ws,PlacedDescriptorConstruction.replace_setTape]
  have hslot : (growPlacement (q := q) g) (Fin.castAdd (count q-6) (5 : Fin 6)) = workingSlot g := by
    rw [growPlacement,InjectivePlacement.active_slot]; rfl
  rw [hslot]
  exact set_working g source ss op oe ps es ws _

theorem shrink_hoare (g : Bool) (source : ℤ → Fin (a+4)) (ss op oe ps es ws : List Bool)
    (hq : 2 ≤ q) (cn : GrowingCounterData.Canonical (if g then ps else es)) :
    HoareTime (shrinkProgram (q := q) (a := a) g)
      (fun v => v = bank (q := q) source ss op oe (some ps) (some es) (some ws))
      (fun v => v = bank (q := q) source ss op oe
        (some (if g then RecursiveChildQuotientsConstant.bits (Counter.value ps/q) else ps))
        (some (if g then es else RecursiveChildQuotientsConstant.bits (Counter.value es/q))) (some ws))
      (FixedBaseDescriptorQuotient.constant q*(Counter.value (if g then ps else es)+1)) := by
  have h := Placement.hoare_at (FixedBaseDescriptorQuotient.quotient_hoare q hq (if g then ps else es) cn)
    (shrinkPlacement (q := q) g) (bank (q := q) source ss op oe (some ps) (some es) (some ws)) (shrink_active g source ss op oe ps es ws)
  have he : ArbitraryWidthPieceCounter.input (RecursiveChildQuotientsConstant.bits (Counter.value (if g then ps else es)/q)) =
      setTape (ArbitraryWidthPieceCounter.input (a := a) (if g then ps else es)) 0
        (RadixZeroFill.encodedBinary (RecursiveChildQuotientsConstant.bits (Counter.value (if g then ps else es)/q))) 1 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;>
      simp [ArbitraryWidthPieceCounter.input,setTape,Function.update_apply,SharedBank.empty,
        RadixHighBlockJoinSetup.encoded_descriptor]
  apply h.consequence (fun _ hh => hh) _ le_rfl
  rintro v ⟨small,rfl,rfl⟩
  rw [he,← shrink_active g source ss op oe ps es ws,PlacedDescriptorConstruction.replace_setTape]
  simp only [shrinkPlacement,InjectivePlacement.active_slot,shrinkSlots,Fin.addCases_left]
  have hh := set_working (q := q) g source ss op oe ps es ws
    (RecursiveChildQuotientsConstant.bits (Counter.value (if g then ps else es)/q))
  cases g <;> exact hh

end
end IntegerMultBounds.Machine.RadixHighBlockJoinArithmetic
