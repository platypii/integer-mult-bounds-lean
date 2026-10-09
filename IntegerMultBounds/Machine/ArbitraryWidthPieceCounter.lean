import IntegerMultBounds.Machine.BinaryDescriptorDivMod
import IntegerMultBounds.Machine.BinaryCanonicalData
import IntegerMultBounds.Machine.BinaryDescriptorInstall

/-! The physical fixed-base digit-extraction boundary for the arbitrary-width
controller. No digit list or runtime quotient is supplied to the program.
This module does not yet compile the outer piece-dispatch loop. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthPieceCounter
noncomputable section
variable {a : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits)

def input (ys : List Bool) : Tapes 14 a :=
  setTape (SharedBank.empty 14 a) (0 : Fin 14) (BinaryDescriptorStack.descriptor ys) 1

def emitted (ys zs rs : List Bool) : Tapes 14 a :=
  setTape (setTape (input ys) (5 : Fin 14) (BinaryDescriptorStack.descriptor zs) 1)
    (6 : Fin 14) (BinaryDescriptorStack.descriptor rs) 1

def initializer (B : ℕ) := Placement.placed (RecursiveChildQuotientsConstant.program (a := a) B)
  (FiniteReturnStackAt.placement (1 : Fin 14))

def extract (B : ℕ) := seq (seq (initializer (a := a) B) (BinaryDescriptorDivMod.program a))
  (BinaryDescriptorCleanupList.oneProgram (1 : Fin 14))

def extractCost (B : ℕ) (ys : List Bool) := RecursiveChildQuotientsConstant.cost B+
  BinaryDescriptorDivMod.cost ys (bits B)+2*(bits B).length+6

theorem extract_hoare (B : ℕ) (hB : 2 ≤ B) (ys : List Bool) :
    ∃ zs rs : List Bool, GrowingCounterData.Canonical zs ∧ GrowingCounterData.Canonical rs ∧
      Counter.value zs = Counter.value ys/B ∧ Counter.value rs = Counter.value ys%B ∧
      HoareTime (extract (a := a) B) (fun v => v = input ys)
        (fun v => v = emitted ys zs rs) (extractCost B ys) := by
  have hi := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) B)
    (FiniteReturnStackAt.placement (1 : Fin 14)) (input (a := a) ys)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  have hi' : HoareTime (initializer (a := a) B) (fun v => v = input ys)
      (fun v => v = BinaryDescriptorDivMod.input ys (bits B)) (RecursiveChildQuotientsConstant.cost B) := by
    apply hi.consequence (fun _ h => h) _ le_rfl
    rintro v ⟨w,rfl,rfl⟩
    rw [FiniteReturnStackAt.replace_bank]
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  obtain ⟨zs,rs,hzc,hrc,hzv,hrv,_,_,hd⟩ := BinaryDescriptorDivMod.divmod_hoare (a := a) ys (bits B)
    (by rw [RecursiveChildQuotientsConstant.bits_value]; omega)
  rw [RecursiveChildQuotientsConstant.bits_value] at hzv hrv
  have hc := BinaryDescriptorCleanupList.one_hoare (1 : Fin 14)
    (BinaryDescriptorDivMod.output (a := a) ys (bits B) zs rs) (bits B) rfl rfl
  have he : setTape (BinaryDescriptorDivMod.output (a := a) ys (bits B) zs rs) (1 : Fin 14)
      (fun _ => blank) 0 = emitted ys zs rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hc
  exact ⟨zs,rs,hzc,hrc,hzv,hrv,((hi'.seq hd).seq hc).consequence
    (fun _ h => h) (fun _ h => h) (by unfold extractCost; omega)⟩

theorem extract_canonical (B : ℕ) (hB : 2 ≤ B) (ys : List Bool) :
    HoareTime (extract (a := a) B) (fun v => v = input ys)
      (fun v => v = emitted ys (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
      (extractCost B ys) := by
  obtain ⟨zs,rs,hzc,hrc,hzv,hrv,h⟩ := extract_hoare (a := a) B hB ys
  have hz : zs = bits (Counter.value ys/B) := BinaryCanonicalData.value_injective _ _ hzc
    (RecursiveChildQuotientsConstant.bits_canonical _) (hzv.trans (RecursiveChildQuotientsConstant.bits_value _).symm)
  have hr : rs = bits (Counter.value ys%B) := BinaryCanonicalData.value_injective _ _ hrc
    (RecursiveChildQuotientsConstant.bits_canonical _) (hrv.trans (RecursiveChildQuotientsConstant.bits_value _).symm)
  simpa only [hz,hr] using h

def constant (B : ℕ) := RecursiveChildQuotientsConstant.cost B+2*(bits B).length+6+
  BinaryDescriptorDivMod.linearConstant (bits B)

theorem extract_linear (B : ℕ) (hB : 2 ≤ B) (ys : List Bool) (hy : GrowingCounterData.Canonical ys) :
    HoareTime (extract (a := a) B) (fun v => v = input ys)
      (fun v => v = emitted ys (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
      (constant B*(Counter.value ys+1)) := by
  apply (extract_canonical (a := a) B hB ys).consequence (fun _ h => h) (fun _ h => h)
  have hd := BinaryDescriptorDivMod.cost_linear ys (bits B) hy
  have hm := Nat.mul_le_mul_left (RecursiveChildQuotientsConstant.cost B+2*(bits B).length+6)
    (show 1 ≤ Counter.value ys+1 by omega)
  unfold extractCost constant
  nlinarith

def ready (zs rs : List Bool) : Tapes 14 a :=
  setTape (input zs) (6 : Fin 14) (BinaryDescriptorStack.descriptor rs) 1

def rotate : Program 14 ((4+5)+4) a := seq
  (seq (BinaryDescriptorCleanupList.oneProgram (0 : Fin 14))
    (BinaryDescriptorInstall.program a (5 : Fin 14) 0 (by decide)))
  (BinaryDescriptorCleanupList.oneProgram (5 : Fin 14))

theorem rotate_hoare (ys zs rs : List Bool) :
    HoareTime (rotate (a := a)) (fun v => v = emitted ys zs rs)
      (fun v => v = ready zs rs) (2*ys.length+4*zs.length+15) := by
  let v1 := setTape (emitted (a := a) ys zs rs) (0 : Fin 14) (fun _ => blank) 0
  let v2 := setTape v1 (0 : Fin 14) (RadixZeroFill.encodedBinary zs) 1
  have he := BinaryDescriptorCleanupList.one_hoare (0 : Fin 14) (emitted (a := a) ys zs rs) ys rfl rfl
  have hi := BinaryDescriptorInstall.install_hoare (5 : Fin 14) (0 : Fin 14) (by decide) v1 zs
    (by change BinaryDescriptorStack.descriptor zs = _; exact BinaryDescriptorStackRoundtrip.descriptor_encoded zs)
    rfl rfl rfl
  have hc := BinaryDescriptorCleanupList.one_hoare (5 : Fin 14) v2 zs rfl rfl
  have hf : setTape v2 (5 : Fin 14) (fun _ => blank) 0 = ready zs rs := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact (BinaryDescriptorStackRoundtrip.descriptor_encoded zs).symm
  rw [hf] at hc
  exact ((he.seq hi).seq hc).consequence (fun _ h => h) (fun _ h => h) (by omega)

def stage (B : ℕ) := seq (extract (a := a) B) rotate
def stageCost (B : ℕ) (ys : List Bool) := extractCost B ys+2*ys.length+
  4*(bits (Counter.value ys/B)).length+16

/-- Actual reusable control boundary: the quotient has physically replaced
the old remaining width, the digit is available on tape six, and every other
tape and head is clean. A continuation must consume and erase this digit. -/
theorem stage_hoare (B : ℕ) (hB : 2 ≤ B) (ys : List Bool) :
    HoareTime (stage (a := a) B) (fun v => v = input ys)
      (fun v => v = ready (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
      (stageCost B ys) := by
  exact ((extract_canonical (a := a) B hB ys).seq
    (rotate_hoare ys (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))).consequence
    (fun _ h => h) (fun _ h => h) (by unfold stageCost; omega)

def stageConstant (B : ℕ) := constant B+22

theorem stageCost_linear (B : ℕ) (ys : List Bool) (hy : GrowingCounterData.Canonical ys) :
    stageCost B ys ≤ stageConstant B*(Counter.value ys+1) := by
  have hd := BinaryDescriptorDivMod.cost_linear ys (bits B) hy
  have hc := Nat.mul_le_mul_left (RecursiveChildQuotientsConstant.cost B+2*(bits B).length+6)
    (show 1 ≤ Counter.value ys+1 by omega)
  have hyw := GrowingCounterData.canonical_width ys hy
  have hyl := Nat.log2_le_self (Counter.value ys)
  have hqw := GrowingCounterData.canonical_width (bits (Counter.value ys/B))
    (RecursiveChildQuotientsConstant.bits_canonical _)
  rw [RecursiveChildQuotientsConstant.bits_value] at hqw
  have hql := Nat.log2_le_self (Counter.value ys/B)
  have hq := Nat.div_le_self (Counter.value ys) B
  unfold stageCost stageConstant extractCost constant
  nlinarith

theorem stage_linear (B : ℕ) (hB : 2 ≤ B) (ys : List Bool) (hy : GrowingCounterData.Canonical ys) :
    HoareTime (stage (a := a) B) (fun v => v = input ys)
      (fun v => v = ready (bits (Counter.value ys/B)) (bits (Counter.value ys%B)))
      (stageConstant B*(Counter.value ys+1)) :=
  (stage_hoare (a := a) B hB ys).consequence (fun _ h => h) (fun _ h => h) (stageCost_linear B ys hy)

end
end IntegerMultBounds.Machine.ArbitraryWidthPieceCounter
