import IntegerMultBounds.Machine.FixedBasePowerStep
import IntegerMultBounds.Machine.FixedBasePowerDescriptor
import IntegerMultBounds.Machine.BinaryDescriptorIncrement
import IntegerMultBounds.Machine.BinaryCanonicalData

/-! Physical paired depth/power control for the arbitrary-width digit loop.
The base is initialized once and retained across level changes. Arbitrary
offset and data spectators are preserved by ordinary tape framing. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthLevelAdvance
noncomputable section
variable {a t : ℕ}
open SharedPlacementAlphabet (setTape)
open RecursiveChildQuotientsConstant (bits cost)

def bank (bs ps ks : List Bool) : Tapes 7 a :=
  (FixedBasePowerStep.input bs ps).append
    (FiniteReturnStack.bank (BinaryDescriptorStack.descriptor ks) 1)

def working (B j : ℕ) : Tapes 7 a := bank (bits B) (FixedBasePowerStep.bits B j) (bits j)

def increment : Program 7 3 a := Placement.placed BinaryDescriptorIncrement.program
  (FiniteReturnStackAt.placement (6 : Fin 7))

private theorem increment_hoare (bs ps ks : List Bool) :
    HoareTime (increment (a := a)) (fun v => v = bank bs ps ks)
      (fun v => v = bank bs ps (GrowingCounterData.increment ks)) (2*(ks.length+1)) := by
  have h := Placement.hoare_at (BinaryDescriptorIncrement.increment_linear (q := a) ks)
    (FiniteReturnStackAt.placement (6 : Fin 7)) (bank (a := a) bs ps ks)
    (by rw [FiniteReturnStackAt.active_bank]; rfl)
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  change Placement.replace _ _ (FiniteReturnStack.bank
    (BinaryDescriptorStack.descriptor (GrowingCounterData.increment ks)) 1) = _
  rw [FiniteReturnStackAt.replace_bank]
  apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl

def advance : Program 7 (53+3) a := seq (extend FixedBasePowerStep.program 1) increment
def advanceCost (B j : ℕ) := 110*B^(j+1)+2*((bits j).length+1)+1

/-- Both emitted controls are canonical; multiplication and carry propagation
are actual fixed finite subprograms, and every private slot is blank again. -/
theorem advance_hoare (B j : ℕ) (hB : 2 ≤ B) :
    HoareTime (advance (a := a)) (fun v => v = working B j)
      (fun v => v = working B (j+1)) (advanceCost B j) := by
  have hp := hoare_extend_eq (FixedBasePowerStep.power_step (q := a) (bits B) B j hB
    (RecursiveChildQuotientsConstant.bits_value B) (RecursiveChildQuotientsConstant.bits_canonical B))
    (FiniteReturnStack.bank (a := a) (BinaryDescriptorStack.descriptor (bits j)) 1)
  have hi := increment_hoare (a := a) (bits B) (FixedBasePowerStep.bits B (j+1)) (bits j)
  have hk : GrowingCounterData.increment (bits j) = bits (j+1) :=
    BinaryCanonicalData.value_injective _ _
      (BinaryDescriptorIncrement.canonical _ (RecursiveChildQuotientsConstant.bits_canonical _))
      (RecursiveChildQuotientsConstant.bits_canonical _)
      (by rw [BinaryDescriptorIncrement.value,RecursiveChildQuotientsConstant.bits_value,
        RecursiveChildQuotientsConstant.bits_value])
  rw [hk] at hi
  exact (hp.seq hi).consequence (fun _ h => h) (fun _ h => h) (by unfold advanceCost; omega)

theorem advance_linear (B j : ℕ) (hB : 2 ≤ B) :
    HoareTime (advance (a := a)) (fun v => v = working B j)
      (fun v => v = working B (j+1)) (120*B^(j+1)) := by
  apply (advance_hoare (a := a) B j hB).consequence (fun _ h => h) (fun _ h => h)
  have hw := GrowingCounterData.canonical_width (bits j) (RecursiveChildQuotientsConstant.bits_canonical j)
  rw [RecursiveChildQuotientsConstant.bits_value] at hw
  have hl := Nat.log2_le_self j
  have hp := FixedBasePowerDescriptor.depth_le_power B (j+1) hB
  unfold advanceCost
  omega

/-- Offset, remaining width, digit counter, serialized data and caller headers
may all occupy this arbitrary fixed frame, with no hidden changes or resets. -/
theorem advance_framed (B j : ℕ) (hB : 2 ≤ B) (frame : Tapes t a) :
    HoareTime (extend (advance (a := a)) t)
      (fun v => v = (working B j).append frame)
      (fun v => v = (working B (j+1)).append frame) (120*B^(j+1)) :=
  hoare_extend_eq (advance_linear B j hB) frame

def initializer (n : ℕ) (slot : Fin 7) := Placement.placed
  (RecursiveChildQuotientsConstant.program (a := a) n) (FiniteReturnStackAt.placement slot)

private theorem initialize_hoare (n : ℕ) (slot : Fin 7) (v : Tapes 7 a)
    (ht : v.tape slot = fun _ => blank) (hp : v.head slot = 0) :
    HoareTime (initializer n slot) (fun w => w = v)
      (fun w => w = setTape v slot (BinaryDescriptorStack.descriptor (bits n)) 1) (cost n) := by
  have h := Placement.hoare_at (RecursiveChildQuotientsConstant.initialize_hoare (a := a) n)
    (FiniteReturnStackAt.placement slot) v (by rw [FiniteReturnStackAt.active_bank,ht,hp])
  apply h.consequence (fun _ h => h) _ le_rfl
  rintro w ⟨z,rfl,rfl⟩
  exact FiniteReturnStackAt.replace_bank _ _ _ _

def setup (B : ℕ) := seq (seq (initializer (a := a) B 3) (initializer 1 5)) (initializer 0 6)

theorem setup_hoare (B : ℕ) :
    HoareTime (setup (a := a) B) (fun v => v = SharedBank.empty 7 a)
      (fun v => v = working B 0) (cost B+cost 1+cost 0+2) := by
  let v1 := setTape (SharedBank.empty 7 a) (3 : Fin 7) (BinaryDescriptorStack.descriptor (bits B)) 1
  let v2 := setTape v1 (5 : Fin 7) (BinaryDescriptorStack.descriptor (bits 1)) 1
  have h1 := initialize_hoare B (3 : Fin 7) (SharedBank.empty 7 a) rfl rfl
  have h2 := initialize_hoare 1 (5 : Fin 7) v1 rfl rfl
  have h3 := initialize_hoare 0 (6 : Fin 7) v2 rfl rfl
  have he : setTape v2 (6 : Fin 7) (BinaryDescriptorStack.descriptor (bits 0)) 1 = working B 0 := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i
    all_goals first | rfl | exact BinaryDescriptorStackRoundtrip.descriptor_encoded _
  rw [he] at h3
  exact (h1.seq h2).seq h3

def unbased (B j : ℕ) : Tapes 7 a := setTape (working B j) (3 : Fin 7) (fun _ => blank) 0
def cleanBase : Program 7 4 a := BinaryDescriptorCleanupList.oneProgram (3 : Fin 7)

theorem cleanBase_hoare (B j : ℕ) :
    HoareTime (cleanBase (a := a)) (fun v => v = working B j)
      (fun v => v = unbased B j) (2*(bits B).length+4) :=
  BinaryDescriptorCleanupList.one_hoare (3 : Fin 7) (working B j) (bits B)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl

def finish : Program 7 ((4+4)+4) a := seq (seq cleanBase
  (BinaryDescriptorCleanupList.oneProgram (5 : Fin 7)))
  (BinaryDescriptorCleanupList.oneProgram (6 : Fin 7))

theorem finish_hoare (B j : ℕ) :
    HoareTime (finish (a := a)) (fun v => v = working B j)
      (fun v => v = SharedBank.empty 7 a)
      (2*(bits B).length+2*(FixedBasePowerStep.bits B j).length+2*(bits j).length+14) := by
  let v1 := unbased (a := a) B j
  let v2 := setTape v1 (5 : Fin 7) (fun _ => blank) 0
  have hb := cleanBase_hoare (a := a) B j
  have hw := BinaryDescriptorCleanupList.one_hoare (5 : Fin 7) v1 (FixedBasePowerStep.bits B j)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have hd := BinaryDescriptorCleanupList.one_hoare (6 : Fin 7) v2 (bits j) rfl rfl
  have he : setTape v2 (6 : Fin 7) (fun _ => blank) 0 = SharedBank.empty 7 a := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [he] at hd
  exact ((hb.seq hw).seq hd).consequence (fun _ h => h) (fun _ h => h) (by omega)

theorem controls (B j : ℕ) :
    (working (a := a) B j).head 5 = 1 ∧
    (working (a := a) B j).tape 5 = RadixZeroFill.encodedBinary (FixedBasePowerStep.bits B j) ∧
    (working (a := a) B j).head 6 = 1 ∧
    (working (a := a) B j).tape 6 = BinaryDescriptorStack.descriptor (bits j) := ⟨rfl,rfl,rfl,rfl⟩

theorem width_bits_eq (B j : ℕ) : FixedBasePowerStep.bits B j = bits (B^j) :=
  BinaryCanonicalData.value_injective _ _ (FixedBasePowerStep.bits_canonical B j)
    (RecursiveChildQuotientsConstant.bits_canonical _) (by
      rw [FixedBasePowerStep.bits_value,RecursiveChildQuotientsConstant.bits_value])

theorem setup_framed (B : ℕ) (frame : Tapes t a) :
    HoareTime (extend (setup (a := a) B) t)
      (fun v => v = (SharedBank.empty 7 a).append frame)
      (fun v => v = (working B 0).append frame) (cost B+cost 1+cost 0+2) :=
  hoare_extend_eq (setup_hoare B) frame

theorem finish_linear (B j : ℕ) (hB : 2 ≤ B) :
    HoareTime (finish (a := a)) (fun v => v = working B j)
      (fun v => v = SharedBank.empty 7 a) ((2*(bits B).length+20)*B^j) := by
  apply (finish_hoare (a := a) B j).consequence (fun _ h => h) (fun _ h => h)
  have hw := GrowingCounterData.canonical_width (FixedBasePowerStep.bits B j)
    (FixedBasePowerStep.bits_canonical B j)
  rw [FixedBasePowerStep.bits_value] at hw
  have hwl := Nat.log2_le_self (B^j)
  have hd := GrowingCounterData.canonical_width (bits j) (RecursiveChildQuotientsConstant.bits_canonical j)
  rw [RecursiveChildQuotientsConstant.bits_value] at hd
  have hdl := Nat.log2_le_self j
  have hp := FixedBasePowerDescriptor.depth_le_power B j hB
  have hc := Nat.mul_le_mul_left (2*(bits B).length+16) (show 1 ≤ B^j by omega)
  nlinarith

theorem finish_framed (B j : ℕ) (hB : 2 ≤ B) (frame : Tapes t a) :
    HoareTime (extend (finish (a := a)) t)
      (fun v => v = (working B j).append frame)
      (fun v => v = (SharedBank.empty 7 a).append frame) ((2*(bits B).length+20)*B^j) :=
  hoare_extend_eq (finish_linear B j hB) frame

end
end IntegerMultBounds.Machine.ArbitraryWidthLevelAdvance
