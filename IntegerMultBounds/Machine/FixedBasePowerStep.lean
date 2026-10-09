import IntegerMultBounds.Machine.DimensionProductDescriptor
import IntegerMultBounds.Machine.BinaryDescriptorCleanupList
import IntegerMultBounds.Machine.BinaryDescriptorInstall
import IntegerMultBounds.Machine.RecursiveChildQuotientsConstant

/-! A fixed binary-descriptor multiplication step for computing a fixed-base
power from a runtime exponent. The old value and temporary product are erased;
all workspace is blank again, with the base retained. -/
namespace IntegerMultBounds.Machine.FixedBasePowerStep
noncomputable section
variable {q : ℕ}
open SharedPlacementAlphabet (setTape)
abbrev input := @DimensionProductDescriptor.input
attribute [local irreducible] DimensionProductDescriptor.bits RecursiveChildQuotientsConstant.bits

def program : Program 6 53 q :=
  seq (seq (seq DimensionProductDescriptor.program
    (BinaryDescriptorCleanupList.oneProgram (5 : Fin 6)))
    (BinaryDescriptorInstall.program q (1 : Fin 6) 5 (by decide)))
    (BinaryDescriptorCleanupList.oneProgram (1 : Fin 6))

theorem step_hoare (ws ps : List Bool) (N B : ℕ) (hB : 0 < B)
    (hw : Counter.value ws = B) (hp : Counter.value ps = N)
    (cw : GrowingCounterData.Canonical ws) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (program (q := q)) (fun v => v = input ws ps)
      (fun v => v = input ws (DimensionProductDescriptor.bits N B))
      (53*(N*B)+2*ps.length+4*(DimensionProductDescriptor.bits N B).length+44) := by
  let out := DimensionProductDescriptor.output (q := q) ws ps N B
  let cleared := setTape out (5 : Fin 6) (fun _ => blank) 0
  let copied := setTape cleared (5 : Fin 6)
    (RadixZeroFill.encodedBinary (DimensionProductDescriptor.bits N B)) 1
  have hh := DimensionProductDescriptor.construct_hoare (q := q) ws ps N B hB hw hp cw cp
  have he := BinaryDescriptorCleanupList.one_hoare (5 : Fin 6) out ps
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have hc := BinaryDescriptorInstall.install_hoare (1 : Fin 6) (5 : Fin 6) (by decide)
    cleared (DimensionProductDescriptor.bits N B) rfl rfl rfl rfl
  have ht := BinaryDescriptorCleanupList.one_hoare (1 : Fin 6) copied
    (DimensionProductDescriptor.bits N B)
    (by rw [BinaryDescriptorStackRoundtrip.descriptor_encoded]; rfl) rfl
  have hfinal : setTape copied (1 : Fin 6) (fun _ => blank) 0 =
      input ws (DimensionProductDescriptor.bits N B) := by
    apply congrArg₂ Tapes.mk <;> funext i <;> fin_cases i <;> rfl
  rw [hfinal] at ht
  exact (((hh.seq he).seq hc).seq ht).consequence (fun _ h => h) (fun _ h => h) (by omega)

/-- The actual step costs a fixed multiple of the new positive value. -/
theorem step_linear (ws ps : List Bool) (N B : ℕ) (hB : 1 ≤ B) (hN : 0 < N)
    (hw : Counter.value ws = B) (hp : Counter.value ps = N)
    (cw : GrowingCounterData.Canonical ws) (cp : GrowingCounterData.Canonical ps) :
    HoareTime (program (q := q)) (fun v => v = input ws ps)
      (fun v => v = input ws (DimensionProductDescriptor.bits N B)) (110*(N*B)) := by
  have hn := GrowingCounterData.canonical_width ps cp
  have hl := Nat.log2_le_self N
  rw [hp] at hn
  have hd := GrowingCounterData.canonical_width (DimensionProductDescriptor.bits N B)
    (DimensionProductDescriptor.bits_canonical N B)
  rw [DimensionProductDescriptor.bits_value] at hd
  have hld := Nat.log2_le_self (N*B)
  have hmul : N ≤ N*B := by nlinarith
  have hpos : 0 < N*B := Nat.mul_pos hN (by omega)
  exact (step_hoare ws ps N B (by omega) hw hp cw cp).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- These are the literal lists emitted at successive physical step boundaries. -/
def bits (B : ℕ) : ℕ → List Bool
  | 0 => RecursiveChildQuotientsConstant.bits 1
  | i+1 => DimensionProductDescriptor.bits (B^i) B

theorem bits_value (B i : ℕ) : Counter.value (bits B i) = B^i := by
  cases i with
  | zero => exact RecursiveChildQuotientsConstant.bits_value 1
  | succ i => rw [bits,DimensionProductDescriptor.bits_value,pow_succ]

theorem bits_canonical (B i : ℕ) : GrowingCounterData.Canonical (bits B i) := by
  cases i with
  | zero => exact RecursiveChildQuotientsConstant.bits_canonical 1
  | succ i => exact DimensionProductDescriptor.bits_canonical _ _

theorem power_step (ws : List Bool) (B i : ℕ) (hB : 2 ≤ B)
    (hw : Counter.value ws = B) (cw : GrowingCounterData.Canonical ws) :
    HoareTime (program (q := q)) (fun v => v = input ws (bits B i))
      (fun v => v = input ws (bits B (i+1))) (110*B^(i+1)) := by
  simpa only [bits,pow_succ] using step_linear (q := q) ws (bits B i) (B^i) B
    (by omega) (pow_pos (by omega) _) hw (bits_value B i) cw (bits_canonical B i)

end
end IntegerMultBounds.Machine.FixedBasePowerStep
