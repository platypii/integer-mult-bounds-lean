import IntegerMultBounds.Machine.TranslationDimensions
import IntegerMultBounds.Machine.FlatCoordinateSchedule

/-! Physically construct the canonical dimensions of a chosen coordinate from
one exponent and one trailing width. The finite machine depends only on target. -/
namespace IntegerMultBounds.Machine.FlatCoordinateDimensions
open Networks.Shared50ModularControl (prime)
open ActualAffineScaling (modulus)
open FlatCoordinateLayout
open FlatCoordinateSchedule (bits)
noncomputable section
variable {d : ℕ}

private theorem hprime : 2 ≤ prime := Networks.Shared50ModularControl.prime_prime.two_le

def program (t : Fin d) := TranslationDimensions.program hprime t.val (suffixFields t)

def input (b W : ℕ) : Tapes 9 prime := TranslationDimensions.input (bits b) (bits W)

def output (t : Fin d) (b W : ℕ) : Tapes 9 prime :=
  TranslationDimensions.output hprime t.val (suffixFields t) (bits b) (bits W) b W

theorem prefix_power (t : Fin d) (b : ℕ) :
    prime^(t.val*b) = prefixSize (Q := modulus b) t := by
  simp only [prefixSize,modulus,pow_mul,Nat.mul_comm]

theorem suffix_power (t : Fin d) (b W : ℕ) :
    prime^(suffixFields t*b)*W = suffixSize (Q := modulus b) (W := W) t := by
  simp only [suffixSize,modulus,pow_mul,Nat.mul_comm]

/-- All scans, conversions, product construction and joins fit common volume. -/
theorem construct_hoare (t : Fin d) (b W : ℕ) (hW : 0 < W) :
    HoareTime (program t) (fun v => v = input b W) (fun v => v = output t b W)
      ((24*t.val+24*suffixFields t+333)*((modulus b)^d*W)) := by
  have hh := TranslationDimensions.construct_hoare_volume hprime t.val (suffixFields t)
    (bits b) (bits W) b W (FlatCoordinateSchedule.bits_value _) (FlatCoordinateSchedule.bits_value _)
    hW (FlatCoordinateSchedule.bits_canonical _) (FlatCoordinateSchedule.bits_canonical _)
  have hv : prime^(t.val*b)*prime^b*(prime^(suffixFields t*b)*W) = (modulus b)^d*W := by
    rw [prefix_power,suffix_power]
    exact (mul_assoc _ _ _).trans (split_volume t).symm
  simpa only [hv,program,input,output] using hh

/-- These are literally the canonical words consumed by each primitive stage. -/
theorem output_descriptors (t : Fin d) (b W : ℕ) :
    (output t b W).tape TranslationDimensions.qSlot = RadixZeroFill.encodedBinary (bits (modulus b)) ∧
    (output t b W).tape TranslationDimensions.pSlot =
      RadixZeroFill.encodedBinary (bits (prefixSize (Q := modulus b) t)) ∧
    (output t b W).tape TranslationDimensions.bSlot =
      RadixZeroFill.encodedBinary (bits (suffixSize (Q := modulus b) (W := W) t)) := by
  have hq := (TranslationDimensions.output_q hprime t.val (suffixFields t) (bits b) (bits W) b W).2
  have hp := (TranslationDimensions.output_p hprime t.val (suffixFields t) (bits b) (bits W) b W).2
  have hb := (TranslationDimensions.output_b hprime t.val (suffixFields t) (bits b) (bits W) b W).2
  rw [TranslationDimensions.qBits_eq_advance] at hq
  rw [TranslationDimensions.pBits_eq_advance,prefix_power] at hp
  rw [TranslationDimensions.bBits_eq_advance,suffix_power] at hb
  exact ⟨hq,hp,hb⟩

theorem input_workspace_blank (b W : ℕ) (i : Fin 9)
    (hb : i ≠ TranslationDimensions.exponentSlot) (hw : i ≠ TranslationDimensions.widthSlot) :
    (input b W).head i = 0 ∧ (input b W).tape i = fun _ => blank :=
  TranslationDimensions.input_workspace_blank _ _ i hb hw

theorem output_heads (t : Fin d) (b W : ℕ) :
    (output t b W).head TranslationDimensions.qSlot = 1 ∧
    (output t b W).head TranslationDimensions.pSlot = 1 ∧
    (output t b W).head TranslationDimensions.bSlot = 1 := ⟨rfl,rfl,rfl⟩

theorem inputs_preserved (t : Fin d) (b W : ℕ) :
    (output t b W).head TranslationDimensions.exponentSlot = 1 ∧
    (output t b W).tape TranslationDimensions.exponentSlot = RadixZeroFill.encodedBinary (bits b) ∧
    (output t b W).head TranslationDimensions.widthSlot = 1 ∧
    (output t b W).tape TranslationDimensions.widthSlot = RadixZeroFill.encodedBinary (bits W) :=
  ⟨rfl,rfl,rfl,rfl⟩

end
end IntegerMultBounds.Machine.FlatCoordinateDimensions
