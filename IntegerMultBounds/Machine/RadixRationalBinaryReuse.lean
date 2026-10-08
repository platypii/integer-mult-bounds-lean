import IntegerMultBounds.Machine.RadixRationalBinary
import IntegerMultBounds.Machine.BinaryDescriptorReset

/-! Recurring fixed-rational conversion. The previous binary output is erased
by actual transitions before the next computation, and all radix workspace is
again completely blank afterward. Alphabet lifting touches only binary output. -/
namespace IntegerMultBounds.Machine.RadixRationalBinaryReuse

open RadixDigits
variable {q : ℕ}

def input (old : List Bool) (xs : List (Fin q)) : Tapes 4 q :=
  RadixRationalBinary.bank ((RadixToBinary.binaryState q old).tape 0) 1 xs []

private def frame (xs : List (Fin q)) : Tapes 3 q :=
  ⟨![0,0,1],![fun _ => blank,fun _ => blank,RadixRationalBinary.source xs]⟩

/-- Decode/encode only the selected binary tape; radix source is an exact frame. -/
def resetProgram : Program 4 4 q :=
  extend (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryDescriptorReset.program) 3

private theorem reset_binary (old : List Bool) :
    HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryDescriptorReset.program)
      (fun v => v = RadixToBinary.binaryState q old)
      (fun v => v = MarkedWordCleanup.one (fun _ => blank) 0) (2*old.length+4) := by
  have hh := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) (BinaryDescriptorReset.reset_hoare old)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

private theorem input_frame (old : List Bool) (xs : List (Fin q)) :
    (RadixToBinary.binaryState q old).append (frame xs) = input old xs := by
  unfold Tapes.append frame input RadixRationalBinary.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem blank_frame (xs : List (Fin q)) :
    (MarkedWordCleanup.one (fun _ => (blank : Fin (q+4))) 0).append (frame xs) = RadixRationalBinary.input xs := by
  unfold Tapes.append frame MarkedWordCleanup.one RadixRationalBinary.input RadixRationalBinary.bank
  congr 1 <;> funext i <;> fin_cases i <;> rfl

theorem reset_hoare (old : List Bool) (xs : List (Fin q)) :
    HoareTime resetProgram (fun v => v = input old xs) (fun v => v = RadixRationalBinary.input xs)
      (2*old.length+4) := by
  have hh := (reset_binary old).extend (frame xs)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,by simpa only [input_frame] using hv⟩
  · rintro v ⟨w,rfl,hv⟩; simpa only [blank_frame] using hv

variable [Fact q.Prime]

def program (r : ℚ) : Program 4 (4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6)) q :=
  seq resetProgram (RadixRationalBinary.program r)

/-- Complete recurring computation; no stale binary suffix or radix scratch remains. -/
theorem compute_hoare (r : ℚ) (old : List Bool) (xs : List (Fin q)) :
    HoareTime (program r) (fun v => v = input old xs) (fun v => v = RadixRationalBinary.output r xs)
      (2*old.length+10*value (RadixRationalBinary.result r xs)+10*xs.length+32) := by
  exact ((reset_hoare old xs).seq (RadixRationalBinary.compute_hoare r xs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- A bounded prior offset makes the actual output-erasure charge volume-linear. -/
theorem compute_hoare_fiber (r : ℚ) (old : List Bool) (xs : List (Fin q)) (B : ℕ) (hB : 0 < B)
    (cold : GrowingCounterData.Canonical old) (hold : Counter.value old < q^xs.length) :
    HoareTime (program r) (fun v => v = input old xs) (fun v => v = RadixRationalBinary.output r xs)
      (54*(q^xs.length*B)) := by
  apply (compute_hoare r old xs).consequence (fun _ h => h) (fun _ h => h) _
  have hv := value_lt (Fact.out : q.Prime).two_le (RadixRationalBinary.result r xs)
  have hw := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le xs.length
  have hlen : (RadixRationalBinary.result r xs).length = xs.length := RadixRationalData.digits_length _ _
  rw [hlen] at hv
  have hc := GrowingCounterData.canonical_width old cold
  have hl := Nat.log2_le_self (Counter.value old)
  have hp : 1 ≤ q^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  have hm : q^xs.length ≤ q^xs.length*B := by nlinarith
  omega

end IntegerMultBounds.Machine.RadixRationalBinaryReuse
