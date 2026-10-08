import IntegerMultBounds.Machine.RadixRationalBinaryReuse
import IntegerMultBounds.Machine.BinaryReplace

/-! Concrete recurring preparation of one fixed-rational translation offset.
Compute from the physical marked radix input, convert to canonical binary,
erase old output/scratch, and install the result on a separate offset tape.
Only the two binary tapes are alphabet-lifted during installation; radix cells
remain exact spectator frames. -/
namespace IntegerMultBounds.Machine.RationalOffsetPrepare

open RadixDigits
variable {q : ℕ}

def descriptor (bits : List Bool) : Tapes 1 q := RadixToBinary.binaryState q bits

/-- Converter output/work/radix scratch/prefix control, then translation offset. -/
def bank (supplied offset : List Bool) (xs : List (Fin q)) : Tapes 5 q :=
  (RadixRationalBinaryReuse.input supplied xs).append (descriptor offset)

private def replacementPlacement : Fin (2+3) ≃ Fin 5 := (Equiv.swap 0 4).trans (Equiv.swap 1 0)

/-- Lift the two active binary tapes only, before placing them in radix workspace. -/
def replacementProgram : Program 5 7 q :=
  Placement.placed (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryReplace.program) replacementPlacement

private theorem binary_replace (old next : List Bool) :
    HoareTime (Alphabet.program (RadixToBinary.binaryEncoding (q := q)) BinaryReplace.program)
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (BinaryReplace.bank old next))
      (fun v => v = Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (BinaryReplace.bank next next))
      (2*old.length+2*next.length+8) := by
  have hh := Alphabet.map_hoare (RadixToBinary.binaryEncoding (q := q)) (BinaryReplace.replace_hoare old next)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

private theorem active_bank (old next : List Bool) (xs : List (Fin q)) :
    Placement.active replacementPlacement (bank next old xs) =
      Alphabet.mapTapes (RadixToBinary.binaryEncoding (q := q)) (BinaryReplace.bank old next) := by
  unfold Placement.active replacementPlacement bank descriptor RadixRationalBinaryReuse.input
    RadixRationalBinary.bank BinaryReplace.bank CountedLoopReuse.controls Alphabet.mapTapes Tapes.append
  congr 1 <;> funext i <;> fin_cases i <;> rfl

private theorem extra_bank (old next : List Bool) (xs : List (Fin q)) :
    Placement.extra replacementPlacement (bank next old xs) = Placement.extra replacementPlacement (bank next next xs) := by
  unfold Placement.extra replacementPlacement bank descriptor RadixRationalBinaryReuse.input
    RadixRationalBinary.bank Tapes.append
  congr 1
  funext i
  fin_cases i <;> rfl

/-- Physical descriptor installation, retaining the computed source and radix control. -/
theorem replacement_hoare (old next : List Bool) (xs : List (Fin q)) :
    HoareTime replacementProgram (fun v => v = bank next old xs) (fun v => v = bank next next xs)
      (2*old.length+2*next.length+8) := by
  have hh := Placement.hoare_at (binary_replace old next) replacementPlacement (bank next old xs)
    (active_bank old next xs)
  apply hh.consequence (fun _ h => h) _ le_rfl
  rintro v ⟨w,rfl,rfl⟩
  rw [Placement.replace,extra_bank,← active_bank next next xs]
  exact Placement.view _ _

variable [Fact q.Prime]

def result (r : ℚ) (xs : List (Fin q)) : List Bool :=
  RadixToBinaryData.output (RadixRationalBinary.result r xs)

private theorem compute_at (r : ℚ) (supplied old : List Bool) (xs : List (Fin q)) :
    HoareTime (extend (RadixRationalBinaryReuse.program r) 1)
      (fun v => v = bank supplied old xs) (fun v => v = bank (result r xs) old xs)
      (2*supplied.length+10*value (RadixRationalBinary.result r xs)+10*xs.length+32) := by
  have hh := (RadixRationalBinaryReuse.compute_hoare r supplied xs).extend (descriptor old)
  apply hh.consequence _ _ le_rfl
  · intro v hv; exact ⟨_,rfl,hv⟩
  · rintro v ⟨w,rfl,hv⟩; exact hv

/-- A fixed scalar offset-preparation machine with five physical tapes. -/
def program (r : ℚ) : Program 5 ((4+((2+(2*r.num.natAbs+r.den+1)+2)+18+6))+7) q :=
  seq (extend (RadixRationalBinaryReuse.program r) 1) replacementProgram

/-- Exact recurring bank: no radix scratch survives and both binary outputs agree. -/
theorem prepare_hoare (r : ℚ) (supplied old : List Bool) (xs : List (Fin q)) :
    HoareTime (program r) (fun v => v = bank supplied old xs)
      (fun v => v = bank (result r xs) (result r xs) xs)
      (2*supplied.length+2*old.length+2*(result r xs).length+
        10*value (RadixRationalBinary.result r xs)+10*xs.length+41) := by
  exact ((compute_at r supplied old xs).seq (replacement_hoare old (result r xs) xs)).consequence
    (fun _ h => h) (fun _ h => h) (by omega)

/-- Modular correctness of the physically installed canonical binary offset. -/
theorem result_value (r : ℚ) (hden : r.den < q) (xs : List (Fin q)) :
    (Counter.value (result r xs) : ZMod (q^xs.length)) =
      Swap.Modular.ratMod (q^xs.length) r * (value xs : ZMod (q^xs.length)) :=
  RadixRationalBinary.output_value r hden xs

theorem result_canonical (r : ℚ) (xs : List (Fin q)) : GrowingCounterData.Canonical (result r xs) :=
  RadixRationalBinary.output_canonical r xs

theorem result_lt (r : ℚ) (xs : List (Fin q)) : Counter.value (result r xs) < q^xs.length := by
  rw [result,RadixToBinaryData.output_value]
  have hh := value_lt (Fact.out : q.Prime).two_le (RadixRationalBinary.result r xs)
  simpa only [RadixRationalBinary.result,RadixRationalData.digits_length] using hh

/-- For canonical old descriptors below the radix modulus, preparation's complete
arithmetic/conversion/replacement cost is absorbed by the physical fiber volume. -/
theorem prepare_hoare_fiber (r : ℚ) (supplied old : List Bool) (xs : List (Fin q)) (B : ℕ) (hB : 0 < B)
    (cs : GrowingCounterData.Canonical supplied) (co : GrowingCounterData.Canonical old)
    (hs : Counter.value supplied < q^xs.length) (ho : Counter.value old < q^xs.length) :
    HoareTime (program r) (fun v => v = bank supplied old xs)
      (fun v => v = bank (result r xs) (result r xs) xs) (67*(q^xs.length*B)) := by
  apply (prepare_hoare r supplied old xs).consequence (fun _ h => h) (fun _ h => h) _
  have hswidth := GrowingCounterData.canonical_width supplied cs
  have hslog := Nat.log2_le_self (Counter.value supplied)
  have howidth := GrowingCounterData.canonical_width old co
  have holog := Nat.log2_le_self (Counter.value old)
  have hrwidth := GrowingCounterData.canonical_width (result r xs) (result_canonical r xs)
  have hrlog := Nat.log2_le_self (Counter.value (result r xs))
  have hr := result_lt r xs
  have hv : Counter.value (result r xs) = value (RadixRationalBinary.result r xs) := RadixToBinaryData.output_value _
  have hw := RadixToBinaryData.width_le_power (Fact.out : q.Prime).two_le xs.length
  have hp : 1 ≤ q^xs.length := Nat.one_le_pow _ _ (by have := (Fact.out : q.Prime).two_le; omega)
  have hm : q^xs.length ≤ q^xs.length*B := by nlinarith
  omega

end IntegerMultBounds.Machine.RationalOffsetPrepare
