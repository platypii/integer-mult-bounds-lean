import IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsShared
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared

/-! Paid construction of the three binary movement headers from only P/G/B/u.
A canonical zero is physically written before the shared dimension engine is
run with radix two and high width zero. All eighteen private tapes are erased
by the reverse cleanup; the arbitrary caller is preserved throughout. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthHeadersShared
noncomputable section
variable {a t n : ℕ}

structure Sources (caller : Tapes t a) (focus : Fin n → Fin t) (hs : Fin n → List Bool) : Prop where
  tape : ∀ i, caller.tape (focus i) = RadixZeroFill.encodedBinary (hs i)
  head : ∀ i, caller.head (focus i) = 1

def values (P G B u : ℕ) : Fin 4 → ℕ := ![P,G,B,u]
def dimensionWords (hs : Fin 4 → List Bool) : Fin 5 → List Bool := ![hs 0,hs 1,hs 2,hs 3,[]]
def dimensionFocus (focus : Fin 4 → Fin t) : Fin 5 → Fin (t+1) :=
  ![Fin.castAdd 1 (focus 0),Fin.castAdd 1 (focus 1),Fin.castAdd 1 (focus 2),
    Fin.castAdd 1 (focus 3),Fin.natAdd t 0]

def input (caller : Tapes t a) :=
  (caller.append ArbitraryWidthZeroHeaderShared.empty).append (FixedHeaderBankCopy.empty 17)
def output (caller : Tapes t a) (P G B u : ℕ) (hs : Fin 4 → List Bool) :=
  (caller.append ArbitraryWidthZeroHeaderShared.header).append
    (ArbitraryWidthHighDimensions.output 2 P G B u 0 (dimensionWords hs))

def program (focus : Fin 4 → Fin t) := seq
  (extend (ArbitraryWidthZeroHeaderShared.program (a := a) (t := t)) 17)
  (ArbitraryWidthHighDimensionsShared.program (dimensionFocus focus) 2)
def cleanup := seq (ArbitraryWidthHighDimensionsShared.cleanup (a := a) (t := t+1))
  (extend (ArbitraryWidthZeroHeaderShared.cleanup (a := a) (t := t)) 17)

/-- The full unpadded rectangular volume for either adjacent-width orientation. -/
def volume (P G B u : ℕ) := 2*P*(2^u)^2*G*B

theorem volume_eq (P G B u : ℕ) :
    volume P G B u = 2*ArbitraryWidthHighDimensions.dataVolume 2 P G B u := by
  have hp : 2^(2*u) = (2^u)^2 := by rw [Nat.mul_comm 2 u,pow_mul]
  simp only [volume,ArbitraryWidthHighDimensions.dataVolume,hp]
  ring

theorem volume_bounds (P G B u : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    0 < volume P G B u ∧ ArbitraryWidthHighDimensions.dataVolume 2 P G B u ≤ volume P G B u := by
  have hv : 0 < ArbitraryWidthHighDimensions.dataVolume 2 P G B u := by
    unfold ArbitraryWidthHighDimensions.dataVolume
    positivity
  rw [volume_eq]
  omega

theorem dimension_values (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (dimensionWords hs i) = ArbitraryWidthHighDimensions.originalValues P G B u 0 i := by
  intro i; fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact hv 3
  · rfl

theorem dimension_canonical (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (dimensionWords hs i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact hc 3
  · exact ArbitraryWidthZeroHeaderShared.zero_canonical

theorem dimension_sources (caller : Tapes t a) (focus : Fin 4 → Fin t)
    (hs : Fin 4 → List Bool) (hh : Sources caller focus hs) :
    Sources (caller.append ArbitraryWidthZeroHeaderShared.header) (dimensionFocus focus) (dimensionWords hs) := by
  constructor
  · intro i; fin_cases i <;>
      simp [dimensionFocus,dimensionWords,Tapes.append,hh.tape,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank,
        ArbitraryWidthZeroHeaderShared.encoded_zero]
  · intro i; fin_cases i <;>
      simp [dimensionFocus,Tapes.append,hh.head,
        ArbitraryWidthZeroHeaderShared.header,FiniteReturnStack.bank]

def constructCoefficient := ArbitraryWidthHighDimensions.linearConstant 2+58

theorem constructs (caller : Tapes t a) (focus : Fin 4 → Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hh : Sources caller focus hs) :
    HoareTime (program focus) (fun v => v = input caller)
      (fun v => v = output caller P G B u hs) (constructCoefficient*volume P G B u) := by
  have hz := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.constructs caller) (FixedHeaderBankCopy.empty 17)
  have hd := ArbitraryWidthHighDimensionsShared.constructs (dimensionFocus focus)
    (caller.append ArbitraryWidthZeroHeaderShared.header) 2 P G B u 0 (by omega) (by omega)
    hP hG hB (dimensionWords hs) (dimension_values P G B u hs hv) (dimension_canonical hs hc)
    (dimension_sources caller focus hs hh).tape (dimension_sources caller focus hs hh).head
  apply (hz.seq hd).consequence (fun _ h => h) (fun _ h => h)
  obtain ⟨hV,hD⟩ := volume_bounds P G B u hP hG hB
  have hm := Nat.mul_le_mul_left (ArbitraryWidthHighDimensions.linearConstant 2+51) hD
  unfold constructCoefficient
  nlinarith

theorem cleans (caller : Tapes t a) (focus : Fin 4 → Fin t)
    (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t)) (fun v => v = output caller P G B u hs)
      (fun v => v = input caller) (105*volume P G B u) := by
  have hd := ArbitraryWidthHighDimensionsShared.cleans (dimensionFocus focus)
    (caller.append ArbitraryWidthZeroHeaderShared.header) 2 P G B u 0 (by omega) (by omega)
    hP hG hB (dimensionWords hs) (dimension_values P G B u hs hv) (dimension_canonical hs hc)
  have hz := hoare_extend_eq (ArbitraryWidthZeroHeaderShared.cleans caller) (FixedHeaderBankCopy.empty 17)
  apply (hd.seq hz).consequence (fun _ h => h) (fun _ h => h)
  obtain ⟨hV,hD⟩ := volume_bounds P G B u hP hG hB
  omega

def movementFocus : Fin 3 → Fin ((t+1)+17) :=
  ![Fin.natAdd (t+1) 0,Fin.natAdd (t+1) 9,Fin.natAdd (t+1) 10]
def movementWords (P G B u : ℕ) (hs : Fin 4 → List Bool) : Fin 3 → List Bool :=
  ![hs 0,ArbitraryWidthHighDimensions.words 2 P G B u 0 4,
    ArbitraryWidthHighDimensions.words 2 P G B u 0 5]
def movementValues (P G B u : ℕ) : Fin 3 → ℕ := ![P,2^u*G,2^u*B]

theorem movement_sources (caller : Tapes t a) (P G B u : ℕ) (hs : Fin 4 → List Bool) :
    Sources (output caller P G B u hs) movementFocus (movementWords P G B u hs) := by
  constructor
  · intro i; fin_cases i <;>
      simp [movementFocus,movementWords,output,Tapes.append,
        ArbitraryWidthHighDimensions.output,ArbitraryWidthHighDimensions.state,
        ArbitraryWidthHighDimensions.bank,dimensionWords] <;> rfl
  · intro i; fin_cases i <;>
      simp [movementFocus,output,Tapes.append,
        ArbitraryWidthHighDimensions.output,ArbitraryWidthHighDimensions.state,
        ArbitraryWidthHighDimensions.bank] <;> rfl

theorem movement_values (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (movementWords P G B u hs i) = movementValues P G B u i := by
  intro i; fin_cases i
  · exact hv 0
  · have h := ArbitraryWidthHighDimensions.words_value 2 P G B u 0 4
    simpa [ArbitraryWidthHighDimensions.values,movementWords,movementValues,Nat.mul_comm] using h
  · have h := ArbitraryWidthHighDimensions.words_value 2 P G B u 0 5
    simpa [ArbitraryWidthHighDimensions.values,movementWords,movementValues,Nat.mul_comm] using h

theorem movement_canonical (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (movementWords P G B u hs i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact ArbitraryWidthHighDimensions.words_canonical 2 P G B u 0 4
  · exact ArbitraryWidthHighDimensions.words_canonical 2 P G B u 0 5

theorem caller_cells (caller : Tapes t a) (P G B u : ℕ) (hs : Fin 4 → List Bool) (i : Fin t) :
    (output caller P G B u hs).head (Fin.castAdd 17 (Fin.castAdd 1 i)) = caller.head i ∧
    (output caller P G B u hs).tape (Fin.castAdd 17 (Fin.castAdd 1 i)) = caller.tape i := by
  simp only [output,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthHeadersShared
