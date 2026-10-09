import IntegerMultBounds.Machine.BinaryAdjacentWidthHeadersShared
import IntegerMultBounds.Machine.BinaryRadixRootHeadersShared

/-! Physically synthesize the doubled spectator prefix needed by the binary
adjacent-width equal call. One is written, the dimension engine runs at fixed
radix/width two/one, and every created tape is erased by the reverse machine. -/
namespace IntegerMultBounds.Machine.BinaryAdjacentWidthPrefixShared
noncomputable section
variable {a t : ℕ}
open BinaryAdjacentWidthHeadersShared (Sources values volume)

def dimensionWords (hs : Fin 4 → List Bool) : Fin 5 → List Bool :=
  ![hs 0,hs 1,hs 2,BinaryRadixRootHeadersShared.oneBits,BinaryRadixRootHeadersShared.oneBits]
def dimensionFocus (focus : Fin 4 → Fin t) : Fin 5 → Fin (t+1) :=
  ![Fin.castAdd 1 (focus 0),Fin.castAdd 1 (focus 1),Fin.castAdd 1 (focus 2),Fin.natAdd t 0,Fin.natAdd t 0]
def input (caller : Tapes t a) :=
  (caller.append (FixedHeaderBankCopy.empty 1)).append (FixedHeaderBankCopy.empty 17)
def output (caller : Tapes t a) (P G B : ℕ) (hs : Fin 4 → List Bool) :=
  (caller.append BinaryRadixRootHeadersShared.oneBank).append
    (ArbitraryWidthHighDimensions.output 2 P G B 1 1 (dimensionWords hs))
def program (focus : Fin 4 → Fin t) := seq
  (extend (BinaryRadixRootHeadersShared.oneWriter (a := a) (t := t)) 17)
  (ArbitraryWidthHighDimensionsShared.program (dimensionFocus focus) 2)
def cleanup := seq (ArbitraryWidthHighDimensionsShared.cleanup (a := a) (t := t+1))
  (extend (BinaryRadixRootHeadersShared.oneCleanup (a := a) (t := t)) 17)

def bits (P G B : ℕ) := ArbitraryWidthHighDimensions.words 2 P G B 1 1 3

theorem bits_value (P G B : ℕ) : Counter.value (bits P G B) = P*2 :=
  ArbitraryWidthHighDimensions.words_value 2 P G B 1 1 3

theorem bits_canonical (P G B : ℕ) : GrowingCounterData.Canonical (bits P G B) :=
  ArbitraryWidthHighDimensions.words_canonical 2 P G B 1 1 3

theorem volume_positive (P G B u : ℕ) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B) :
    0 < volume P G B u := by
  unfold volume
  exact Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (Nat.mul_pos (by decide) hP)
    (pow_pos (Nat.two_pow_pos u) 2)) hG) hB

theorem data_volume_bound (P G B u : ℕ) :
    ArbitraryWidthHighDimensions.dataVolume 2 P G B 1 ≤ 2*volume P G B u := by
  have hp : 1 ≤ (2^u)^2 := Nat.one_le_pow _ _ (Nat.two_pow_pos u)
  have h := Nat.mul_le_mul_left (4*P*G*B) hp
  unfold ArbitraryWidthHighDimensions.dataVolume volume
  norm_num only [Nat.mul_one,Nat.reducePow,Nat.reduceMul] at *
  nlinarith only [h]

private theorem dimension_values (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (dimensionWords hs i) = ArbitraryWidthHighDimensions.originalValues P G B 1 1 i := by
  intro i; fin_cases i
  · exact hv 0
  · exact hv 1
  · exact hv 2
  · exact RecursiveChildQuotientsConstant.bits_value 1
  · exact RecursiveChildQuotientsConstant.bits_value 1

private theorem dimension_canonical (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (dimensionWords hs i) := by
  intro i; fin_cases i
  · exact hc 0
  · exact hc 1
  · exact hc 2
  · exact RecursiveChildQuotientsConstant.bits_canonical 1
  · exact RecursiveChildQuotientsConstant.bits_canonical 1

private theorem dimension_sources (caller : Tapes t a) (focus : Fin 4 → Fin t)
    (hs : Fin 4 → List Bool) (hsources : Sources caller focus hs) :
    Sources (caller.append BinaryRadixRootHeadersShared.oneBank) (dimensionFocus focus) (dimensionWords hs) := by
  constructor
  · intro i; fin_cases i
    · simpa [dimensionFocus,dimensionWords,Tapes.append] using hsources.tape 0
    · simpa [dimensionFocus,dimensionWords,Tapes.append] using hsources.tape 1
    · simpa [dimensionFocus,dimensionWords,Tapes.append] using hsources.tape 2
    · simp [dimensionFocus, dimensionWords, Tapes.append, BinaryRadixRootHeadersShared.oneBank, FixedHeaderBankCopy.headerBank, FixedHeaderBankCopy.bank, RecursiveDimensionBank.head, RecursiveDimensionBank.tape]
    · simp [dimensionFocus, dimensionWords, Tapes.append, BinaryRadixRootHeadersShared.oneBank, FixedHeaderBankCopy.headerBank, FixedHeaderBankCopy.bank, RecursiveDimensionBank.head, RecursiveDimensionBank.tape]
  · intro i; fin_cases i
    · simpa [dimensionFocus,Tapes.append] using hsources.head 0
    · simpa [dimensionFocus,Tapes.append] using hsources.head 1
    · simpa [dimensionFocus,Tapes.append] using hsources.head 2
    · simp [dimensionFocus, Tapes.append, BinaryRadixRootHeadersShared.oneBank, FixedHeaderBankCopy.headerBank, FixedHeaderBankCopy.bank, RecursiveDimensionBank.head, RecursiveDimensionBank.tape]
    · simp [dimensionFocus, Tapes.append, BinaryRadixRootHeadersShared.oneBank, FixedHeaderBankCopy.headerBank, FixedHeaderBankCopy.bank, RecursiveDimensionBank.head, RecursiveDimensionBank.tape]

def coefficient := 2*(ArbitraryWidthHighDimensions.linearConstant 2+51)+10

theorem constructs (caller : Tapes t a) (focus : Fin 4 → Fin t) (P G B u : ℕ)
    (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) (hsources : Sources caller focus hs) :
    HoareTime (program focus) (fun z => z = input caller)
      (fun z => z = output caller P G B hs) (coefficient*volume P G B u) := by
  have h1 := hoare_extend_eq (BinaryRadixRootHeadersShared.writes_one caller) (FixedHeaderBankCopy.empty 17)
  have hsrc := dimension_sources caller focus hs hsources
  have h2 := ArbitraryWidthHighDimensionsShared.constructs (dimensionFocus focus)
    (caller.append BinaryRadixRootHeadersShared.oneBank) 2 P G B 1 1 (by decide) le_rfl
    hP hG hB (dimensionWords hs) (dimension_values P G B u hs hv) (dimension_canonical hs hc) hsrc.tape hsrc.head
  have hvol := volume_positive P G B u hP hG hB
  have hbound := data_volume_bound P G B u
  apply (h1.seq h2).consequence (fun _ h => h) (fun _ h => h)
  unfold coefficient
  nlinarith

theorem cleans (caller : Tapes t a) (focus : Fin 4 → Fin t) (P G B u : ℕ)
    (hs : Fin 4 → List Bool) (hP : 0 < P) (hG : 0 < G) (hB : 0 < B)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    HoareTime (cleanup (a := a) (t := t)) (fun z => z = output caller P G B hs)
      (fun z => z = input caller) (210*volume P G B u) := by
  have h1 := ArbitraryWidthHighDimensionsShared.cleans (dimensionFocus focus)
    (caller.append BinaryRadixRootHeadersShared.oneBank) 2 P G B 1 1 (by decide) le_rfl
    hP hG hB (dimensionWords hs) (dimension_values P G B u hs hv) (dimension_canonical hs hc)
  have h2 := FixedHeaderBankCopy.cleans_linear (a := a) (by omega : 0 < t+1) caller
    (fun _ : Fin 1 => BinaryRadixRootHeadersShared.oneBits) 1 (by decide)
    (fun _ => RecursiveChildQuotientsConstant.bits_canonical 1)
    (fun _ => (RecursiveChildQuotientsConstant.bits_value 1).le)
  have h2' := hoare_extend_eq h2 (FixedHeaderBankCopy.empty 17)
  have hvol := volume_positive P G B u hP hG hB
  have hbound := data_volume_bound P G B u
  exact (h1.seq h2').consequence (fun _ h => h) (fun _ h => h) (by nlinarith)

def prefixSlot : Fin ((t+1)+17) := Fin.natAdd (t+1) 8

theorem prefix_cells (caller : Tapes t a) (P G B : ℕ) (hs : Fin 4 → List Bool) :
    (output caller P G B hs).head (prefixSlot (t := t)) = 1 ∧
    (output caller P G B hs).tape (prefixSlot (t := t)) = RadixZeroFill.encodedBinary (bits P G B) := by
  simp only [output,prefixSlot,Tapes.append,Fin.addCases_right]
  exact ⟨rfl,rfl⟩

def equalFocus (focus : Fin 4 → Fin t) : Fin 4 → Fin ((t+1)+17) :=
  ![prefixSlot,Fin.castAdd 17 (Fin.castAdd 1 (focus 1)),
    Fin.castAdd 17 (Fin.castAdd 1 (focus 2)),Fin.castAdd 17 (Fin.castAdd 1 (focus 3))]
def equalWords (P G B : ℕ) (hs : Fin 4 → List Bool) : Fin 4 → List Bool := ![bits P G B,hs 1,hs 2,hs 3]

theorem equal_values (P G B u : ℕ) (hs : Fin 4 → List Bool)
    (hv : ∀ i, Counter.value (hs i) = values P G B u i) :
    ∀ i, Counter.value (equalWords P G B hs i) = values (P*2) G B u i := by
  intro i; fin_cases i
  · exact bits_value P G B
  · exact hv 1
  · exact hv 2
  · exact hv 3

theorem equal_canonical (P G B : ℕ) (hs : Fin 4 → List Bool)
    (hc : ∀ i, GrowingCounterData.Canonical (hs i)) :
    ∀ i, GrowingCounterData.Canonical (equalWords P G B hs i) := by
  intro i; fin_cases i
  · exact bits_canonical P G B
  · exact hc 1
  · exact hc 2
  · exact hc 3

theorem equal_sources (caller : Tapes t a) (focus : Fin 4 → Fin t) (P G B : ℕ)
    (hs : Fin 4 → List Bool) (hsources : Sources caller focus hs) :
    Sources (output caller P G B hs) (equalFocus focus) (equalWords P G B hs) := by
  constructor
  · intro i; fin_cases i
    · exact (prefix_cells caller P G B hs).2
    · simpa [output,equalFocus,equalWords,Tapes.append] using hsources.tape 1
    · simpa [output,equalFocus,equalWords,Tapes.append] using hsources.tape 2
    · simpa [output,equalFocus,equalWords,Tapes.append] using hsources.tape 3
  · intro i; fin_cases i
    · exact (prefix_cells caller P G B hs).1
    · simpa [output,equalFocus,Tapes.append] using hsources.head 1
    · simpa [output,equalFocus,Tapes.append] using hsources.head 2
    · simpa [output,equalFocus,Tapes.append] using hsources.head 3

end
end IntegerMultBounds.Machine.BinaryAdjacentWidthPrefixShared
