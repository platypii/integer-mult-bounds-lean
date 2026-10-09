import IntegerMultBounds.Machine.ArbitraryWidthHighInitializedRun
import IntegerMultBounds.Machine.ArbitraryWidthHighDimensionsAndSuffixShared
import IntegerMultBounds.Machine.ArbitraryWidthZeroHeaderShared
import IntegerMultBounds.Machine.ArbitraryWidthJoinedHeaders

/-! Concrete source-slot wiring from the physically constructed metadata
caller into the three private high-execution header-copy families. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighRuntimeHeaderWiring
noncomputable section
open Networks
open Shared50ModularControl (prime)
open ArbitraryWidthHighExecutionInitialize (Sources)
open ArbitraryWidthExecutionPrivateHeadersRoot (exchangeWords)
open ArbitraryWidthExecutionPrivateHeadersMovement (movementWords)
open ArbitraryWidthExecutionPrivateHeadersPadding (paddedWords)
variable {t : ℕ}

abbrev count (t : ℕ) := ((t+17)+12)+1

def bank (base : Tapes t prime) (P G B e r : ℕ)
    (dimensionHeaders : Fin 5 → List Bool) (joinedHeaders : Fin 6 → List Bool) : Tapes (count t) prime :=
  ((base.append (ArbitraryWidthHighDimensionsAndSuffixShared.output prime P G B e r dimensionHeaders)).append
    (ArbitraryWidthJoinedHeaders.output joinedHeaders e r)).append ArbitraryWidthZeroHeaderShared.header

def baseSlot (i : Fin t) : Fin (count t) := Fin.castAdd 1 (Fin.castAdd 12 (Fin.castAdd 17 i))
def dimensionSlot (i : Fin 17) : Fin (count t) := Fin.castAdd 1 (Fin.castAdd 12 (Fin.natAdd t i))
def joinedSlot (i : Fin 12) : Fin (count t) := Fin.castAdd 1 (Fin.natAdd (t+17) i)
def zeroSlot : Fin (count t) := Fin.natAdd ((t+17)+12) 0

def exchangeFocus (focus : Fin 7 → Fin t) : Fin 7 → Fin (count t) := fun i => baseSlot (focus i)

def movementFocus (focus : Fin 7 → Fin t) : Fin 5 → Fin (count t) :=
  ![dimensionSlot 9,dimensionSlot 8,dimensionSlot 10,zeroSlot,baseSlot (focus (Fin.natAdd 6 (0 : Fin 1)))]

def paddingFocus (rows rounded : Fin t) : Fin (4+6) → Fin (count t) :=
  Fin.addCases ![dimensionSlot 0,baseSlot rows,baseSlot rounded,dimensionSlot 12]
    (fun i => joinedSlot (Fin.natAdd 6 i))

def paddingWords (dimensionHeaders : Fin 5 → List Bool) (rows rounded : List Bool) (e r G B : ℕ) :
    Fin 4 → List Bool := ![dimensionHeaders 0,rows,rounded,ArbitraryWidthHighPaddingSuffix.bits prime e r G B]

theorem base_cells (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (i : Fin t) :
    (bank base P G B e r dh jh).head (baseSlot i) = base.head i ∧
    (bank base P G B e r dh jh).tape (baseSlot i) = base.tape i := by
  simp only [bank,baseSlot,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

theorem dimension_original (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (i : Fin 5) :
    (bank base P G B e r dh jh).head (dimensionSlot (Fin.castAdd 12 i)) = 1 ∧
    (bank base P G B e r dh jh).tape (dimensionSlot (Fin.castAdd 12 i)) =
      RadixZeroFill.encodedBinary (dh i) := by
  simp only [bank,dimensionSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  have h := ArbitraryWidthHighDimensionsAndSuffixShared.headers_cells (a := prime) prime P G B e r dh
    (Fin.castAdd 6 i)
  have hi : Fin.castAdd 6 (Fin.castAdd 6 i) = Fin.castAdd 12 i := Fin.ext rfl
  rw [hi] at h
  simpa only [ArbitraryWidthHighDimensionsAndSuffixShared.headerWords,Fin.addCases_left] using h

theorem dimension_generated (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (i : Fin 6) :
    (bank base P G B e r dh jh).head (dimensionSlot (Fin.castAdd 6 (Fin.natAdd 5 i))) = 1 ∧
    (bank base P G B e r dh jh).tape (dimensionSlot (Fin.castAdd 6 (Fin.natAdd 5 i))) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighDimensions.words prime P G B e r i) := by
  simp only [bank,dimensionSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  have h := ArbitraryWidthHighDimensionsAndSuffixShared.headers_cells (a := prime) prime P G B e r dh
    (Fin.natAdd 5 i)
  simpa only [ArbitraryWidthHighDimensionsAndSuffixShared.headerWords,Fin.addCases_right] using h

theorem suffix_cells (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) :
    (bank base P G B e r dh jh).head (dimensionSlot 12) = 1 ∧
    (bank base P G B e r dh jh).tape (dimensionSlot 12) =
      RadixZeroFill.encodedBinary (ArbitraryWidthHighPaddingSuffix.bits prime e r G B) := by
  simp only [bank,dimensionSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  exact ArbitraryWidthHighDimensionsAndSuffixShared.suffix_cells prime P G B e r dh

theorem joined_cells (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (i : Fin 6) :
    (bank base P G B e r dh jh).head (joinedSlot (Fin.natAdd 6 i)) = 1 ∧
    (bank base P G B e r dh jh).tape (joinedSlot (Fin.natAdd 6 i)) =
      RadixZeroFill.encodedBinary (ArbitraryWidthJoinedHeaders.words jh e r i) := by
  simp only [bank,joinedSlot,Tapes.append,Fin.addCases_left,Fin.addCases_right]
  exact ArbitraryWidthJoinedHeaders.target jh e r i

theorem zero_cells (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) :
    (bank base P G B e r dh jh).head zeroSlot = 1 ∧
    (bank base P G B e r dh jh).tape zeroSlot = RadixZeroFill.encodedBinary [] := by
  simp only [bank,zeroSlot,Tapes.append,Fin.addCases_right]
  exact ⟨rfl,ArbitraryWidthZeroHeaderShared.encoded_zero⟩

/-- The original seven exchange source words are retained on the base caller. -/
theorem exchange_sources (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool)
    (focus : Fin 7 → Fin t) (hs : Fin 6 → List Bool) (rs : List Bool)
    (he : Sources base focus (exchangeWords hs rs)) :
    Sources (bank base P G B e r dh jh) (exchangeFocus focus) (exchangeWords hs rs) := by
  constructor
  · intro i
    exact (base_cells base P G B e r dh jh (focus i)).2.trans (he.tape i)
  · intro i
    exact (base_cells base P G B e r dh jh (focus i)).1.trans (he.head i)

/-- Movement uses generated GL/PH/BL, the physically written zero clock,
and the base caller's retained rho. These are literal head/cell facts. -/
theorem movement_sources (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool)
    (focus : Fin 7 → Fin t) (hs : Fin 6 → List Bool) (rs : List Bool)
    (he : Sources base focus (exchangeWords hs rs)) :
    Sources (bank base P G B e r dh jh) (movementFocus focus)
      (movementWords (ArbitraryWidthHighDimensions.words prime P G B e r 4)
        (ArbitraryWidthHighDimensions.words prime P G B e r 3)
        (ArbitraryWidthHighDimensions.words prime P G B e r 5) rs) := by
  have rhoCells : (bank base P G B e r dh jh).head (baseSlot (focus (Fin.natAdd 6 (0 : Fin 1)))) = 1 ∧
      (bank base P G B e r dh jh).tape (baseSlot (focus (Fin.natAdd 6 (0 : Fin 1)))) = RadixZeroFill.encodedBinary rs := by
    have h := base_cells base P G B e r dh jh (focus (Fin.natAdd 6 (0 : Fin 1)))
    exact ⟨h.1.trans (he.head _),h.2.trans (by simpa only [exchangeWords,Fin.addCases_right] using he.tape (Fin.natAdd 6 (0 : Fin 1)))⟩
  constructor
  · intro i; fin_cases i
    · exact (dimension_generated base P G B e r dh jh 4).2
    · exact (dimension_generated base P G B e r dh jh 3).2
    · exact (dimension_generated base P G B e r dh jh 5).2
    · exact (zero_cells base P G B e r dh jh).2
    · exact rhoCells.2
  · intro i; fin_cases i
    · exact (dimension_generated base P G B e r dh jh 4).1
    · exact (dimension_generated base P G B e r dh jh 3).1
    · exact (dimension_generated base P G B e r dh jh 5).1
    · exact (zero_cells base P G B e r dh jh).1
    · exact rhoCells.1

/-- Padding reads P and the constructed row suffix from dimensions, row and
rounded-row originals from the base, and all six actual joined output headers. -/
theorem padding_sources (base : Tapes t prime) (P G B e r : ℕ)
    (dh : Fin 5 → List Bool) (jh : Fin 6 → List Bool) (rows rounded : Fin t) (rs rps : List Bool)
    (hrows : base.tape rows = RadixZeroFill.encodedBinary rs) (hrowhead : base.head rows = 1)
    (hrounded : base.tape rounded = RadixZeroFill.encodedBinary rps) (hroundedhead : base.head rounded = 1) :
    Sources (bank base P G B e r dh jh) (paddingFocus rows rounded)
      (paddedWords (paddingWords dh rs rps e r G B) (ArbitraryWidthJoinedHeaders.words jh e r)) := by
  have hrc := base_cells base P G B e r dh jh rows
  have hpc := base_cells base P G B e r dh jh rounded
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i
      · exact (dimension_original base P G B e r dh jh 0).2
      · exact hrc.2.trans hrows
      · exact hpc.2.trans hrounded
      · exact (suffix_cells base P G B e r dh jh).2
    | right i =>
      simpa only [paddingFocus,paddedWords,Fin.addCases_right] using (joined_cells base P G B e r dh jh i).2
  · intro i
    induction i using Fin.addCases with
    | left i =>
      fin_cases i
      · exact (dimension_original base P G B e r dh jh 0).1
      · exact hrc.1.trans hrowhead
      · exact hpc.1.trans hroundedhead
      · exact (suffix_cells base P G B e r dh jh).1
    | right i =>
      simpa only [paddingFocus,Fin.addCases_right] using (joined_cells base P G B e r dh jh i).1

/-- Literal movement words denote GL, PH, BL, zero-clock, and rho in the
order expected by the actual movement engine. -/
theorem movement_values (P G B e r : ℕ) (rs : List Bool) (hr : Counter.value rs = r) :
    ∀ i : Fin 5, Counter.value
      (movementWords (ArbitraryWidthHighDimensions.words prime P G B e r 4)
        (ArbitraryWidthHighDimensions.words prime P G B e r 3)
        (ArbitraryWidthHighDimensions.words prime P G B e r 5) rs i) =
      (![prime^(e-r)*G,P*prime^r,prime^(e-r)*B,0,r] : Fin 5 → ℕ) i := by
  intro i
  fin_cases i
  · change Counter.value (ArbitraryWidthHighDimensions.words prime P G B e r 4) = prime^(e-r)*G
    exact (ArbitraryWidthHighDimensions.words_value prime P G B e r 4).trans (Nat.mul_comm G _)
  · exact ArbitraryWidthHighDimensions.words_value prime P G B e r 3
  · change Counter.value (ArbitraryWidthHighDimensions.words prime P G B e r 5) = prime^(e-r)*B
    exact (ArbitraryWidthHighDimensions.words_value prime P G B e r 5).trans (Nat.mul_comm B _)
  · rfl
  · exact hr

theorem movement_canonical (P G B e r : ℕ) (rs : List Bool)
    (cr : GrowingCounterData.Canonical rs) :
    ∀ i : Fin 5, GrowingCounterData.Canonical
      (movementWords (ArbitraryWidthHighDimensions.words prime P G B e r 4)
        (ArbitraryWidthHighDimensions.words prime P G B e r 3)
        (ArbitraryWidthHighDimensions.words prime P G B e r 5) rs i) := by
  intro i
  fin_cases i
  · exact ArbitraryWidthHighDimensions.words_canonical prime P G B e r 4
  · exact ArbitraryWidthHighDimensions.words_canonical prime P G B e r 3
  · exact ArbitraryWidthHighDimensions.words_canonical prime P G B e r 5
  · exact ArbitraryWidthZeroHeaderShared.zero_canonical
  · exact cr

/-- Actual copied P, base row/rounded descriptors and generated suffix form
exactly the padding machine's four canonical shape headers. -/
theorem padding_headers (P G B e r R' : ℕ) (dh : Fin 5 → List Bool) (rs rps : List Bool)
    (hP : Counter.value (dh 0) = P) (hR : Counter.value rs = prime^(2*r))
    (hR' : Counter.value rps = R') (cP : GrowingCounterData.Canonical (dh 0))
    (cR : GrowingCounterData.Canonical rs) (cR' : GrowingCounterData.Canonical rps) :
    ArbitraryWidthPaddedPiecePadding.Headers
      (ArbitraryWidthHighLayout.joinedDescriptor prime P e r G B) R'
      (paddingWords dh rs rps e r G B) := by
  constructor
  · intro i
    fin_cases i
    · exact hP
    · exact hR
    · exact hR'
    · change Counter.value (ArbitraryWidthHighPaddingSuffix.bits prime e r G B) =
        RecursiveInterchangeRows.rowLength prime (ArbitraryWidthHighLayout.joinedDescriptor prime P e r G B)
      rw [ArbitraryWidthHighPaddingSuffix.bits_value,ArbitraryWidthHighPaddingSuffix.joined_rowLength]
  · intro i
    fin_cases i
    · exact cP
    · exact cR
    · exact cR'
    · exact ArbitraryWidthHighPaddingSuffix.bits_canonical prime e r G B

/-- The six actual joined-header outputs are precisely the padded low-root
shape, with only its row count replaced by the retained rounded value. -/
theorem lowroot_headers (P G B e r R' : ℕ) (jh : Fin 6 → List Bool)
    (hv : ∀ i, Counter.value (jh i) = ArbitraryWidthJoinedHeaders.originalValues P G B e r R' i)
    (hc : ∀ i, GrowingCounterData.Canonical (jh i)) :
    RecursiveDimensionBank.Headers
      (RecursiveRowPadding.withRows (ArbitraryWidthHighLayout.joinedDescriptor prime P e r G B) R')
      (ArbitraryWidthJoinedHeaders.words jh e r) :=
  ArbitraryWidthJoinedHeaders.headers jh P G B e r R' hv hc

end
end IntegerMultBounds.Machine.ArbitraryWidthHighRuntimeHeaderWiring
