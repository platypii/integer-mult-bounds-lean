import IntegerMultBounds.Machine.ArbitraryWidthHighCommonPrepare
import IntegerMultBounds.Machine.ArbitraryWidthHighRuntimeHeaderWiring

/-! Concrete high-branch sources from the common physical folding and
high-row metadata output, starting with only the original six shape words. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonHeaderWiring
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor)
open ArbitraryWidthHighExecutionInitialize (Sources)
open ArbitraryWidthHighCommonPrepare (originalSlot foldedSlot metadataSlot)
variable {t : ℕ}

abbrev count (t : ℕ) := (t+16)+19

def foldedPrefix (d : Descriptor) := d.beforeRows*d.rows*d.beforeH

def rhoWord (d : Descriptor) := ArbitraryWidthHighPrepare.words prime d.width 2
def rowWord (d : Descriptor) := ArbitraryWidthHighPrepare.words prime d.width 3
def roundedWord (d : Descriptor) := ArbitraryWidthHighPrepare.words prime d.width 4

def exchangeFocus : Fin (6+1) → Fin (count t) :=
  Fin.addCases foldedSlot (fun _ => metadataSlot 2)
def dimensionsFocus : Fin 5 → Fin (count t) :=
  ![foldedSlot 0,originalSlot 4,originalSlot 5,originalSlot 3,metadataSlot 2]
def joinedFocus : Fin (5+1) → Fin (count t) :=
  Fin.addCases dimensionsFocus (fun _ => metadataSlot 4)
def rowFocus : Fin (count t) := metadataSlot 3
def roundedFocus : Fin (count t) := metadataSlot 4

def dimensionsWords (d : Descriptor) (hs : Fin 6 → List Bool) : Fin 5 → List Bool :=
  ![ArbitraryWidthHighFoldHeaders.words d hs 0,hs 4,hs 5,hs 3,rhoWord d]
def joinedWords (d : Descriptor) (hs : Fin 6 → List Bool) : Fin (5+1) → List Bool :=
  Fin.addCases (dimensionsWords d hs) (fun _ => roundedWord d)

theorem foldedPrefix_positive (d : Descriptor) (hp : d.Positive) : 0 < foldedPrefix d :=
  Nat.mul_pos (Nat.mul_pos hp.1 hp.2.1) hp.2.2.1

/-- The six folded shape words have the exact scalar layout required by
the high body, including the physically multiplied spectator prefix. -/
theorem folded_headers (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) :
    RecursiveDimensionBank.Headers
      (ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD)
      (ArbitraryWidthHighFoldHeaders.words d hs) :=
  ArbitraryWidthHighFoldHeaders.headers d hs hv

/-- All seven exchange sources are read from actual common-preparation
outputs; no exchange-source contract is assumed. -/
theorem exchange_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (ArbitraryWidthHighCommonPrepare.output caller d hs prime) exchangeFocus
      (ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords
        (ArbitraryWidthHighFoldHeaders.words d hs) (rhoWord d)) := by
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simpa only [exchangeFocus,ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords,Fin.addCases_left] using
        (ArbitraryWidthHighCommonPrepare.folded_view caller d hs prime i).2
    | right i =>
      simpa only [exchangeFocus,ArbitraryWidthExecutionPrivateHeadersRoot.exchangeWords,Fin.addCases_right,rhoWord] using
        (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2).2
  · intro i
    induction i using Fin.addCases with
    | left i =>
      simpa only [exchangeFocus,Fin.addCases_left] using
        (ArbitraryWidthHighCommonPrepare.folded_view caller d hs prime i).1
    | right i =>
      simpa only [exchangeFocus,Fin.addCases_right] using
        (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2).1

/-- Dimension construction copies P/G/B/e/rho from their literal retained
common-preparation tapes, each restored to head one. -/
theorem dimensions_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (ArbitraryWidthHighCommonPrepare.output caller d hs prime) dimensionsFocus (dimensionsWords d hs) := by
  constructor
  · intro i; fin_cases i
    · exact (ArbitraryWidthHighCommonPrepare.folded_view caller d hs prime 0).2
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 4).2
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 5).2
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 3).2
    · exact (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2).2
  · intro i; fin_cases i
    · exact (ArbitraryWidthHighCommonPrepare.folded_view caller d hs prime 0).1
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 4).1
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 5).1
    · exact (ArbitraryWidthHighCommonPrepare.original_view caller d hs prime 3).1
    · exact (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 2).1

/-- Joined-header construction reads those same five originals and the
actual rounded row descriptor, never a preinitialized low-root bank. -/
theorem joined_sources (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    Sources (ArbitraryWidthHighCommonPrepare.output caller d hs prime) joinedFocus (joinedWords d hs) := by
  have hd := dimensions_sources caller d hs
  constructor
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [joinedFocus,joinedWords,Fin.addCases_left] using hd.tape i
    | right i =>
      simpa only [joinedFocus,joinedWords,Fin.addCases_right,roundedWord] using
        (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 4).2
  · intro i
    induction i using Fin.addCases with
    | left i => simpa only [joinedFocus,Fin.addCases_left] using hd.head i
    | right i =>
      simpa only [joinedFocus,Fin.addCases_right] using
        (ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 4).1

/-- The padding row and rounded-row sources are actual retained outputs
of the common high-row constructor. -/
theorem row_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head rowFocus = 1 ∧
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape rowFocus = RadixZeroFill.encodedBinary (rowWord d) :=
  ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 3

theorem rounded_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head roundedFocus = 1 ∧
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape roundedFocus = RadixZeroFill.encodedBinary (roundedWord d) :=
  ArbitraryWidthHighCommonPrepare.metadata_view caller d hs prime 4

theorem rho_value (d : Descriptor) : Counter.value (rhoWord d) = ArbitraryWidthHighPrepare.highDepth prime d.width :=
  ArbitraryWidthHighPrepare.words_value prime d.width 2

theorem row_value (d : Descriptor) :
    Counter.value (rowWord d) = prime^(2*ArbitraryWidthHighPrepare.highDepth prime d.width) := by
  rw [ArbitraryWidthHighRows.square_power]
  exact ArbitraryWidthHighPrepare.words_value prime d.width 3

theorem rounded_value (d : Descriptor) :
    Counter.value (roundedWord d) = ArbitraryWidthHighPrepare.rounded prime d.width :=
  ArbitraryWidthHighPrepare.words_value prime d.width 4

theorem rho_canonical (d : Descriptor) : GrowingCounterData.Canonical (rhoWord d) :=
  ArbitraryWidthHighPrepare.words_canonical prime d.width 2

theorem row_canonical (d : Descriptor) : GrowingCounterData.Canonical (rowWord d) :=
  ArbitraryWidthHighPrepare.words_canonical prime d.width 3

theorem rounded_canonical (d : Descriptor) : GrowingCounterData.Canonical (roundedWord d) :=
  ArbitraryWidthHighPrepare.words_canonical prime d.width 4

/-- Both branch metadata source families have canonical words and exact
numeric values derived solely from the original six-header specification. -/
theorem dimensions_values (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 5) :
    Counter.value (dimensionsWords d hs i) = ArbitraryWidthHighDimensions.originalValues
      (foldedPrefix d) d.between d.afterD d.width (ArbitraryWidthHighPrepare.highDepth prime d.width) i := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_value d.beforeRows d.rows d.beforeH
  · exact hv.1 4
  · exact hv.1 5
  · exact hv.1 3
  · exact rho_value d

theorem dimensions_canonical (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 5) :
    GrowingCounterData.Canonical (dimensionsWords d hs i) := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_canonical d.beforeRows d.rows d.beforeH
  · exact hv.2 4
  · exact hv.2 5
  · exact hv.2 3
  · exact rho_canonical d

theorem joined_values (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 6) :
    Counter.value (joinedWords d hs i) = ArbitraryWidthJoinedHeaders.originalValues
      (foldedPrefix d) d.between d.afterD d.width (ArbitraryWidthHighPrepare.highDepth prime d.width)
      (ArbitraryWidthHighPrepare.rounded prime d.width) i := by
  fin_cases i
  · exact ArbitraryWidthHighPrefix.bits_value d.beforeRows d.rows d.beforeH
  · exact hv.1 4
  · exact hv.1 5
  · exact hv.1 3
  · exact rho_value d
  · exact rounded_value d

theorem joined_canonical (d : Descriptor) (hs : Fin 6 → List Bool)
    (hv : RecursiveDimensionBank.Headers d hs) (i : Fin 6) :
    GrowingCounterData.Canonical (joinedWords d hs i) := by
  change Fin (5+1) at i
  induction i using Fin.addCases with
  | left i => simpa only [joinedWords,Fin.addCases_left] using dimensions_canonical d hs hv i
  | right i => simpa only [joinedWords,Fin.addCases_right] using rounded_canonical d

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonHeaderWiring
