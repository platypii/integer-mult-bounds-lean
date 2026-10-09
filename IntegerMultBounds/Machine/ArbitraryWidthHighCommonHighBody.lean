import IntegerMultBounds.Machine.ArbitraryWidthHighPreparedRun
import IntegerMultBounds.Machine.ArbitraryWidthHighCommonHeaderWiring
import IntegerMultBounds.Machine.ArbitraryWidthHighOriginalEncoding

/-! The actual high body starts with the common preparation output. All its
source contracts follow from the original six shape headers; folding retains
the exact original payload and full transpose endpoints. -/
namespace IntegerMultBounds.Machine.ArbitraryWidthHighCommonHighBody
noncomputable section
open Networks
open Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighCommonHeaderWiring
open ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

def callerSlot (focus : Fin t) : Fin ((t+16)+19) := Fin.castAdd 19 (Fin.castAdd 16 focus)

def input (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) :=
  ArbitraryWidthHighPreparedRun.input (ArbitraryWidthHighCommonPrepare.output caller d hs prime)

def program (focus : Fin t) := ArbitraryWidthHighPreparedRun.program (callerSlot focus)
  dimensionsFocus joinedFocus exchangeFocus rowFocus roundedFocus

def cost (d : Descriptor) (hs : Fin 6 → List Bool) :=
  ArbitraryWidthHighPreparedRun.cost (foldedPrefix d) d.width d.between d.afterD (joinedWords d hs)

theorem caller_cells (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool) (focus : Fin t) :
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).head (callerSlot focus) = caller.head focus ∧
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime).tape (callerSlot focus) = caller.tape focus := by
  simp only [callerSlot,ArbitraryWidthHighCommonPrepare.output,Tapes.append,Fin.addCases_left]
  exact ⟨trivial,trivial⟩

private theorem changed_common (caller : Tapes t prime) (d : Descriptor) (hs : Fin 6 → List Bool)
    (focus : Fin t) (word : ℤ → Fin (prime+4)) :
    setTape (ArbitraryWidthHighCommonPrepare.output caller d hs prime) (callerSlot focus) word 0 =
      ArbitraryWidthHighCommonPrepare.output (setTape caller focus word 0) d hs prime := by
  unfold callerSlot ArbitraryWidthHighCommonPrepare.output
  rw [SharedPlacementAlphabet.setTape_append_left,SharedPlacementAlphabet.setTape_append_left]

theorem runs (caller : Tapes t prime) (focus : Fin t) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (hguard : 1 ≤ ArbitraryWidthHighPrepare.highDepth prime d.width ∧
      ArbitraryWidthHighPrepare.highDepth prime d.width < d.width)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) :
    HoareTime (program focus) (fun z => z = input caller d hs)
      (fun z => z = input (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0) d hs)
      (cost d hs) := by
  have hfold := folded_headers d hs hv
  have hbase := caller_cells caller d hs focus
  have h := ArbitraryWidthHighPreparedRun.runs
    (ArbitraryWidthHighCommonPrepare.output caller d hs prime) (callerSlot focus)
    dimensionsFocus joinedFocus exchangeFocus rowFocus roundedFocus
    (foldedPrefix d) d.width d.between d.afterD (foldedPrefix_positive d hp)
    hp.2.2.2.1 hp.2.2.2.2 hguard.2.le
    (dimensionsWords d hs) (joinedWords d hs) (ArbitraryWidthHighFoldHeaders.words d hs)
    (rhoWord d) (rowWord d) (roundedWord d)
    (dimensions_values d hs hv) (dimensions_canonical d hs hv)
    (joined_values d hs hv) (joined_canonical d hs hv)
    (dimensions_sources caller d hs) (joined_sources caller d hs) (exchange_sources caller d hs)
    hfold (rho_value d) (rho_canonical d) (row_value d) (row_canonical d)
    (rounded_value d) (rounded_canonical d) (row_cells caller d hs).2 (row_cells caller d hs).1
    (rounded_cells caller d hs).2 (rounded_cells caller d hs).1
    (ArbitraryWidthHighFoldSemantics.foldArray x)
    (hbase.2.trans (hf.trans (ArbitraryWidthHighOriginalEncoding.source_fold x).symm))
    (hbase.1.trans hh)
  have hword : sourceWord (Shared50RecursiveNodeRows.transpose
      (v := ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD)
      (one_dvd _) (ArbitraryWidthHighFoldSemantics.foldArray x)) =
      sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) :=
    ArbitraryWidthHighOriginalEncoding.source_transpose_fold (by decide : 0 < 1) (one_dvd d.rows) x
  rw [hword,changed_common] at h
  exact h

theorem cost_bound (d : Descriptor) (hs : Fin 6 → List Bool)
    (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (hr : ArbitraryWidthHighPrepare.highDepth prime d.width < d.width) :
    (cost d hs : ℝ) ≤ ArbitraryWidthHighPreparedRun.coefficient*
      (volume prime d : ℝ)*(d.width : ℝ)^Parameters.tau := by
  have h := ArbitraryWidthHighPreparedRun.cost_bound (foldedPrefix d) d.width d.between d.afterD
    (joinedWords d hs) (foldedPrefix_positive d hp) hp.2.2.2.1 hp.2.2.2.2 hr
    (joined_values d hs hv) (joined_canonical d hs hv)
  have hvol : volume prime d = volume prime
      (ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD) :=
    ArbitraryWidthHighFoldSemantics.folded_volume prime d
  rw [← hvol] at h
  exact h

end
end IntegerMultBounds.Machine.ArbitraryWidthHighCommonHighBody
