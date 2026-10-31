module

public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonHighBody
public import IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighPreparedRunWithin

/-! The actual high body starts with the common preparation output. All its
source contracts follow from the original six shape headers; folding retains
the exact original payload and full transpose endpoints. -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonHighBodyWithin
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.Networks
variable [Net]
noncomputable section
open Networks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonHeaderWiring
open IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open SharedPlacementAlphabet (setTape)
variable {t : ℕ}

open ArbitraryWidthHighCommonHighBody

theorem runs_within (caller : Tapes t prime) (focus : Fin t) (d : Descriptor) (hs : Fin 6 → List Bool)
    (hp : d.Positive) (hv : RecursiveDimensionBank.Headers d hs)
    (hguard : 1 ≤ ArbitraryWidthHighPrepare.highDepth prime d.width ∧
      ArbitraryWidthHighPrepare.highDepth prime d.width < d.width)
    (x : Fin (volume prime d) → ZMod 2)
    (hf : caller.tape focus = sourceWord x) (hh : caller.head focus = 0) (lo hi : ℤ)
    (hmargin : ∀ j, lo+(ArbitraryWidthHighPreparedRunWithin.coefficient*volume prime d : ℕ) ≤
      (input caller d hs).head j ∧ (input caller d hs).head j+
        (ArbitraryWidthHighPreparedRunWithin.coefficient*volume prime d : ℕ) ≤ hi) :
    HoareWithin (program focus) (fun z => z = input caller d hs)
      (fun z => z = input (setTape caller focus
        (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0) d hs)
      (cost d hs) (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  have hfold := folded_headers d hs hv
  have hbase := caller_cells caller d hs focus
  have h := ArbitraryWidthHighPreparedRunWithin.runs_within
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
    (hbase.1.trans hh) lo hi (by
      have hvol : volume prime d = volume prime
          (ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD) :=
        ArbitraryWidthHighFoldSemantics.folded_volume prime d
      rw [← hvol]
      exact hmargin)
  have hword : sourceWord (Shared50RecursiveNodeRows.transpose
      (v := ArbitraryWidthHighLayout.originalDescriptor (foldedPrefix d) d.width d.between d.afterD)
      (one_dvd _) (ArbitraryWidthHighFoldSemantics.foldArray x)) =
      sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd d.rows) x) :=
    ArbitraryWidthHighOriginalEncoding.source_transpose_fold (by decide : 0 < 1) (one_dvd d.rows) x
  rw [hword,changed_common] at h
  exact h

end
end IntegerMultBounds.MathlibTM2.M8.Machine.ArbitraryWidthHighCommonHighBodyWithin
