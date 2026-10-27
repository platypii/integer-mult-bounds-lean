module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedEntryAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyPackedWord

/-! Copy an addressed packed boundary entry and identify its exact decoded matrix value. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

theorem packedBoundaryEntry_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (haddress : (S.R 0).length = packedEntryOffset B.card W n m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail)
    (h94 : S.R 94 = []) (h135 : S.R 135 = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    let word := csyms A (2*q+8) (columns[n] (bFoldAt s B m))
    let S' : Stacks 154 A := {S with R := Function.update S.R 143 (word++S.R 143)}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ copyPackedWordCost q (packedEntryOffset B.card W n m) ∧
      Exec body copyPackedWord (mk v S) steps (mk v' S') ∧
      (value q (decodeWord ((S'.R 143).take (2*q+8)))).re =
        bandBoundaryTable B W (computedBoundaryTable A q (2*q+8) B columns)
          (bFoldAt s B m) (bFoldAt s B n) := by
  dsimp only
  obtain ⟨hk,hentry⟩ := packedEntryOffset_entry B W columns hlen n m hn hm
  obtain ⟨v',steps,hu,hsteps,he⟩ := copyPackedWord_exec (body := body) q (packedEntryOffset B.card W n m)
    (bandTableValues B W columns 0) hk tail v S hq haddress
    (by simpa only [bandTableWords_values] using hsource) h94 h135 hblank
  refine ⟨v',steps,hu,hsteps,?_,?_⟩
  · simpa only [hentry] using he
  · obtain ⟨hmN,hmn,hnm⟩ := (mem_foldedBandIndices hn).mp hm
    have hrel : FoldBRel s B W (bFoldAt s B m) (bFoldAt s B n) := by
      simpa only [FoldBRel,bFoldPos_bFoldAt s B m hmN,bFoldPos_bFoldAt s B n hn] using And.intro hmn hnm
    have hn' : n < columns.length := by omega
    simp [List.take_append,bandBoundaryTable,hrel,computedBoundaryTable,
      bFoldPos_bFoldAt s B n hn,hn',columnWordRead]
    rw [getElem_congr rfl (bFoldPos_bFoldAt s B n hn)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
