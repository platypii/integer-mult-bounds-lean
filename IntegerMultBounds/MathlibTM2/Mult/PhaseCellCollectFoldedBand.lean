module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectColumnEntries
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFoldedBandSchedule

/-! Accumulate a contiguous folded-row interval from a computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

theorem collectFoldedBand_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V W n : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hn : n < B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = n-W) (hcount : (S.R 138).length = min B.card (n+W+1)-(n-W))
    (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ collectColumnEntriesCost B q V (n-W) (min B.card (n+W+1)-(n-W)) ∧
      Exec body collectColumnEntries (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 138 []) 132
          (cstream A (2*q+8) ((foldedBandRows B W n).reverse.map C)++S.R 132))
          137 [])}) := by
  let start := n-W
  let L := min B.card (n+W+1)-start
  have hstart : start ≤ min B.card (n+W+1) := by dsimp [start]; omega
  have hfit : start+L ≤ B.card := by dsimp [L]; omega
  have hindices : List.range' start L = (List.range L).map (fun i => start+i) := by
    apply List.ext_getElem <;> simp
  obtain ⟨v',m,hu,hm,he⟩ := collectColumnEntries_exec (body := body) B q V start L hA hs hfit C
    pageTail tail v S hcursor hcount hwidth hpage hq hsource h0 h94 h106 h135 h136 h139 h140 hblank
  refine ⟨v',m,hu,hm,?_⟩
  have hwords : (foldedBandRows B W n).reverse.map C =
      (List.range L).reverse.map (fun i => C (bFoldAt s B (start+i))) := by
    change ((List.range' start L).map (bFoldAt s B)).reverse.map C = _
    rw [hindices]
    simp [List.map_reverse,List.map_map,Function.comp_def]
  simpa only [hwords] using he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
