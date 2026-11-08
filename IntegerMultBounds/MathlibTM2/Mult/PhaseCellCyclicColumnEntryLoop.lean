module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicColumnEntryStep
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWordCollectionScan

/-! Collect selected cyclic residual entries in reverse folded-row order. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def cyclicColumnEntryLoop : Pr P 151 Q A U := scanP 138 140 cyclicColumnEntryStep

noncomputable def cyclicColumnEntryLoopCost {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (q V a b start L : ℕ) : ℕ :=
  (∑ j ∈ Finset.range L, (cyclicColumnEntryStepCost q V s a b (start+j) (bFoldAt s B (start+j)).val+3))+2*L+4

theorem cyclicColumnEntryLoop_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V a b start L : ℕ)
    (hA : 4 ≤ A) (hwide : s+s ≤ 2^V) (ha : a ≤ s) (hb : b ≤ s) (hfit : start+L ≤ B.card)
    (C D : ZMod s → GaussianInt) (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = start) (hcount : (S.R 138).length = L)
    (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q) (hs : (S.R 121).length = s)
    (haSrc : (S.R 144).length = a) (hbSrc : (S.R 145).length = b)
    (hsource : S.R 132 = cstream A (2*q+8) (chirpLine s D)++(cstream A (2*q+8) (chirpLine s C)++tail))
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = [])
    (hblank : ∀ k : Fin 151, k.val < 31 → k ≠ 0 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ cyclicColumnEntryLoopCost B q V a b start L ∧
      Exec body cyclicColumnEntryLoop (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 150
          (cstream A (2*q+8) ((List.range L).reverse.map (fun j =>
            let i := bFoldAt s B (start+j)
            if a ≤ i.val ∧ i.val < b then C i else D i))++S.R 150))
          137 (List.replicate L tick++S.R 137))}) := by
  let F := fun j => let i := bFoldAt s B (start+j); if a ≤ i.val ∧ i.val < b then C i else D i
  apply wordCollectionScan_exec cyclicColumnEntryStep 138 140 150 137 (by decide)
    (2*q+8) L F (fun j => cyclicColumnEntryStepCost q V s a b (start+j) (bFoldAt s B (start+j)).val) v S hcount h140
  intro j hj vi Si hSi
  have hoff (k : Fin 151) (h150 : k ≠ 150) (h137 : k ≠ 137) (h138 : k ≠ 138) (h140 : k ≠ 140) :
      Si.R k = S.R k := by
    rw [hSi k h138 h140]
    simp [wordCollectionR,h150,h137]
  have hcursor' : (Si.R 137).length = start+j := by
    rw [hSi 137 (by decide) (by decide)]
    simp [wordCollectionR,hcursor,Nat.add_comm]
  exact cyclicColumnEntryStep_exec (body := body) B q V a b (start+j) hA hwide ha hb (by omega) C D pageTail tail vi Si hcursor'
    (by rw [hoff 115 (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
    (by rw [hoff 109 (by decide) (by decide) (by decide) (by decide)]; exact hpage)
    (by rw [hoff 119 (by decide) (by decide) (by decide) (by decide)]; exact hq)
    (by rw [hoff 121 (by decide) (by decide) (by decide) (by decide)]; exact hs)
    (by rw [hoff 144 (by decide) (by decide) (by decide) (by decide)]; exact haSrc)
    (by rw [hoff 145 (by decide) (by decide) (by decide) (by decide)]; exact hbSrc)
    (by rw [hoff 132 (by decide) (by decide) (by decide) (by decide)]; exact hsource)
    (by rw [hoff 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
    (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact h94)
    (by rw [hoff 106 (by decide) (by decide) (by decide) (by decide)]; exact h106)
    (by rw [hoff 135 (by decide) (by decide) (by decide) (by decide)]; exact h135)
    (by rw [hoff 136 (by decide) (by decide) (by decide) (by decide)]; exact h136)
    (by rw [hoff 139 (by decide) (by decide) (by decide) (by decide)]; exact h139)
    (by intro k hk hk0
        rw [hoff k (by omega) (by omega) (by omega) (by omega)]
        exact hblank k hk hk0)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
