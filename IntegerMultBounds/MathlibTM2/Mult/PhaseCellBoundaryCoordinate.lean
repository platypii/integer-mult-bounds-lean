module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyIndexedWord

/-! Paid restoring access to a coordinate in the actual folded boundary page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def boundaryCoordinate : Pr P₀ 148 Q A U := copyIndexedWord 0 115 109 106 1 2 3 4 5 6

theorem boundaryCoordinate_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (w j : ℕ)
    (hj : j < B.card) (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hindex : (S.R 0).length = j) (hwidth : (S.R 115).length = w)
    (hsource : S.R 109 = cstream A w ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+22 ∧
      Exec body boundaryCoordinate (mk v S) m
        (mk v' {S with R := (Function.update S.R 106
          (tblPairs A w (bFoldAt s B j).val 0++S.R 106))}) ∧
      bFoldAt s B j ∈ B ∧ bFoldPos s B (bFoldAt s B j) = j := by
  let xs := (bFoldOrder s B).map (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt))
  have hjxs : j < xs.length := by simpa [xs,bFoldOrder] using hj
  obtain ⟨v',m,hu,hm,he⟩ := copyIndexedWord_exec (body := body)
    (index := 0) (width := 115) (src := 109) (dst := 106) (skip := 1)
    (savedSkip := 2) (saved := 3) (tmp := 4) (work₁ := 5) (work₂ := 6) (by decide)
    w j xs hjxs tail v S hindex hwidth hsource (by
      intro r hr
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl <;> exact hblank _ (by decide) (by decide))
  have hword : csyms A w xs[j] = tblPairs A w (bFoldAt s B j).val 0 := by
    simp [xs,bFoldOrder,csyms,red,tblPairs]
  exact ⟨v',m,hu,hm,by simpa only [boundaryCoordinate,hword] using he,bFoldAt_mem s B j hj,bFoldPos_bFoldAt s B j hj⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
