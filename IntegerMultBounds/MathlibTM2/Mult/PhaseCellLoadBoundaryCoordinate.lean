module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDecodeNaturalWord

/-! Restoring folded-page lookup followed by paid unary coordinate decoding. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

def loadBoundaryCoordinate : Pr P 148 Q A U :=
  .seq boundaryCoordinate (decodeNaturalWord 106 139 1 2 3)

theorem loadBoundaryCoordinate_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (w j : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^w) (hj : j < B.card)
    (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hindex : (S.R 0).length = j) (hwidth : (S.R 115).length = w)
    (hsource : S.R 109 = cstream A w ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+27*w+6*(bFoldAt s B j).val+34 ∧
      Exec body loadBoundaryCoordinate (mk v S) m
        (mk v' {S with R := Function.update S.R 139 (List.replicate (bFoldAt s B j).val tick)}) ∧
      bFoldAt s B j ∈ B ∧ bFoldPos s B (bFoldAt s B j) = j := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hmem,hpos⟩ := boundaryCoordinate_exec (body := body)
    B w j hj tail v S hindex hwidth hsource hblank
  let x := (bFoldAt s B j).val
  let S₁ : Stacks 148 A := {S with R := Function.update S.R 106 (tblPairs A w x 0)}
  have he₁' : Exec body boundaryCoordinate (mk v S) m₁ (mk v₁ S₁) := by
    simpa [S₁,x,h106] using he₁
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := decodeNaturalWord_exec (body := body)
    (src := 106) (dst := 139) (work := 1) (saved := 2) (tmp := 3) (by decide)
    hA w x ((bFoldAt s B j).val_lt.trans_le hs) v₁ S₁ (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> simpa [S₁] using hblank _ (by decide) (by decide))
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,by dsimp [x] at hm₂; omega,
    Exec.seq he₁' ?_,hmem,hpos⟩
  convert he₂ using 1
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h106' : k = 106 <;> by_cases h139' : k = 139 <;>
    simp_all [S₁,Function.update_apply,x]

/-- The width generated with the folded page fits every ambient coordinate. -/
theorem loadBoundaryCoordinate_generatedWidth {s t band a b : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (j : ℕ) (hj : j < (haloBoundary s t band a b).card)
    (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hindex : (S.R 0).length = j)
    (hwidth : (S.R 115).length = publicationGeometryWidth t band)
    (hsource : S.R 109 = cstream A (publicationGeometryWidth t band)
      ((bFoldOrder s (haloBoundary s t band a b)).map
        (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 148, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    let B := haloBoundary s t band a b
    let w := publicationGeometryWidth t band
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+27*w+6*(bFoldAt s B j).val+34 ∧
      Exec body loadBoundaryCoordinate (mk v S) m
        (mk v' {S with R := Function.update S.R 139 (List.replicate (bFoldAt s B j).val tick)}) ∧
      bFoldAt s B j ∈ B ∧ bFoldPos s B (bFoldAt s B j) = j := by
  have hfit := publicationGeometryWidth_fits t band
  have hs : s ≤ 2^(publicationGeometryWidth t band) := by nlinarith only [hfit,hst]
  exact loadBoundaryCoordinate_exec (haloBoundary s t band a b) (publicationGeometryWidth t band)
    j hA hs hj tail v S hindex hwidth hsource h106 h139 hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
