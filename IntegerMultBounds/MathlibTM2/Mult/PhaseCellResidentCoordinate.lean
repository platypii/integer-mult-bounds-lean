module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedBoundaryFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCopyIndexedWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDecodeNaturalWord

/-! Paid restoring access to a coordinate in the actual folded boundary page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 151 Q A U}

def residentBoundaryWord : Pr P₀ 151 Q A U := copyIndexedWord 0 115 109 106 1 2 3 4 5 6

theorem residentBoundaryWord_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (w j : ℕ)
    (hj : j < B.card) (tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = j) (hwidth : (S.R 115).length = w)
    (hsource : S.R 109 = cstream A w ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+10*w+22 ∧
      Exec body residentBoundaryWord (mk v S) m
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
  exact ⟨v',m,hu,hm,by simpa only [residentBoundaryWord,hword] using he,bFoldAt_mem s B j hj,bFoldPos_bFoldAt s B j hj⟩

def loadResidentCoordinate : Pr P₀ 151 Q A U :=
  .seq residentBoundaryWord (decodeNaturalWord 106 139 1 2 3)

theorem loadResidentCoordinate_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (w j : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^w) (hj : j < B.card)
    (tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = j) (hwidth : (S.R 115).length = w)
    (hsource : S.R 109 = cstream A w ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+9)+27*w+6*(bFoldAt s B j).val+34 ∧
      Exec body loadResidentCoordinate (mk v S) m
        (mk v' {S with R := Function.update S.R 139 (List.replicate (bFoldAt s B j).val tick)}) ∧
      bFoldAt s B j ∈ B ∧ bFoldPos s B (bFoldAt s B j) = j := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hmem,hpos⟩ := residentBoundaryWord_exec (body := body)
    B w j hj tail v S hindex hwidth hsource hblank
  let x := (bFoldAt s B j).val
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 106 (tblPairs A w x 0)}
  have he₁' : Exec body residentBoundaryWord (mk v S) m₁ (mk v₁ S₁) := by
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

def selectResidentCoordinate : Pr P₀ 151 Q A U := .seq loadResidentCoordinate (uclear 0)

theorem selectResidentCoordinate_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (w j : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^w) (hj : j < B.card)
    (tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hindex : (S.R 0).length = j) (hwidth : (S.R 115).length = w)
    (hsource : S.R 109 = cstream A w ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++tail)
    (h106 : S.R 106 = []) (h139 : S.R 139 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ j*(12*w+11)+27*w+6*(bFoldAt s B j).val+36 ∧
      Exec body selectResidentCoordinate (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 0 [])
          139 (List.replicate (bFoldAt s B j).val tick))}) ∧
      bFoldAt s B j ∈ B ∧ bFoldPos s B (bFoldAt s B j) = j := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hmem,hpos⟩ := loadResidentCoordinate_exec (body := body)
    B w j hA hs hj tail v S hindex hwidth hsource h106 h139 hblank
  let S₁ : Stacks 151 A := {S with R := Function.update S.R 139 (List.replicate (bFoldAt s B j).val tick)}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 0 v₁ S₁
  have hlen : (S₁.R 0).length = j := by simpa [S₁] using hindex
  refine ⟨v₂,m₁+(2*j+2),hu₂.trans hu₁,by nlinarith only [hm₁],
    (Exec.seq he₁ he₂).cast (by rw [hlen]) ?_,hmem,hpos⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases h0 : k = 0 <;> by_cases h139' : k = 139 <;> simp [S₁,h0,h139']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
