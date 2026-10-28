module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedGeneratedBoundaryRhs

/-! Run the generated boundary RHS in the family workspace and prepend its owned
output to the factor bank, preserving all borrowed data and the factor suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def familyGeneratedRhsReg (i : Fin 148) : Fin 263 := ⟨i.val,by omega⟩

theorem familyGeneratedRhsReg_injective : Function.Injective familyGeneratedRhsReg := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Fin 263 => r.val) h)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 263 Q A U}

def familyGeneratedBoundaryRhs : Pr P₀ 263 Q A U :=
  .seq (embProg familyGeneratedRhsReg Empty.elim (closedGeneratedBoundaryRhs (P₀ := Empty)))
    (.seq (moveR 143 138 id) (moveR 138 206 id))

def familyGeneratedBoundaryRhsCost (P q s t u band a b : ℕ) : ℕ :=
  closedGeneratedBoundaryRhsCost P q s t u band a b+4*s*(2*q+8)+4

theorem familyGeneratedBoundaryRhs_exec {s t : ℕ} [NeZero s]
    (P q u band a b : ℕ) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 263 Q A U) (S : Stacks 263 A)
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hmasters : ∀ r ∈ couplingHeaderCopies,
      (S.R (familyGeneratedRhsReg (boundaryRhsHeaderReg r.1))).length = couplingHeaderValue P q s t u band a b r.1)
    (hheaders : ∀ r ∈ couplingHeaderRegisters, S.R (familyGeneratedRhsReg (boundaryRhsHeaderReg r)) = [])
    (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (hfresh : ∀ r ∈ [(106 : Fin 148),108,135,138,139,143], S.R (familyGeneratedRhsReg r) = [])
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R (familyGeneratedRhsReg r) = [])
    (hleft : ∀ r : Fin 148, S.L (familyGeneratedRhsReg r) = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ familyGeneratedBoundaryRhsCost P q s t u band a b ∧
      Exec body familyGeneratedBoundaryRhs (mk v S) m
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C)++S.R 206))}) := by
  let e := familyGeneratedRhsReg
  let output := cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C)
  let S₁ : Stacks 263 A := {S with R := Function.update S.R 143 output}
  let S₂ : Stacks 263 A := {S₁ with R := Function.update (Function.update S₁.R 143 []) 138 output.reverse}
  obtain ⟨vi,m,hu,hm,he⟩ := closedGeneratedBoundaryRhs_exec (body := fun p : Empty => nomatch p)
    P q u band a b hst haS hbS hA C tail (embDn e v) (embStk e S)
    hsrc hmasters hheaders hcount hfresh hblank hleft
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    familyGeneratedRhsReg_injective (fun p => nomatch p) he v rfl S rfl
  have hstate : embOvr e {embStk e S with R := Function.update (embStk e S).R 143 output}.get S = S₁ := by
    rw [embOvr_updR familyGeneratedRhsReg_injective,embOvr_stk]
    rfl
  have he₁' : Exec body (embProg e Empty.elim (closedGeneratedBoundaryRhs (P₀ := Empty)))
      (mk v S) m (mk v₁ S₁) := by
    change Exec body _ _ _ (mk v₁ (embOvr e {embStk e S with R := Function.update (embStk e S).R 143 output}.get S)) at he₁
    rw [hstate] at he₁
    exact he₁
  have h138 : S.R 138 = [] := hfresh 138 (by simp)
  have h143 : S.R 143 = [] := hfresh 143 (by simp)
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec (body := body) 143 138 (by decide) id v₁ S₁
  have he₂' : Exec body (moveR 143 138 id) (mk v₁ S₁) (2*output.length+2) (mk v₂ S₂) := by
    convert he₂ using 1 <;> simp [S₁,S₂,movedR,h138]
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 138 206 (by decide) id v₂ S₂
  have he₃' : Exec body (moveR 138 206 id) (mk v₂ S₂) (2*output.length+2)
      (mk v₃ {S with R := Function.update S.R 206 (output++S.R 206)}) := by
    convert he₃ using 1
    · simp [S₂,S₁]
    · apply congrArg (mk v₃)
      refine Stacks.ext rfl rfl rfl ?_
      funext r
      by_cases h : r = 143
      · subst r; simp [movedR,S₂,S₁,h143]
      by_cases h' : r = 138
      · subst r; simp [movedR,S₂,S₁,h138]
      simp [movedR,S₂,S₁,h,h',Function.update_apply]
  have hlen : output.length = (haloBoundary s t band a b).card*(2*q+8) := by
    simp [output,bFoldOrder]
  have hcard : (haloBoundary s t band a b).card ≤ s := by
    simpa using (haloBoundary s t band a b).card_le_univ
  refine ⟨v₃,m+(2*output.length+2)+(2*output.length+2),hu₃.trans (hu₂.trans (hu₁.trans hu)),?_,?_⟩
  · dsimp only [familyGeneratedBoundaryRhsCost]
    rw [hlen]
    have hprod := Nat.mul_le_mul_right (2*q+8) hcard
    nlinarith only [hm,hprod]
  · exact (Exec.seq he₁' (Exec.seq he₂' he₃')).cast (by omega) rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
