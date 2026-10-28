module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedBoundaryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCouplingHeaderFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCouplingHeaders
public import IntegerMultBounds.MathlibTM2.Host.EmbedOverwrite

/-! Install and release scalar headers around the linear boundary RHS pipeline. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def boundaryRhsHeaderReg (i : Fin 144) : Fin 148 := ⟨i.val,by omega⟩

theorem boundaryRhsHeaderReg_injective : Function.Injective boundaryRhsHeaderReg := by
  intro i j h
  exact Fin.ext (congrArg (fun r : Fin 148 => r.val) h)

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 148 Q A U}

def closedGeneratedBoundaryRhs : Pr P₀ 148 Q A U :=
  .seq (embProg boundaryRhsHeaderReg Empty.elim (installCouplingHeaders (P₀ := Empty)))
    (.seq generatedBoundaryRhs (embProg boundaryRhsHeaderReg Empty.elim (releaseCouplingHeaders (P₀ := Empty))))

def closedGeneratedBoundaryRhsCost (P q s t u band a b : ℕ) : ℕ :=
  installCouplingHeadersCost P q s t u band a b+generatedBoundaryRhsCost s t band a b (2*q+8)+
    releaseCouplingHeadersCost P q s t u band a b

theorem closedGeneratedBoundaryRhs_exec {s t : ℕ} [NeZero s]
    (P q u band a b : ℕ) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hA : 4 ≤ A)
    (C : ZMod s → GaussianInt) (tail : List (Fin (A+4))) (v : HS 148 Q A U) (S : Stacks 148 A)
    (hsrc : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (hmasters : ∀ r ∈ couplingHeaderCopies, (S.R (boundaryRhsHeaderReg r.1)).length = couplingHeaderValue P q s t u band a b r.1)
    (hheaders : ∀ r ∈ couplingHeaderRegisters, S.R (boundaryRhsHeaderReg r) = [])
    (hcount : (S.R 116).length = (haloBoundary s t band a b).card)
    (hfresh : ∀ r ∈ [(106 : Fin 148),108,135,138,139,143], S.R r = [])
    (hblank : ∀ r : Fin 148, r.val < 77 → S.R r = []) (hleft : ∀ r, S.L r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ closedGeneratedBoundaryRhsCost P q s t u band a b ∧
      Exec body closedGeneratedBoundaryRhs (mk v S) m
        (mk v' {S with R := Function.update S.R 143 (cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C))}) := by
  let e := boundaryRhsHeaderReg
  let T := embStk e S
  let H : Stacks 144 A := {T with R := couplingHeadersR P q s t u band a b T.R}
  let S₁ := embOvr e H.get S
  let output := cstream A (2*q+8) ((bFoldOrder s (haloBoundary s t band a b)).map C)
  let S₂ : Stacks 148 A := {S₁ with R := Function.update S₁.R 143 output}
  obtain ⟨vi,hu₀,he₀⟩ := installCouplingHeaders_from_lengths_exec (body := fun p : Empty => nomatch p)
    P q s t u band a b (embDn e v) T hmasters (hheaders 94 (by decide)) (hfresh 135 (by simp))
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    boundaryRhsHeaderReg_injective (fun p => nomatch p) he₀ v rfl S rfl
  have hproj : embStk e S₁ = H := embStk_ovr boundaryRhsHeaderReg_injective H S
  have hat (i : Fin 144) : S₁.R (e i) = couplingHeadersR P q s t u band a b T.R i :=
    congrArg (fun M : Stacks 144 A => M.R i) hproj
  have hoff (i : Fin 144) (hi : i ∉ couplingHeaderRegisters) : S₁.R (e i) = S.R (e i) := by
    rw [hat,couplingHeadersR_off P q s t u band a b T.R i hi]
    rfl
  have hvalues (r : Fin 144 × Fin 144) (hr : r ∈ couplingHeaderCopies) :
      S₁.R (e r.2) = List.replicate (couplingHeaderValue P q s t u band a b r.1) tick := by
    rw [hat]
    have hdst : r.2 ∈ couplingHeaderRegisters ∧ r.2 ≠ 94 := by
      simp only [couplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    unfold couplingHeadersR
    rw [Function.update_of_ne hdst.2,unaryCopiesR_at _ _ _ (by decide) r hr]
    change _ ++ S.R (e r.2) = _
    rw [hheaders r.2 hdst.1,List.append_nil]
  have hlow : ∀ r : Fin 148, r.val < 77 → S₁.R r = [] := by
    intro r hr
    let i : Fin 144 := ⟨r.val,by omega⟩
    have hei : e i = r := Fin.ext rfl
    have hi : i ∉ couplingHeaderRegisters := by simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff]; dsimp only [i]; omega
    rw [← hei,hoff i hi,hei]
    exact hblank r hr
  have hleft₁ : ∀ r, S₁.L r = [] := by
    have hh : S₁.L = S.L := by
      change embExt e (S.L ∘ e) S.L = S.L
      exact embExt_comp S.L
    simpa only [hh] using hleft
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := generatedBoundaryRhs_exec (body := body) hst haS hbS hA C (2*q+8) tail v₁ S₁
    (by simpa [e,boundaryRhsHeaderReg] using (hoff 110 (by decide)).trans hsrc)
    (by simpa [e,boundaryRhsHeaderReg,couplingHeaderValue] using congrArg List.length (hvalues (121,97) (by decide)))
    (by simpa [e,boundaryRhsHeaderReg,couplingHeaderValue] using congrArg List.length (hvalues (122,98) (by decide)))
    (by simpa [e,boundaryRhsHeaderReg,couplingHeaderValue] using congrArg List.length (hvalues (124,100) (by decide)))
    (by simpa [e,boundaryRhsHeaderReg,couplingHeaderValue] using congrArg List.length (hvalues (141,101) (by decide)))
    (by simpa [e,boundaryRhsHeaderReg,couplingHeaderValue] using congrArg List.length (hvalues (142,103) (by decide)))
    (by simpa [e,boundaryRhsHeaderReg,couplingHeadersR] using congrArg List.length (hat 94))
    (by simpa [e,boundaryRhsHeaderReg] using congrArg List.length (hoff 116 (by decide)) |>.trans hcount)
    (by intro r hr
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl
        · simpa [e,boundaryRhsHeaderReg] using (hoff 106 (by decide)).trans (hfresh 106 (by simp))
        · simpa [e,boundaryRhsHeaderReg] using (hoff 108 (by decide)).trans (hfresh 108 (by simp))
        · simpa [e,boundaryRhsHeaderReg] using (hoff 138 (by decide)).trans (hfresh 138 (by simp))
        · simpa [e,boundaryRhsHeaderReg] using (hoff 139 (by decide)).trans (hfresh 139 (by simp))
        · simpa [e,boundaryRhsHeaderReg] using (hoff 143 (by decide)).trans (hfresh 143 (by simp))) hlow hleft₁
  let T' : Stacks 144 A := {T with R := Function.update T.R 143 output}
  have hz' : ∀ r ∈ couplingHeaderRegisters, T'.R r = [] := by
    intro r hr
    have hn : r ≠ 143 := by simp only [couplingHeaderRegisters,List.mem_cons,List.not_mem_nil,or_false] at hr; rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [T',T,e,embStk,hn] using hheaders r hr
  obtain ⟨vo,hu₃,he₃⟩ := releaseCouplingHeaders_exec (body := fun p : Empty => nomatch p) P q s t u band a b
    (embDn e v₂) T' hz'
  have hinput : embStk e S₂ = {T' with R := couplingHeadersR P q s t u band a b T'.R} := by
    change embStk e {S₁ with R := Function.update S₁.R (e 143) output} = _
    rw [embStk_update_right e boundaryRhsHeaderReg_injective S₁ 143 output,hproj]
    simp only [T',H,couplingHeadersR_update_output]
  obtain ⟨v₃,hv₃,hu₃',he₃'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    boundaryRhsHeaderReg_injective (fun p => nomatch p) he₃ v₂ rfl S₂ hinput
  refine ⟨v₃,installCouplingHeadersCost P q s t u band a b+m₂+releaseCouplingHeadersCost P q s t u band a b,
    hu₃'.trans (hu₃.trans (hu₂.trans (hu₁.trans hu₀))),by dsimp only [closedGeneratedBoundaryRhsCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ he₃')).cast (by omega) ?_⟩
  apply congrArg (mk v₃)
  have hs₂ : S₂ = embOvr e ({H with R := Function.update H.R 143 output} : Stacks 144 A).get S := by
    rw [embOvr_updR boundaryRhsHeaderReg_injective]
    rfl
  change embOvr e T'.get S₂ = _
  rw [hs₂,embOvr_overwrite]
  dsimp only [T']
  rw [embOvr_updR boundaryRhsHeaderReg_injective,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
