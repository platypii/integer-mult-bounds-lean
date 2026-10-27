module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingSourceMaskCode
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginRelease
public import IntegerMultBounds.MathlibTM2.Fast.TableBounds

/-! Execute and release the geometry table, retaining one selection symbol per coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Layer
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

def couplingSourceMaskSymbols (boundary : Bool) (A s t band a b : ℕ) : List (Fin (A+4)) :=
  (List.range s).map (fun k => pairSym A (haloMaskAt boundary s t band a b k) (haloMaskAt boundary s t band a b k))

@[simp] theorem couplingSourceMaskSymbols_length (boundary : Bool) (A s t band a b : ℕ) :
    (couplingSourceMaskSymbols boundary A s t band a b).length = s := by simp [couplingSourceMaskSymbols]

theorem couplingSourceMaskSymbols_getElem (boundary : Bool) (A s t band a b k : ℕ) (hk : k < s) :
    (couplingSourceMaskSymbols boundary A s t band a b)[k]'(by simpa using hk) =
      pairSym A (haloMaskAt boundary s t band a b k) (haloMaskAt boundary s t band a b k) := by
  simp [couplingSourceMaskSymbols]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def couplingSourceMaskHost (boundary : Bool) : Pr P₀ 117 Q A U :=
  .seq (uclear 17) (.seq (.act (.push (.rt 17) (fun _ => tick) .done))
    (.seq (tblCompile originReg (couplingSourceMaskCode boundary)) (.seq (moveR 18 109 id) releaseOriginBank)))

def couplingSourceMaskHostCost (V s : ℕ) : ℕ := (29*s+3)*tblC V 1+64*V+2*s+68

theorem couplingSourceMaskHost_exec (boundary : Bool) {V s t band a b : ℕ} (st : TblSt 16 A)
    (hs : st.val 0 = s) (ht : st.val 1 = t) (hband : st.val 2 = band)
    (ha : st.val 4 = a) (hb : st.val 5 = b) (hacc : st.acc = [])
    (hs0 : 0 < s) (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : band ≤ s)
    (hwide : 8*(t+1)^2+2*band+8 < 2^V) (hbound : ∀ r, st.val r < 2^V)
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds originReg S (tblRho V (List.replicate V tick) (List.replicate V tick) st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ couplingSourceMaskHostCost V s ∧
      Exec body (couplingSourceMaskHost boundary) (mk v S) m
        (mk v' {S with R := fun r => if r.val < 31 then [] else if r = 109 then
          couplingSourceMaskSymbols boundary A s t band a b++S.R r else S.R r}) := by
  have hV : 1 ≤ V := by
    by_contra h
    have : V = 0 := by omega
    subst V
    norm_num at hwide
  have h17 : S.R 17 = List.replicate V tick := by simpa [originReg,tblRho] using hS .wn
  obtain ⟨v₁,hu₁,he₁⟩ := uclear_exec (body := body) 17 v S
  let S₁ : Stacks 117 A := {S with R := Function.update S.R 17 []}
  have he₁' : Exec body (uclear 17) (mk v S) (2*V+2) (mk v₁ S₁) := by
    simpa [S₁,h17] using he₁
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 17 [tick]}
  have he₂ : Exec body (.act (.push (.rt 17) (fun _ => tick) .done)) (mk v₁ S₁) 1 (mk v₁ S₂) := by
    simpa [S₂,S₁,Action.run,update_rt] using
      (Exec.act (body := body) (.push (.rt 17) (fun _ => tick) .done) (mk v₁ S₁))
  have hh₂ : tblHolds originReg S₂ (tblRho V (List.replicate V tick) [tick] st) := by
    intro r
    by_cases hr : r = .wn
    · subst r; simp [S₂,S₁,originReg,tblRho]
    · have hne : originReg r ≠ (17 : Fin 117) := by
        change originReg r ≠ originReg .wn
        exact originReg_injective.ne hr
      have hh := hS r
      cases r <;> simp_all [S₂,S₁,tblRho]
  have hc := couplingSourceMaskCode_do boundary (A := A) (V := V) (w := 1) st hs ht hband ha hb
    hs0 hst haS hbS hbandS hwide
  obtain ⟨st',hout,hrun⟩ := TblDo.host (body := body) originReg_injective
    (List.replicate V tick) [tick] (by simp) (by simp) hV (hc.bounded hbound) hbound
  obtain ⟨v₃,S₃,m₃,hu₃,hm₃,he₃,hh₃,hf₃⟩ := hrun v₁ S₂ hh₂
  have hmask : (List.range s).flatMap (fun k =>
      tblPairs A 1 (if haloMaskAt boundary s t band a b k then 1 else 0)
        (if haloMaskAt boundary s t band a b k then 1 else 0)) = couplingSourceMaskSymbols boundary A s t band a b := by
    simp only [couplingSourceMaskSymbols,publicationMaskSymbol]
    exact List.map_eq_flatMap.symm
  have hacc₃ : S₃.R 18 = (couplingSourceMaskSymbols boundary A s t band a b).reverse := by
    have hh := hh₃ .acc
    simpa [originReg,tblRho,hout,hacc,hmask] using hh
  have hoff₃ (r : Fin 117) (hr : 31 ≤ r.val) : S₃.R r = S.R r := by
    have hne : ∀ x, originReg x ≠ r := by
      intro x he
      have hx := originReg_range x
      rw [he] at hx
      omega
    rw [hf₃.2.2.2 r hne]
    simp [S₂,S₁,show r ≠ 17 by intro he; subst r; norm_num at hr]
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 18 109 (by decide) id v₃ S₃
  let S₄ : Stacks 117 A := {S₃ with R := movedR S₃.R 18 109 id (S₃.R 18)}
  have hh₄ : tblHolds originReg S₄ (tblRho V (List.replicate V tick) [tick] ⟨st'.val,[]⟩) := by
    intro r
    have hne : originReg r ≠ (109 : Fin 117) := by
      intro he
      have hx := originReg_range r
      rw [he] at hx
      omega
    by_cases hr : r = .acc
    · subst r; simp [S₄,movedR,originReg,tblRho]
    · have ha : originReg r ≠ (18 : Fin 117) := by
        change originReg r ≠ originReg .acc
        exact originReg_injective.ne hr
      have hh := hh₃ r
      cases r <;> simp_all [S₄,movedR,tblRho]
  obtain ⟨v₅,m₅,hu₅,hm₅,he₅⟩ := releaseOriginBank_width_exec (body := body) V 1 hV st'.val v₄ S₄ hh₄
  refine ⟨v₅,(2*V+2)+(1+(m₃+((2*s+2)+m₅))),hu₅.trans (hu₄.trans (hu₃.trans hu₁)),?_,
    (Exec.seq he₁' (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))).cast ?_ ?_⟩
  · dsimp only [couplingSourceMaskHostCost]
    nlinarith only [hm₃,hm₅]
  · simp [hacc₃]
  · apply congrArg (mk v₅)
    refine Stacks.ext hf₃.1 hf₃.2.1 hf₃.2.2.1 ?_
    funext r
    by_cases hr : r.val < 31
    · simp [hr]
    · have hr' : 31 ≤ r.val := by omega
      by_cases h109 : r = 109
      · subst r; simp [S₄,movedR,hacc₃,hoff₃ 109 (by decide)]
      · have h18 : r ≠ 18 := by intro he; subst r; norm_num at hr
        simp [hr,h109,S₄,movedR,h18,hoff₃ r hr']

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
