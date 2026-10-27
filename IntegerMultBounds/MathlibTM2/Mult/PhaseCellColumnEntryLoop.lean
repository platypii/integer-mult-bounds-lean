module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellColumnEntryStep

/-! Accumulate a contiguous folded-row interval from a computed column. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

def columnEntryLoop : Pr P 151 Q A U := scanP 138 140 columnEntryStep

noncomputable def columnEntryLoopCost {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V start L : ℕ) : ℕ :=
  (∑ i ∈ Finset.range L, (columnEntryStepCost q V (start+i) (bFoldAt s B (start+i)).val+3))+2*L+4

theorem columnEntryLoop_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q V start L : ℕ)
    (hA : 4 ≤ A) (hs : s ≤ 2^V) (hfit : start+L ≤ B.card) (C : ZMod s → GaussianInt)
    (pageTail tail : List (Fin (A+4))) (v : HS 151 Q A U) (S : Stacks 151 A)
    (hcursor : (S.R 137).length = start) (hcount : (S.R 138).length = L)
    (hwidth : (S.R 115).length = V)
    (hpage : S.R 109 = cstream A V ((bFoldOrder s B).map
      (fun k : ZMod s => (⟨(k.val : ℤ),0⟩ : GaussianInt)))++pageTail)
    (hq : (S.R 119).length = q)
    (hsource : S.R 110 = cstream A (2*q+8) (chirpLine s C)++tail)
    (h0 : S.R 0 = []) (h94 : S.R 94 = []) (h106 : S.R 106 = [])
    (h135 : S.R 135 = []) (h136 : S.R 136 = []) (h139 : S.R 139 = []) (h140 : S.R 140 = [])
    (hblank : ∀ r : Fin 151, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ columnEntryLoopCost B q V start L ∧
      Exec body columnEntryLoop (mk v S) m
        (mk v' {S with R := (Function.update (Function.update S.R 132
          (cstream A (2*q+8) ((List.range L).reverse.map (fun i => C (bFoldAt s B (start+i))))++S.R 132))
          137 (List.replicate L tick++S.R 137))}) := by
  let F := fun i => C (bFoldAt s B (start+i))
  let Ψ : ℕ → Regs 151 A := fun i => Function.update (Function.update S.R
    132 (cstream A (2*q+8) ((List.range i).reverse.map F)++S.R 132))
    137 (List.replicate i tick++S.R 137)
  have hstep : IterSpec body columnEntryStep 138 140 Ψ
      (fun i => columnEntryStepCost q V (start+i) (bFoldAt s B (start+i)).val) L := by
    intro i hi vi Si hSi
    have hoff (k : Fin 151) (hk132 : k ≠ 132) (hk137 : k ≠ 137)
        (hk138 : k ≠ 138) (hk140 : k ≠ 140) : Si.R k = S.R k := by
      rw [hSi k hk138 hk140]
      simp [Ψ,hk132,hk137]
    have hcursor' : (Si.R 137).length = start+i := by
      rw [hSi 137 (by decide) (by decide)]
      simp [Ψ,hcursor,Nat.add_comm]
    obtain ⟨vi',m,hu,hm,he⟩ := columnEntryStep_exec (body := body) B q V (start+i)
      hA hs (by omega) C pageTail tail vi Si hcursor'
      (by rw [hoff 115 (by decide) (by decide) (by decide) (by decide)]; exact hwidth)
      (by rw [hoff 109 (by decide) (by decide) (by decide) (by decide)]; exact hpage)
      (by rw [hoff 119 (by decide) (by decide) (by decide) (by decide)]; exact hq)
      (by rw [hoff 110 (by decide) (by decide) (by decide) (by decide)]; exact hsource)
      (by rw [hoff 0 (by decide) (by decide) (by decide) (by decide)]; exact h0)
      (by rw [hoff 94 (by decide) (by decide) (by decide) (by decide)]; exact h94)
      (by rw [hoff 106 (by decide) (by decide) (by decide) (by decide)]; exact h106)
      (by rw [hoff 135 (by decide) (by decide) (by decide) (by decide)]; exact h135)
      (by rw [hoff 136 (by decide) (by decide) (by decide) (by decide)]; exact h136)
      (by rw [hoff 139 (by decide) (by decide) (by decide) (by decide)]; exact h139) (by
        intro k hk1 hk7
        rw [hoff k (by omega) (by omega) (by omega) (by omega)]
        exact hblank k hk1 hk7)
    let R' := Function.update (Function.update Si.R 132 (csyms A (2*q+8) (F i)++Si.R 132))
      137 (tick::Si.R 137)
    refine ⟨vi',R',m,hu,hm,he,by simp [R'],by simp [R'],?_⟩
    intro k hk138 hk140
    by_cases hk132 : k = 132
    · subst k
      rw [show R' 132 = csyms A (2*q+8) (F i)++Si.R 132 by simp [R'],hSi 132 (by decide) (by decide)]
      simp [Ψ,List.range_succ,List.reverse_append,cstream,List.append_assoc]
    by_cases hk137 : k = 137
    · subst k
      rw [show R' 137 = tick::Si.R 137 by simp [R'],hSi 137 (by decide) (by decide)]
      simp [Ψ,List.replicate_succ]
    rw [show R' k = Si.R k by simp [R',hk132,hk137],hSi k hk138 hk140]
    simp [Ψ,hk132,hk137]
  obtain ⟨v',R',m,hu,hm,he,h138,h140',hrest⟩ := scanP_exec (body := body)
    (show (138 : Fin 151) ≠ 140 by decide) hstep 0 v S (by simp [hcount]) (by
      intro k _ _
      by_cases hk132 : k = 132 <;> by_cases hk137 : k = 137 <;> simp [Ψ,hk132,hk137])
  have hR : R' = Ψ L := by
    funext k
    by_cases hk138 : k = 138
    · subst k; simpa [Ψ,h140] using h138
    by_cases hk140 : k = 140
    · subst k; simpa [Ψ,h140] using h140'
    simpa [hcount] using hrest k hk138 hk140
  rw [hR] at he
  refine ⟨v',m,hu,?_,he⟩
  simpa [columnEntryLoopCost,hcount,h140] using hm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
