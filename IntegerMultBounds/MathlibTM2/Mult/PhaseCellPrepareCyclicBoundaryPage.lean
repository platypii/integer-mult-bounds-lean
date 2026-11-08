module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedCyclicPageFold
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedCyclicBoundaryOrder
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCyclicEndpoints
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableBoundaryFold

/-! Build the joint folded coordinate page from ordinary retained dimensions. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def residentPublicationWidth : Pr P 154 Q A U :=
  embProg (boundaryPieceReg false) Empty.elim (generatePublicationWidth (P₀ := Empty))

theorem residentPublicationWidth_exec (t band : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (ht : (S.R 122).length = t) (hb : (S.R 124).length = band) (h115 : S.R 115 = [])
    (hlow : ∀ k : Fin 154, k.val < 31 → S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ generatePublicationWidthCost t band ∧
      Exec body residentPublicationWidth (mk v S) m
        (mk v' {S with R := Function.update S.R 115 (List.replicate (publicationGeometryWidth t band) tick)}) := by
  obtain ⟨vi,m,hu,hm,he⟩ := generatePublicationWidth_exec (body := fun e : Empty => nomatch e)
    t band (embDn (boundaryPieceReg false) v) (embStk (boundaryPieceReg false) S)
    (by simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using ht)
    (by simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using hb)
    (by simpa [embStk,boundaryPieceReg,boundaryPieceBase,Equiv.swap_apply_def] using h115)
    (by intro k hk
        have hk31 : k.val < 31 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl <;> decide
        change S.R (boundaryPieceReg false k) = []
        rw [boundaryPieceReg_low false k hk31]
        exact hlow _ hk31)
  obtain ⟨vf,_,hv,hf⟩ := exec_emb_ovr (e := boundaryPieceReg false) (ι := Empty.elim) (body' := body)
    (boundaryPieceReg_injective false) (fun e => nomatch e) he v rfl S rfl
  refine ⟨vf,m,hv.trans hu,hm,hf.cast rfl ?_⟩
  apply congrArg (mk vf)
  rw [embOvr_updR (boundaryPieceReg_injective false) (embStk (boundaryPieceReg false) S) S 115 _,embOvr_stk]
  rfl

def prepareCyclicBoundaryPage : Pr P 154 Q A U :=
  .seq residentPublicationWidth (.seq retainedCyclicEndpoints
    (.seq countedCyclicBoundaryOrder
      (embProg tableFoldReg Empty.elim (closedCyclicPageFold (P := Empty)))))

def prepareCyclicBoundaryPageCost (R : Regs 154 A) (s t band a n : ℕ) [NeZero s] : ℕ :=
  let V := publicationGeometryWidth t band
  let N := (cyclicPrincipalBoundary s t band a n).card
  generatePublicationWidthCost t band+(retainedCyclicEndpointsCost R V a n+
    ((residentCyclicBoundaryOrderCost V s t band a n+N*(6*V+6)+4)+closedCyclicPageFoldCost N V))

theorem prepareCyclicBoundaryPage_exec {s t band a n : ℕ} [NeZero s]
    (hst : s < t) (ha : a < s) (hn : n ≤ s) (hband : band ≤ s)
    (v : HS 154 Q A U) (S : Stacks 154 A)
    (hs : (S.R 121).length = s) (ht : (S.R 122).length = t) (hb : (S.R 124).length = band)
    (haSrc : (S.R 141).length = a) (hnSrc : (S.R 142).length = n)
    (hfresh : ∀ k ∈ [(106 : Fin 154),108,109,115,116,135,138,144,145,146], S.R k = [])
    (hlow : ∀ k : Fin 154, k.val < 77 → S.R k = []) (hleft : ∀ k, S.L k = []) :
    let V := publicationGeometryWidth t band
    let N := (cyclicPrincipalBoundary s t band a n).card
    let output := cstream A V ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
      (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
    let R := Function.update (Function.update (Function.update (Function.update (Function.update S.R
      141 []) 142 []) 144 (List.replicate a tick)) 145 (List.replicate (a+min n (s-a)) tick))
        146 (List.replicate (n-min n (s-a)) tick)
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareCyclicBoundaryPageCost S.R s t band a n ∧
      Exec body prepareCyclicBoundaryPage (mk v S) m
        (mk v' {S with R := (Function.update (Function.update (Function.update R
          115 (List.replicate V tick)) 116 (List.replicate N tick)) 109 output)}) := by
  dsimp only
  let V := publicationGeometryWidth t band
  let N := (cyclicPrincipalBoundary s t band a n).card
  let output := cstream A V ((bFoldOrder s (cyclicPrincipalBoundary s t band a n)).map
    (fun j : ZMod s => (⟨(j.val : ℤ),0⟩ : GaussianInt)))
  obtain ⟨v₀,m₀,hv₀,hm₀,he₀⟩ := residentPublicationWidth_exec (body := body) t band v S ht hb
    (hfresh 115 (by simp)) (by intro k hk; exact hlow k (by omega))
  let S₀ : Stacks 154 A := {S with R := Function.update S.R 115 (List.replicate V tick)}
  obtain ⟨v₁,m₁,hv₁,hm₁,he₁⟩ := retainedCyclicEndpoints_exec (body := body) V s a n ha.le hn
    (by change s < 2^(publicationGeometryWidth t band); have h := publicationGeometryWidth_fits t band; nlinarith only [h,hst]) v₀ S₀
    (by simpa [S₀] using hs) (by simpa [S₀] using haSrc) (by simpa [S₀] using hnSrc) (by simp [S₀])
    (by intro k hk
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₀] using hfresh _ (by simp))
    (by intro k hk; simpa [S₀,show k ≠ 115 by intro h; subst k; norm_num at hk] using hlow k (by omega))
  let S₁ : Stacks 154 A := {S₀ with R := (Function.update (Function.update (Function.update (Function.update
    (Function.update S₀.R 141 []) 142 []) 144 (List.replicate a tick))
      145 (List.replicate (a+min n (s-a)) tick)) 146 (List.replicate (n-min n (s-a)) tick))}
  have hoff (k : Fin 154) (hk : k.val < 77) : S₁.R k = [] := by
    have h141 : k ≠ 141 := by intro h; subst k; norm_num at hk
    have h142 : k ≠ 142 := by intro h; subst k; norm_num at hk
    have h144 : k ≠ 144 := by intro h; subst k; norm_num at hk
    have h145 : k ≠ 145 := by intro h; subst k; norm_num at hk
    have h146 : k ≠ 146 := by intro h; subst k; norm_num at hk
    have h115 : k ≠ 115 := by intro h; subst k; norm_num at hk
    simpa [S₁,S₀,h141,h142,h144,h145,h146,h115] using hlow k hk
  obtain ⟨v₂,m₂,hv₂,hm₂,he₂⟩ := countedCyclicBoundaryOrder_exec (body := body)
    (V := V) (s := s) (t := t) (band := band) (a := a) (n := n) hst ha hn hband
    (by dsimp [V,publicationGeometryWidth]; omega) (publicationGeometryWidth_fits t band) v₁ S₁
    (by simpa [S₁,S₀] using hs) (by simpa [S₁,S₀] using ht) (by simpa [S₁,S₀] using hb)
    (by simp [S₁]) (by simp [S₁]) (by simp [S₁]) (by simpa [S₁,S₀] using hfresh 138 (by simp))
    (by simp [S₁,S₀]) (by simpa [S₁,S₀] using hfresh 106 (by simp)) (by simpa [S₁,S₀] using hfresh 108 (by simp))
    (by simpa [S₁,S₀] using hfresh 109 (by simp)) (by simpa [S₁,S₀] using hfresh 116 (by simp))
    (by intro k hk; exact hoff k (by omega))
  let S₂ : Stacks 154 A := {S₁ with R := (Function.update (Function.update S₁.R 109
    (cstream A V (cyclicBoundaryIndexWords s t band a n))) 116 (List.replicate N tick))}
  obtain ⟨vi,m₃,hvi,hm₃,hei⟩ := closedCyclicPageFold_exec (body := fun e : Empty => nomatch e)
    hst band a n V ha hn (embDn tableFoldReg v₂) (embStk tableFoldReg S₂)
    (by simp [S₂,embStk,tableFoldReg]) (by simp [S₂,S₁,S₀,embStk,tableFoldReg])
    (by simp [S₂,embStk,tableFoldReg,N])
    (by intro k hk
        have hk109 : tableFoldReg k ≠ 109 := by intro h; have hv := congrArg Fin.val h; change k.val = 109 at hv; omega
        have hk116 : tableFoldReg k ≠ 116 := by intro h; have hv := congrArg Fin.val h; change k.val = 116 at hv; omega
        simpa [S₂,embStk,hk109,hk116] using hoff (tableFoldReg k) hk)
    (by intro k; exact hleft _)
  obtain ⟨v₃,_,hv₃,he₃⟩ := exec_emb_ovr (e := tableFoldReg) (ι := Empty.elim) (body' := body)
    tableFoldReg_injective (fun e => nomatch e) hei v₂ rfl S₂ rfl
  have he₃' : Exec body (embProg tableFoldReg Empty.elim (closedCyclicPageFold (P := Empty)))
      (mk v₂ S₂) m₃ (mk v₃ {S₂ with R := Function.update S₂.R 109 output}) := by
    convert he₃ using 1
    apply congrArg (mk v₃)
    rw [embOvr_updR tableFoldReg_injective (embStk tableFoldReg S₂) S₂ 109 _,embOvr_stk]
    rfl
  have hm₁' : m₁ ≤ retainedCyclicEndpointsCost S.R V a n := by
    simpa [S₀,retainedCyclicEndpointsCost,cyclicSplitRulersCost,binaryHeaderQueueCost] using hm₁
  refine ⟨v₃,m₀+(m₁+(m₂+m₃)),hv₃.trans (hvi.trans (hv₂.trans (hv₁.trans hv₀))),
    Nat.add_le_add hm₀ (Nat.add_le_add hm₁' (Nat.add_le_add hm₂ hm₃)),
    (Exec.seq he₀ (Exec.seq he₁ (Exec.seq he₂ he₃'))).cast rfl ?_⟩
  apply congrArg (mk v₃)
  ext1
  · rfl
  · rfl
  · rfl
  · funext k
    by_cases h109 : k = 109 <;> by_cases h115 : k = 115 <;> by_cases h116 : k = 116 <;>
      simp [S₂,S₁,S₀,h109,h115,h116,N,V,output,Function.update_apply]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
