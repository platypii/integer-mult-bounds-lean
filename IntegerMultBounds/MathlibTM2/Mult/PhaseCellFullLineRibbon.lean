module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPadCouplingSource
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCouplingRibbonMask
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedFinishCouplingCoefficientInterval
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetainedCouplingReady

/-! Generate the full-system gathered ribbon directly from the current iterate. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

theorem rawCouplingRibbon_fullLine {s : ℕ} [NeZero s] (band : ℕ)
    (F : ZMod s → GaussianInt) :
    rawCouplingRibbon band 0 s F = cyclicPaddedLine F band := by
  simp only [rawCouplingRibbon,List.drop_zero]
  apply List.take_of_length_le
  simp only [cyclicPaddedLine,List.length_map,List.length_range]
  omega

namespace ScalarPlacement
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 144 Q A U}

theorem padCouplingSource_fullRibbon_exec {s : ℕ} [NeZero s] (F : ZMod s → GaussianInt)
    (band w : ℕ) (hb : band ≤ s) (tail : List (Fin (A+4)))
    (v : HS 144 Q A U) (S : Stacks 144 A)
    (hs : (S.R 97).length = s) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = cstream A w (chirpLine s F)++tail)
    (h107 : S.R 107 = []) (h108 : S.R 108 = []) (h109 : S.R 109 = [])
    (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ padCouplingSourceCost s band w ∧
      Exec body padCouplingSource (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (rawCouplingRibbon band 0 s F)++tail)}) := by
  simpa only [rawCouplingRibbon_fullLine] using
    padCouplingSource_exec (body := body) F band w hb tail v S hs hband hw hsrc
      h107 h108 h109 h115 h116 h104 h105 h106

set_option autoImplicit false in
theorem padCouplingSource_fullRibbon168_exec {s Q A : ℕ} {P U : Type}
    {body : P → Pr P 168 Q A U} [NeZero s] (F : ZMod s → GaussianInt)
    (band w : ℕ) (hb : band ≤ s) (tail : List (Fin (A+4)))
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hs : (S.R 97).length = s) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = cstream A w (chirpLine s F)++tail)
    (h107 : S.R 107 = []) (h108 : S.R 108 = []) (h109 : S.R 109 = [])
    (h115 : S.R 115 = []) (h116 : S.R 116 = [])
    (h104 : S.R 104 = []) (h105 : S.R 105 = []) (h106 : S.R 106 = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ padCouplingSourceCost s band w ∧
      Exec body (embProg (Fin.castLE (by decide : 144 ≤ 168)) Empty.elim
        (padCouplingSource (P := Empty))) (mk v S) m
        (mk v' {S with R := Function.update S.R 141 (cstream A w (rawCouplingRibbon band 0 s F)++tail)}) := by
  let e : Fin 144 → Fin 168 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by intro i j h; apply Fin.ext; exact congrArg (fun k : Fin 168 => k.val) h
  obtain ⟨vi,n,hu,hn,he⟩ := padCouplingSource_fullRibbon_exec
    (body := fun f : Empty => nomatch f) F band w hb tail (embDn e v) (embStk e S)
    hs hband hw hsrc h107 h108 h109 h115 h116 h104 h105 h106
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    hinj (fun f => nomatch f) he v rfl S rfl
  refine ⟨v',n,hu'.trans hu,hn,?_⟩
  have hf : embOvr e ({embStk e S with R := (Function.update (embStk e S).R 141
      (cstream A w (rawCouplingRibbon band 0 s F)++tail))} : Stacks 144 A).get S =
      {S with R := Function.update S.R 141 (cstream A w (rawCouplingRibbon band 0 s F)++tail)} := by
    rw [embOvr_updR hinj,embOvr_stk]
    rfl
  rw [hf] at he'
  exact he'

/-- Two transfers preserve ribbon order while freeing the masked-output port. -/
theorem moveFullLineRibbon_exec {Q A s precision q t u a b : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P 168 Q A U} (F : ZMod s → GaussianInt) (band w : ℕ)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hsrc : S.R 141 = cstream A w (cyclicPaddedLine F band))
    (htmp : S.R 107 = []) (hdst : S.R 160 = [])
    (raw : List (Fin (A+4)))
    (hready : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg S))) :
    ∃ v', v'.user = v.user ∧
      Exec body (.seq (moveR 141 107 id) (moveR 107 160 id)) (mk v S) (4*((s+2*band)*w)+4)
        (mk v' {S with R := (Function.update (Function.update S.R 141 [])
          160 (cstream A w (rawCouplingRibbon band 0 s F)))}) ∧
      RetainedCouplingReady precision q w s t u band a b raw
        (embStk groupReg (embStk intervalPageReg
          {S with R := (Function.update (Function.update S.R 141 [])
            160 (cstream A w (rawCouplingRibbon band 0 s F)))})) := by
  obtain ⟨v₁,hu₁,he₁⟩ := moveR_exec body 141 107 (by decide) id v S
  let B : Stacks 168 A := {S with R := movedR S.R 141 107 id (S.R 141)}
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 107 160 (by decide) id v₁ B
  have he := Exec.seq he₁ he₂
  refine ⟨v₂,hu₂.trans hu₁,?_,?_⟩
  · have hn : 2*(S.R 141).length+2+(2*(B.R 107).length+2) = 4*((s+2*band)*w)+4 := by
      simp [B,movedR,hsrc,htmp,length_cstream,cyclicPaddedLine]
      omega
    refine he.cast hn ?_
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [B,movedR,Function.update_apply,List.map_id]
    split_ifs <;> subst_vars <;> simp_all [hsrc,rawCouplingRibbon_fullLine]
  · have hproj : embStk groupReg (embStk intervalPageReg
        {S with R := (Function.update (Function.update S.R 141 [])
          160 (cstream A w (rawCouplingRibbon band 0 s F)))}) =
        embStk groupReg (embStk intervalPageReg S) := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have hk := k.isLt
      simp [embStk,groupReg,intervalPageReg,Function.update_apply,Fin.ext_iff,
        show k.val ≠ 141 by omega,show k.val ≠ 160 by omega]
    rw [hproj]
    exact hready

/-- Prepare the periodic source for the gathered coupling executor. -/
def prepareFullLineRibbon {Q A : ℕ} {P U : Type} : Pr P 168 Q A U :=
  .seq (embProg (Fin.castLE (by decide : 144 ≤ 168)) Empty.elim (padCouplingSource (P := Empty)))
    (.seq (moveR 141 107 id) (moveR 107 160 id))

theorem prepareFullLineRibbon_exec {Q A s precision q t u a b : ℕ} [NeZero s] {P U : Type}
    {body : P → Pr P 168 Q A U} (F : ZMod s → GaussianInt) (band w : ℕ) (hb : band ≤ s)
    (v : HS 168 Q A U) (S : Stacks 168 A)
    (hs : (S.R 97).length = s) (hband : (S.R 100).length = band) (hw : (S.R 94).length = w)
    (hsrc : S.R 141 = cstream A w (chirpLine s F))
    (hclean : ∀ k ∈ ([107,108,109,115,116,104,105,106,160] : List (Fin 168)), S.R k = [])
    (raw : List (Fin (A+4)))
    (hready : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg S))) :
    ∃ v' n, v'.user = v.user ∧ n ≤ padCouplingSourceCost s band w+4*((s+2*band)*w)+4 ∧
      Exec body prepareFullLineRibbon (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 141 [])
          160 (cstream A w (rawCouplingRibbon band 0 s F)))}) := by
  obtain ⟨v₁,n,hu₁,hn,he₁⟩ := padCouplingSource_fullRibbon168_exec (body := body) F band w hb [] v S
    hs hband hw (by simpa using hsrc) (hclean 107 (by simp)) (hclean 108 (by simp))
    (hclean 109 (by simp)) (hclean 115 (by simp)) (hclean 116 (by simp))
    (hclean 104 (by simp)) (hclean 105 (by simp)) (hclean 106 (by simp))
  let B : Stacks 168 A := {S with R := Function.update S.R 141 (cstream A w (rawCouplingRibbon band 0 s F))}
  have hreadyB : RetainedCouplingReady precision q w s t u band a b raw
      (embStk groupReg (embStk intervalPageReg B)) := by
    have heq : embStk groupReg (embStk intervalPageReg B) = embStk groupReg (embStk intervalPageReg S) := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      have hk := k.isLt
      simp [B,embStk,groupReg,intervalPageReg,Fin.ext_iff,show k.val ≠ 141 by omega]
    rw [heq]
    exact hready
  obtain ⟨v₂,hu₂,he₂,_⟩ := moveFullLineRibbon_exec (body := body) F band w v₁ B
    (by simp [B,rawCouplingRibbon_fullLine]) (by simpa [B] using hclean 107 (by simp))
    (by simpa [B] using hclean 160 (by simp)) raw hreadyB
  refine ⟨v₂,n+(4*((s+2*band)*w)+4),hu₂.trans hu₁,by omega,?_⟩
  have he₁' : Exec body (embProg (Fin.castLE (by decide : 144 ≤ 168)) Empty.elim
      (padCouplingSource (P := Empty))) (mk v S) n (mk v₁ B) := by simpa [B] using he₁
  simpa only [prepareFullLineRibbon,B,Function.update_idem] using Exec.seq he₁' he₂

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
