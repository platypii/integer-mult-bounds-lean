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

end ScalarPlacement
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
