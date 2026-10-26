module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFinishComponents
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPairedPhysicalRead

/-! Final complex accuracy and the released real-solver bank after consuming both results. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem finishComponents_spec {P N q l s t u band : ℕ} [NeZero s] (hA : 4 ≤ A)
    (X Y : ZMod s → GaussianInt) (active : Finset (ZMod s)) (z : ZMod s → ℂ) (eX eY : ℝ)
    (recovery rhs tail savedTail outputTail : List (Fin (A+4)))
    (hr : recovery.length = s*(2*q+8)) (hb : rhs.length = s*(2*q+8))
    (hX : PhaseCellInterface.ErrorOn active
      (fun i => publishedCellRead q (2*q+8) (0 : ZMod s) (cstream A (2*q+8) (chirpLine s X)++savedTail) i)
      (fun i => (z i).re) eX)
    (hY : PhaseCellInterface.ErrorOn active
      (fun i => publishedCellRead q (2*q+8) (0 : ZMod s) (cstream A (2*q+8) (chirpLine s Y)++outputTail) i)
      (fun i => (z i).im) eY)
    (v : HS 148 Q A U) (S : Stacks 148 A)
    (hready : LengthKeyReady P N q l s t u band 0 0 (recovery++(rhs++tail)) (embStk componentReg S))
    (hx : S.R 145 = cstream A (2*q+8) (chirpLine s X)++savedTail)
    (hy : S.R 132 = cstream A (2*q+8) (chirpLine s Y)++outputTail)
    (h146 : S.R 146 = []) (h147 : S.R 147 = []) :
    let Z := cstream A (2*q+8) (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++outputTail
    let S' : Stacks 148 A := {S with R := Function.update (Function.update (Function.update S.R 110 tail) 145 savedTail) 132 Z}
    ∃ v' n, v'.user = v.user ∧ n ≤ finishComponentsCost q s ∧
      Exec (embTab componentReg body) finishComponents (mk v S) n (mk v' S') ∧
      PhaseCellInterface.ErrorOn active (pairedCellRead q (2*q+8) (S'.R 132)) z (eX+eY) ∧
      LengthKeyReady P N q l s t u band 0 0 tail (embStk componentReg S') := by
  dsimp only
  let Z := cstream A (2*q+8) (chirpLine s (fun i => pairComponentWord (X i) (Y i)))++outputTail
  have hq : (S.R 119).length = q := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (119,112) (by simp [groupHeaderCopies])
  have hs : (S.R 121).length = s := by
    simpa [embStk,componentReg,groupHeaderValue] using hready.masters (121,97) (by simp [groupHeaderCopies])
  have hfresh (r : Fin 144) (hr : r ∈ [(131 : Fin 144),134,135,136,137,140]) : S.R (componentReg r) = [] :=
    hready.fresh r hr
  obtain ⟨v',n,hu,hn,he⟩ := finishComponents_exec (body := body) hA q s (chirpLine s X) (chirpLine s Y)
    (by simp [chirpLine]) (by simp [chirpLine]) recovery rhs tail savedTail outputTail hr hb v S hq hs
    (by simpa [embStk,componentReg] using hready.source) hx hy
    (by simpa [embStk,componentReg] using hready.blank 94 (by decide) (by decide) (by decide))
    (by simpa [componentReg] using hfresh 131 (by simp))
    (by simpa [componentReg] using hfresh 134 (by simp))
    (by simpa [componentReg] using hfresh 135 (by simp))
    (by simpa [componentReg] using hfresh 136 (by simp)) h146 h147
  refine ⟨v',n,hu,hn,?_,?_,?_⟩
  · simpa only [pairComponentWords_chirpLine] using he
  · simpa only [Function.update_self] using
      pairedComponents_physical_accuracy hA X Y active z eX eY outputTail savedTail outputTail hX hY
  · have hproject : embStk componentReg {S with R := (Function.update (Function.update (Function.update S.R
        110 tail) 145 savedTail) 132 Z)} =
        {(embStk componentReg S) with R := (Function.update (Function.update (embStk componentReg S).R 110 tail) 132 Z)} := by
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases h110 : k = 110
      · subst k; simp [embStk,componentReg]
      by_cases h132 : k = 132
      · subst k; simp [embStk,componentReg]
      have hne110 : componentReg k ≠ 110 := by
        intro he; apply h110; apply Fin.ext; exact congrArg (fun r : Fin 148 => r.val) he
      have hne132 : componentReg k ≠ 132 := by
        intro he; apply h132; apply Fin.ext; exact congrArg (fun r : Fin 148 => r.val) he
      simp [embStk,Function.comp_def,h110,h132,hne110,hne132,componentReg_off 145 (by decide) k]
    rw [hproject]
    exact (hready.update_source tail).update_output Z

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
