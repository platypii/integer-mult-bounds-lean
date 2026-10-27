module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakeNaturalCoordinate
public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSetupOps

/-! Emit a reversed advance packet from one decoded ascending coordinate. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Fast.TableVM

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def boundaryAdvancePacket : Pr P 224 Q A U :=
  .seq (ucopy 1 6 3) (.seq (usub 0 1 3) (.seq (unaryProduct 1 160 7 3 4)
    (.seq (copyR 7 8 3 id) (.seq (.act (.push (.rt 8) (fun _ => blank) .done))
      (.seq (uclear 7) (.seq (uclear 1) (.seq (uclear 0) (moveR 6 0 id))))))))

theorem boundaryAdvancePacket_exec (previous x w : ℕ) (horder : previous ≤ x)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hprev : S.R 0 = List.replicate previous tick) (hx : S.R 1 = List.replicate x tick)
    (hw : (S.R 160).length = w)
    (hclean : ∀ i ∈ ([3,4,6,7] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ x*(10*w+23)+25 ∧
      Exec body boundaryAdvancePacket (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          0 (List.replicate x tick)) 1 []) 8
          (blank::(List.replicate ((x-previous)*w) tick++S.R 8)))}) := by
  let d := x-previous
  let bytes := d*w
  have hsplit : previous+d = x := by dsimp [d]; omega
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 1) (b := 6) (t := 3)
    (by decide) (by decide) (by decide) v S (hclean 3 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 6 (List.replicate x tick)}
  have he₁' : Exec body (ucopy 1 6 3) (mk v S) (4*x+4) (mk v₁ S₁) := by
    simpa [S₁,hx,hclean 6 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := usub_exec (body := body) (a := 0) (b := 1) (t := 3)
    (by decide) (by decide) (by decide) v₁ S₁ (by simpa [S₁] using hclean 3 (by simp))
  let S₂ : Stacks 224 A := {S₁ with R := Function.update S₁.R 1 (List.replicate d tick)}
  have he₂' : Exec body (usub 0 1 3) (mk v₁ S₁) (4*previous+4) (mk v₂ S₂) := by
    simpa [S₂,S₁,hprev,hx,d] using he₂
  obtain ⟨v₃,n₃,hu₃,hn₃,he₃⟩ := unaryProduct_exec (body := body)
    (a := 1) (b := 160) (dst := 7) (t₁ := 3) (t₂ := 4) (by decide) v₂ S₂
    (by simpa [S₂,S₁] using hclean 3 (by simp)) (by simpa [S₂,S₁] using hclean 4 (by simp))
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 7 (List.replicate bytes tick)}
  have he₃' : Exec body (unaryProduct 1 160 7 3 4) (mk v₂ S₂) n₃ (mk v₃ S₃) := by
    simpa [S₃,S₂,S₁,bytes,hw,hclean 7 (by simp)] using he₃
  have hn₃' : n₃ ≤ d*(4*w+9)+4 := by simpa [S₂,S₁,hw] using hn₃
  obtain ⟨v₄,hu₄,he₄⟩ := copyR_exec body 7 8 3 (by decide) (by decide) (by decide) id v₃ S₃
    (by simpa [S₃,S₂,S₁] using hclean 3 (by simp))
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 8 (List.replicate bytes tick++S.R 8)}
  have he₄' : Exec body (copyR 7 8 3 id) (mk v₃ S₃) (4*bytes+4) (mk v₄ S₄) := by
    simpa [S₄,S₃,S₂,S₁] using he₄
  let S₅ : Stacks 224 A := {S₄ with R := Function.update S₄.R 8 (blank::S₄.R 8)}
  have he₅ : Exec body (.act (.push (.rt 8) (fun _ => blank) .done)) (mk v₄ S₄) 1 (mk v₄ S₅) := by
    simpa [S₅,Action.run,update_rt] using Exec.act (body := body) (.push (.rt 8) (fun _ => blank) .done) (mk v₄ S₄)
  obtain ⟨v₆,hu₆,he₆⟩ := uclear_exec body 7 v₄ S₅
  let S₆ : Stacks 224 A := {S₅ with R := Function.update S₅.R 7 []}
  have he₆' : Exec body (uclear 7) (mk v₄ S₅) (2*bytes+2) (mk v₆ S₆) := by simpa [S₆,S₅,S₄,S₃] using he₆
  obtain ⟨v₇,hu₇,he₇⟩ := uclear_exec body 1 v₆ S₆
  let S₇ : Stacks 224 A := {S₆ with R := Function.update S₆.R 1 []}
  have he₇' : Exec body (uclear 1) (mk v₆ S₆) (2*d+2) (mk v₇ S₇) := by simpa [S₇,S₆,S₅,S₄,S₃,S₂] using he₇
  obtain ⟨v₈,hu₈,he₈⟩ := uclear_exec body 0 v₇ S₇
  let S₈ : Stacks 224 A := {S₇ with R := Function.update S₇.R 0 []}
  have he₈' : Exec body (uclear 0) (mk v₇ S₇) (2*previous+2) (mk v₈ S₈) := by
    simpa [S₈,S₇,S₆,S₅,S₄,S₃,S₂,S₁,hprev] using he₈
  obtain ⟨v₉,hu₉,he₉⟩ := moveR_exec body 6 0 (by decide) id v₈ S₈
  have he₉' : Exec body (moveR 6 0 id) (mk v₈ S₈) (2*x+2)
      (mk v₉ {S₈ with R := Function.update (Function.update S₈.R 6 []) 0 (List.replicate x tick)}) := by
    simpa [S₈,S₇,S₆,S₅,S₄,S₃,S₂,S₁,movedR] using he₉
  refine ⟨v₉,(4*x+4)+((4*previous+4)+(n₃+((4*bytes+4)+(1+((2*bytes+2)+((2*d+2)+((2*previous+2)+(2*x+2)))))))),
    hu₉.trans (hu₈.trans (hu₇.trans (hu₆.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁)))))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' (Exec.seq he₅
      (Exec.seq he₆' (Exec.seq he₇' (Exec.seq he₈' he₉')))))))).cast rfl ?_⟩
  · have hd : d*w ≤ x*w := Nat.mul_le_mul_right w (Nat.sub_le x previous)
    dsimp only [bytes]
    nlinarith only [hn₃',hd,hsplit,horder]
  · apply congrArg (mk v₉)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hi6 : i = 6 <;>
      by_cases hi7 : i = 7 <;> by_cases hi8 : i = 8 <;>
      simp [S₈,S₇,S₆,S₅,S₄,S₃,S₂,S₁,d,bytes,hi0,hi1,hi6,hi7,hi8,hclean 6 (by simp),hclean 7 (by simp)]

/-- Read one real coordinate word and emit its scaled advance packet. -/
def boundaryAdvanceNext : Pr P 224 Q A U :=
  .seq (takeNaturalCoordinate 115 109 1 2 3 4 5) boundaryAdvancePacket

theorem boundaryAdvanceNext_exec (hA : 4 ≤ A) (previous x V w : ℕ)
    (horder : previous ≤ x) (hxV : x < 2^V) (tail : List (Fin (A+4)))
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hprev : S.R 0 = List.replicate previous tick)
    (hwidth : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hsrc : S.R 109 = tblPairs A V x 0++tail)
    (hclean : ∀ i ∈ ([1,2,3,4,5,6,7] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ x*(10*w+29)+23*V+43 ∧
      Exec body boundaryAdvanceNext (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          109 tail) 0 (List.replicate x tick)) 8
          (blank::(List.replicate ((x-previous)*w) tick++S.R 8)))}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := takeNaturalCoordinate_exec (body := body)
    (width := 115) (src := 109) (dst := 1) (word := 2) (work := 3) (saved := 4) (tmp := 5)
    (by decide) hA V x hxV tail v S hwidth hsrc (fun i hi => hclean i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto))
  let S₁ : Stacks 224 A := {S with R := Function.update (Function.update S.R 109 tail) 1 (List.replicate x tick)}
  have he₁' : Exec body (takeNaturalCoordinate 115 109 1 2 3 4 5) (mk v S) n₁ (mk v₁ S₁) := by
    simpa [S₁,hclean 1 (by simp)] using he₁
  have hz : ∀ i ∈ ([3,4,6,7] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have ho : i ≠ 109 ∧ i ≠ 1 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,ho.1,ho.2] using hclean i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryAdvancePacket_exec (body := body) previous x w horder v₁ S₁
    (by simpa [S₁] using hprev) (by simp [S₁]) (by simpa [S₁] using hw) hz
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,by nlinarith only [hn₁,hn₂],(Exec.seq he₁' he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hi8 : i = 8 <;>
    by_cases hi109 : i = 109 <;> simp [S₁,hi0,hi1,hi8,hi109,hclean 1 (by simp)]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
