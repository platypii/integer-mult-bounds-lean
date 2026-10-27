module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryAdvanceLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationSchedule

/-! Generate complete delimited advances from a retained ascending coordinate page. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

def generateBoundaryAdvances : Pr P 224 Q A U :=
  .seq (ucopy 116 9 3) (.seq (countedLoop 116 boundaryAdvanceNext)
    (.seq (uclear 0) (.seq (.act (.push (.rt 206) (fun _ => blank) .done))
      (.seq (moveR 8 206 id) (moveR 9 116 id)))))

def generateBoundaryAdvancesCost (N V w bound : ℕ) : ℕ :=
  N*(bound*(10*w+29)+23*V+54)+2*bound*(w+1)+13

theorem generateBoundaryAdvances_exec (hA : 4 ≤ A) (V w bound : ℕ) (origins : List ℕ)
    (hsorted : (0::origins).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ origins, x ≤ bound ∧ x < 2^V)
    (tail : List (Fin (A+4))) (v : HS 224 Q A U) (S : Stacks 224 A)
    (hcount : S.R 116 = List.replicate origins.length tick)
    (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hsrc : S.R 109 = origins.flatMap (fun x => tblPairs A V x 0)++tail)
    (hclean : ∀ i ∈ ([0,1,2,3,4,5,6,7,8,9] : List (Fin 224)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ generateBoundaryAdvancesCost origins.length V w bound ∧
      Exec body generateBoundaryAdvances (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 109 tail) 206
          (gatherControls A (originAdvances w 0 origins++[0])++S.R 206))}) := by
  let N := origins.length
  let controls := gatherControls A (originAdvances w 0 origins)
  let last := origins.getLastD 0
  obtain ⟨v₁,hu₁,he₁⟩ := ucopy_exec (body := body) (a := 116) (b := 9) (t := 3)
    (by decide) (by decide) (by decide) v S (hclean 3 (by simp))
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 9 (List.replicate N tick)}
  have he₁' : Exec body (ucopy 116 9 3) (mk v S) (4*N+4) (mk v₁ S₁) := by
    simpa [S₁,N,hcount,hclean 9 (by simp)] using he₁
  have hz : ∀ i ∈ ([1,2,3,4,5,6,7] : List (Fin 224)), S₁.R i = [] := by
    intro i hi
    have hi9 : i ≠ 9 := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
      rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
    simpa [S₁,hi9] using hclean i (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hi ⊢; tauto)
  have hpeek := Exec.act (body := body) (peekR 116) (mk v₁ S₁)
  rw [peekR_run] at hpeek
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := boundaryAdvanceLoop_exec (body := body) hA V w bound origins 0
    (List.replicate N tick) tail hsorted hbound {v₁ with flag := (S₁.R 116).head?.isSome} S₁
    (by simpa [S₁,N] using hcount) (by simp [N])
    (by simpa [S₁] using hclean 0 (by simp)) (by simpa [S₁] using hV)
    (by simpa [S₁] using hw) (by simpa [S₁] using hsrc) hz (by simp [S₁,hcount,N])
  let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update (Function.update (Function.update S₁.R
    116 []) 109 tail) 0 (List.replicate last tick)) 8 controls.reverse)}
  have he₂' : Exec body (countedLoop 116 boundaryAdvanceNext) (mk v₁ S₁) (1+n₂) (mk v₂ S₂) := by
    simpa [countedLoop,S₂,controls,last,S₁,hclean 8 (by simp)] using Exec.seq hpeek he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 0 v₂ S₂
  let S₃ : Stacks 224 A := {S₂ with R := Function.update S₂.R 0 []}
  have he₃' : Exec body (uclear 0) (mk v₂ S₂) (2*last+2) (mk v₃ S₃) := by simpa [S₃,S₂] using he₃
  let S₄ : Stacks 224 A := {S₃ with R := Function.update S₃.R 206 (blank::S.R 206)}
  have he₄ : Exec body (.act (.push (.rt 206) (fun _ => blank) .done)) (mk v₃ S₃) 1 (mk v₃ S₄) := by
    simpa [S₄,S₃,S₂,S₁,Action.run,update_rt] using
      Exec.act (body := body) (.push (.rt 206) (fun _ => blank) .done) (mk v₃ S₃)
  obtain ⟨v₅,hu₅,he₅⟩ := moveR_exec body 8 206 (by decide) id v₃ S₄
  let S₅ : Stacks 224 A := {S₄ with R := (Function.update (Function.update S₄.R 8 []) 206
    (controls++blank::S.R 206))}
  have he₅' : Exec body (moveR 8 206 id) (mk v₃ S₄) (2*controls.length+2) (mk v₅ S₅) := by
    simpa [S₅,S₄,S₃,S₂,movedR] using he₅
  obtain ⟨v₆,hu₆,he₆⟩ := moveR_exec body 9 116 (by decide) id v₅ S₅
  have he₆' : Exec body (moveR 9 116 id) (mk v₅ S₅) (2*N+2)
      (mk v₆ {S₅ with R := Function.update (Function.update S₅.R 9 []) 116 (List.replicate N tick)}) := by
    simpa [S₅,S₄,S₃,S₂,S₁,movedR] using he₆
  have hl : last ≤ bound := by
    have hm := List.getLastD_mem_cons (l := origins) (a := 0)
    simp only [List.mem_cons] at hm
    rcases hm with hm | hm
    · change origins.getLastD 0 ≤ bound
      rw [hm]
      exact Nat.zero_le bound
    · exact (hbound _ hm).1
  have hv : (originAdvances w 0 origins).sum ≤ bound*w := by
    simpa using originAdvances_sum_le w 0 bound origins hsorted (Nat.zero_le _) (fun x hx => (hbound x hx).1)
  have hc : controls.length ≤ bound*w+N := by simp only [controls,length_gatherControls,originAdvances_length]; omega
  refine ⟨v₆,(4*N+4)+((1+n₂)+((2*last+2)+(1+((2*controls.length+2)+(2*N+2))))),
    hu₆.trans (hu₅.trans (hu₃.trans (hu₂.trans hu₁))),?_,
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄ (Exec.seq he₅' he₆'))))).cast rfl ?_⟩
  · dsimp only [generateBoundaryAdvancesCost,N]
    dsimp only [N] at hc
    nlinarith only [hn₂,hl,hc]
  · apply congrArg (mk v₆)
    rw [gatherControls_append]
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h0 : i = 0 <;> by_cases h8 : i = 8 <;> by_cases h9 : i = 9 <;>
      by_cases h109 : i = 109 <;> by_cases h116 : i = 116 <;> by_cases h206 : i = 206 <;>
      simp [S₅,S₄,S₃,S₂,S₁,controls,gatherControls,N,h0,h8,h9,h109,h116,h206,
        hcount,hclean 0 (by simp),hclean 8 (by simp),hclean 9 (by simp),List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
