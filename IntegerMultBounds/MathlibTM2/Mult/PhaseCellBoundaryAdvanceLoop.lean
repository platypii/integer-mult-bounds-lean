module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryAdvancePacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCountedLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAdvanceSchedule

/-! Structural runtime loop over ascending encoded boundary coordinates. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

theorem boundaryAdvanceLoop_exec (hA : 4 ≤ A) (V w bound : ℕ)
    (origins : List ℕ) (previous : ℕ) (clock tail : List (Fin (A+4)))
    (hsorted : (previous::origins).Pairwise (· ≤ ·))
    (hbound : ∀ x ∈ origins, x ≤ bound ∧ x < 2^V)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hcount : S.R 116 = clock) (hlen : clock.length = origins.length)
    (hprev : S.R 0 = List.replicate previous tick)
    (hV : (S.R 115).length = V) (hw : (S.R 160).length = w)
    (hsrc : S.R 109 = origins.flatMap (fun x => tblPairs A V x 0)++tail)
    (hclean : ∀ i ∈ ([1,2,3,4,5,6,7] : List (Fin 224)), S.R i = [])
    (hflag : v.flag = clock.head?.isSome) :
    ∃ v' n, v'.user = v.user ∧ n ≤ origins.length*(bound*(10*w+29)+23*V+46)+1 ∧
      Exec body (.loop (·.flag) (countedLoopBody 116 boundaryAdvanceNext)) (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update (Function.update S.R
          116 []) 109 tail) 0 (List.replicate (origins.getLastD previous) tick)) 8
          ((gatherControls A (originAdvances w previous origins)).reverse++S.R 8))}) := by
  induction origins generalizing previous clock v S with
  | nil =>
    have hc : clock = [] := List.eq_nil_of_length_eq_zero (by simpa using hlen)
    have he : Exec body (.loop (·.flag) (countedLoopBody 116 boundaryAdvanceNext)) (mk v S) 1 (mk v S) :=
      Exec.loop_false (by simpa [hc] using hflag)
    refine ⟨v,1,rfl,by simp,he.cast rfl ?_⟩
    apply congrArg (mk v)
    refine Stacks.ext rfl rfl rfl ?_
    funext i
    by_cases h116 : i = 116 <;> by_cases h109 : i = 109 <;> by_cases h0 : i = 0 <;>
      by_cases h8 : i = 8 <;> simp [h116,h109,h0,h8,hcount,hc,hsrc,hprev,originAdvances,gatherControls]
  | cons x origins ih =>
    cases clock with
    | nil => simp at hlen
    | cons c clock =>
      have horder : previous ≤ x := (List.pairwise_cons.mp hsorted).1 x (by simp)
      have hsorted' : (x::origins).Pairwise (· ≤ ·) := (List.pairwise_cons.mp hsorted).2
      have hx := hbound x (by simp)
      let S₁ : Stacks 224 A := {S with R := Function.update S.R 116 clock}
      have hpop : Exec body (.act (.pop (.rt 116) (fun v _ => v) .done)) (mk v S) 1 (mk v S₁) := by
        simpa [S₁,Action.run,hcount,update_rt] using
          Exec.act (body := body) (.pop (.rt 116) (fun v _ => v) .done) (mk v S)
      obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := boundaryAdvanceNext_exec (body := body) hA previous x V w horder hx.2
        (origins.flatMap (fun x => tblPairs A V x 0)++tail) v S₁
        (by simpa [S₁] using hprev) (by simpa [S₁] using hV) (by simpa [S₁] using hw)
        (by simpa [S₁,List.flatMap_cons,List.append_assoc] using hsrc) (by
          intro i hi
          have hi116 : i ≠ 116 := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          simpa [S₁,hi116] using hclean i hi)
      let S₂ : Stacks 224 A := {S₁ with R := (Function.update (Function.update (Function.update S₁.R
        109 (origins.flatMap (fun x => tblPairs A V x 0)++tail)) 0 (List.replicate x tick)) 8
        (blank::(List.replicate ((x-previous)*w) tick++S₁.R 8)))}
      have hn₁' : n₁ ≤ bound*(10*w+29)+23*V+43 := hn₁.trans (by gcongr; exact hx.1)
      have hpeek := Exec.act (body := body) (peekR 116) (mk v₁ S₂)
      rw [peekR_run] at hpeek
      obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩  := ih x clock hsorted'
        (fun y hy => hbound y (by simp [hy])) {v₁ with flag := (S₂.R 116).head?.isSome} S₂
        (by simp [S₂,S₁]) (by simpa using hlen) (by simp [S₂])
        (by simpa [S₂,S₁] using hV) (by simpa [S₂,S₁] using hw) (by simp [S₂]) (by
          intro i hi
          have ho : i ≠ 116 ∧ i ≠ 109 ∧ i ≠ 0 ∧ i ≠ 8 := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
            rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          simpa [S₂,S₁,ho.1,ho.2.1,ho.2.2.1,ho.2.2.2] using hclean i hi)
        (by simp [S₂,S₁])
      refine ⟨v₂,1+(n₁+1)+n₂+1,hu₂.trans hu₁,?_,
        (Exec.loop_true (by simpa using hflag) (Exec.seq hpop (Exec.seq he₁ hpeek)) he₂).cast rfl ?_⟩
      · simp only [List.length_cons,Nat.add_mul,Nat.one_mul]
        omega
      · apply congrArg (mk v₂)
        rw [List.getLastD_cons]
        refine Stacks.ext rfl rfl rfl ?_
        funext i
        by_cases h116 : i = 116 <;> by_cases h109 : i = 109 <;> by_cases h0 : i = 0 <;>
          by_cases h8 : i = 8 <;>
          simp [S₂,S₁,h116,h109,h0,h8,originAdvances,gatherControls,List.reverse_append,List.append_assoc]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
