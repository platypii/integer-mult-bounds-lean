module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Host.EmitRun

/-! Consume a runtime binary count packet and append its run to the reversed mask buffer. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def emitRunPacket (symbol : Fin (A+4)) : Pr P 117 Q A U :=
  .seq (takePrefix 115 109 20 25 26)
    (.seq (emitRun 20 21 22 25 26 27 symbol) (uclear 20))

theorem emitRunPacket_exec (W n : ℕ) (hn : n < 2^W) (symbol : Fin (A+4))
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hW : (S.R 115).length = W) (hsrc : S.R 109 = binSyms W n++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,25,26,27], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 8*n+19*W+16 ∧
      Exec body (emitRunPacket symbol) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 109 tail) 22
          (List.replicate n symbol++S.R 22))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (show [(115 : Fin 117),109,20,25,26].Nodup by decide) v S (binSyms W n) tail hsrc
    (by simpa using hW) (hfresh 25 (by simp)) (hfresh 26 (by simp))
  let S₁ : Stacks 117 A := {S with R := Function.update (Function.update S.R 109 tail) 20 (binSyms W n)}
  have he₁' : Exec body (takePrefix 115 109 20 25 26) (mk v S) (6*W+6) (mk v₁ S₁) := by
    simpa [S₁,hfresh 20 (by simp)] using he₁
  obtain ⟨v₂,steps,hu₂,hs,he₂⟩ := emitRun_exec (body := body)
    (show [(20 : Fin 117),21,22,25,26,27].Nodup by decide) W n hn symbol v₁ S₁
    (by simp [S₁]) (by
      intro k hk
      have hk20 : k ≠ (20 : Fin 117) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide
      have hk109 : k ≠ (109 : Fin 117) := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl <;> decide
      simp [S₁,hk20,hk109,hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)])
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 22 (List.replicate n symbol++S₁.R 22)}
  have he₂' : Exec body (emitRun 20 21 22 25 26 27 symbol) (mk v₁ S₁) steps (mk v₂ S₂) := he₂
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec (body := body) 20 v₂ S₂
  refine ⟨v₃,(6*W+6)+(steps+(2*W+2)),hu₃.trans (hu₂.trans hu₁),by omega,
    (Exec.seq he₁' (Exec.seq he₂' he₃)).cast ?_ ?_⟩
  · simp [S₂,S₁]
  · apply congrArg (mk v₃)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₂,S₁,Function.update_apply]
    split_ifs <;> simp_all

/-- The run symbol is read from the physical symbol saved by `eachSym`. -/
def emitFlagRunPacket (off on : Fin (A+4)) : Pr P 117 Q A U :=
  .cond (fun v => v.sym == some (bitSymbol true)) (emitRunPacket on) (emitRunPacket off)

theorem emitFlagRunPacket_exec (W n : ℕ) (hn : n < 2^W) (flag : Bool)
    (off on : Fin (A+4)) (v : HS 117 Q A U) (S : Stacks 117 A)
    (tail : List (Fin (A+4))) (hflag : v.sym = some (bitSymbol flag))
    (hW : (S.R 115).length = W) (hsrc : S.R 109 = binSyms W n++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,25,26,27], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ 8*n+19*W+17 ∧
      Exec body (emitFlagRunPacket off on) (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update S.R 109 tail) 22
          (List.replicate n (if flag then on else off)++S.R 22))}) := by
  obtain ⟨v',steps,hu,hs,he⟩ := emitRunPacket_exec (body := body) W n hn
    (if flag then on else off) v S tail hW hsrc hfresh
  refine ⟨v',steps+1,hu,by omega,?_⟩
  cases flag with
  | false => exact Exec.cond_false (by simp [hflag,bitSymbol]) he
  | true => exact Exec.cond_true (by simp [hflag]) he

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
