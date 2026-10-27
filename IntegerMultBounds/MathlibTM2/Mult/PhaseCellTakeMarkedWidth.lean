module

public import IntegerMultBounds.MathlibTM2.Node.Params
public import IntegerMultBounds.MathlibTM2.Host.WordTape

/-! Consume a tick prefix and its zero-bit delimiter into a unary width register. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node

variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def markedWidthPeek (src : Fin T) : Act T Q A U :=
  .peek (.rt src) (fun v o => {v with flag := (o.map symBit).getD false}) .done

def markedWidthStep (src dst : Fin T) : Act T Q A U :=
  .pop (.rt src) (fun v _ => v) (.push (.rt dst) (fun _ => tick) (markedWidthPeek src))

def takeMarkedWidth (src dst : Fin T) : Pr P T Q A U :=
  .seq (.act (markedWidthPeek src))
    (.seq (.loop (·.flag) (.act (markedWidthStep src dst)))
      (.act (.pop (.rt src) (fun v _ => v) .done)))

theorem takeMarkedWidth_exec (src dst : Fin T) (hne : src ≠ dst) (W : ℕ)
    (tail : List (Fin (A+4))) (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = List.replicate W tick++bitSymbol false::tail) :
    ∃ v', v'.user = v.user ∧
      Exec body (takeMarkedWidth src dst) (mk v S) (2*W+3)
        (mk v' {S with R := (Function.update (Function.update S.R src tail)
          dst (List.replicate W tick++S.R dst))}) := by
  have hbit (n : ℕ) : (((List.replicate n (tick : Fin (A+4))++bitSymbol false::tail).head?.map symBit).getD false) =
      decide (0 < n) := by
    cases n <;> simp [List.replicate_succ, tick,symBit_bitSymbol]
  have hhead (n : ℕ) : symBit ((List.replicate n (tick : Fin (A+4))).head?.getD (bitSymbol false)) = decide (0 < n) := by
    cases n <;> simp [List.replicate_succ, tick, symBit_bitSymbol]
  have hloop : ∀ n (vi : HS T Q A U) B, B.R src = List.replicate n tick++bitSymbol false::tail →
      vi.flag = decide (0 < n) →
      ∃ vf, vf.user = vi.user ∧
        Exec body (.loop (·.flag) (.act (markedWidthStep src dst))) (mk vi B) (2*n+1)
          (mk vf {B with R := (Function.update (Function.update B.R src (bitSymbol false::tail))
            dst (List.replicate n tick++B.R dst))}) := by
    intro n
    induction n with
    | zero =>
      intro vi B hb hf
      refine ⟨vi,rfl,(Exec.loop_false (by simpa using hf)).cast rfl ?_⟩
      apply congrArg (mk vi)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;> simp_all
    | succ n ih =>
      intro vi B hb hf
      let B₁ : Stacks T A := {B with R := (Function.update (Function.update B.R src
        (List.replicate n tick++bitSymbol false::tail)) dst (tick::B.R dst))}
      have he₁ : Exec body (.act (markedWidthStep src dst)) (mk vi B) 1
          (mk {vi with flag := decide (0 < n)} B₁) := by
        simpa [markedWidthStep,markedWidthPeek,Action.run,update_rt,hb,B₁,hne,hne.symm,hbit,hhead] using
          Exec.act (body := body) (markedWidthStep src dst) (mk vi B)
      obtain ⟨vf,huf,hef⟩ := ih {vi with flag := decide (0 < n)} B₁ (by simp [B₁,hne]) rfl
      refine ⟨vf,huf,(Exec.loop_true (by simpa using hf) he₁ hef).cast (by omega) ?_⟩
      apply congrArg (mk vf)
      refine Stacks.ext rfl rfl rfl ?_
      have hrep : List.replicate n (tick : Fin (A+4))++tick::B.R dst = List.replicate (n+1) tick++B.R dst := by
        rw [List.replicate_succ']
        simp [List.append_assoc]
      funext k
      by_cases hs : k = src <;> by_cases hd : k = dst <;> simp_all only [B₁, Function.update_apply, ite_eq_left, ite_eq_right, hne.symm, not_false_eq_true, List.replicate_succ, List.cons_append]
  have he₀ : Exec body (.act (markedWidthPeek src)) (mk v S) 1
      (mk {v with flag := decide (0 < W)} S) := by
    simpa [markedWidthPeek,Action.run,hsrc, ← List.cons_append, List.replicate_succ, hbit,hhead] using Exec.act (body := body) (markedWidthPeek src) (mk v S)
  obtain ⟨v₁,hu₁,he₁⟩ := hloop W {v with flag := decide (0 < W)} S hsrc rfl
  let S₁ : Stacks T A := {S with R := (Function.update (Function.update S.R src (bitSymbol false::tail))
    dst (List.replicate W tick++S.R dst))}
  have he₂ : Exec body (.act (.pop (.rt src) (fun v _ => v) .done)) (mk v₁ S₁) 1
      (mk v₁ {S₁ with R := Function.update S₁.R src tail}) := by
    simpa [Action.run,update_rt,S₁,hne] using
      Exec.act (body := body) (.pop (.rt src) (fun v _ => v) .done) (mk v₁ S₁)
  refine ⟨v₁,hu₁,(Exec.seq he₀ (Exec.seq he₁ he₂)).cast (by omega) ?_⟩
  apply congrArg (mk v₁)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hs : k = src <;> by_cases hd : k = dst <;> simp_all [S₁]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
