module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Isolate the real solver's 144 registers from four retained component registers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

def componentReg (i : Fin 144) : Fin 148 := ⟨i.val,by omega⟩

theorem componentReg_injective : Function.Injective componentReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 148 => k.val) h)

theorem componentReg_off (k : Fin 148) (hk : 144 ≤ k.val) : ∀ i, componentReg i ≠ k := by
  intro i h
  have hh := congrArg (fun k : Fin 148 => k.val) h
  simp only [componentReg] at hh
  omega

theorem componentProject_updateR {A : ℕ} (S : Stacks 148 A) (k : Fin 148)
    (xs : List (Fin (A+4))) (hk : 144 ≤ k.val) :
    embStk componentReg {S with R := Function.update S.R k xs} = embStk componentReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  simp [embStk,Function.comp_def,componentReg_off k hk i]

theorem componentProject_updateR_inner {A : ℕ} (S : Stacks 148 A) (k : Fin 144)
    (xs : List (Fin (A+4))) :
    embStk componentReg {S with R := Function.update S.R (componentReg k) xs} =
      {(embStk componentReg S) with R := Function.update (embStk componentReg S).R k xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = k
  · subst i; simp [embStk]
  · have hne : componentReg i ≠ componentReg k := fun he => hi (componentReg_injective he)
    simp [embStk,Function.comp_def,hi,hne]

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 144 Q A U}

theorem componentExec_twoPorts (p : Pr P₀ 144 Q A U) (v : HS 148 Q A U) (S : Stacks 148 A)
    (v' : HS 144 Q A U) (n : ℕ) (input output : List (Fin (A+4)))
    (hu : v'.user = v.user)
    (he : Exec body p (mk (embDn componentReg v) (embStk componentReg S)) n
      (mk v' {(embStk componentReg S) with R := (Function.update
        (Function.update (embStk componentReg S).R 110 input) 132 output)})) :
    ∃ v'', v''.user = v.user ∧ Exec (embTab componentReg body) (embProg componentReg id p)
      (mk v S) n (mk v'' {S with R := Function.update (Function.update S.R 110 input) 132 output}) := by
  have hbody : ∀ p, (embTab componentReg body) (id p) = embProg componentReg id (body p) := fun _ => rfl
  obtain ⟨v'',hv'',hu'',he''⟩ := exec_emb_ovr (ι := id) (body' := embTab componentReg body)
    componentReg_injective hbody he v rfl S rfl
  refine ⟨v'',hu''.trans hu,he''.cast rfl ?_⟩
  apply congrArg (mk v'')
  let B := embStk componentReg S
  let B₁ : Stacks 144 A := {B with R := Function.update B.R 110 input}
  rw [embOvr_updR componentReg_injective B₁ S 132 output,
    embOvr_updR componentReg_injective B S 110 input,embOvr_stk]
  rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
