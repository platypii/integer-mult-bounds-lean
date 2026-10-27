module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Keep the table-loop cursor, count and saved count outside the resident arithmetic bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

def tableReg (i : Fin 151) : Fin 154 := ⟨i.val,by omega⟩

theorem tableReg_injective : Function.Injective tableReg := by
  intro i j h
  exact Fin.ext (congrArg (fun k : Fin 154 => k.val) h)

theorem tableProject_updateR_inner {A : ℕ} (S : Stacks 154 A) (k : Fin 151)
    (xs : List (Fin (A+4))) :
    embStk tableReg {S with R := Function.update S.R (tableReg k) xs} =
      {(embStk tableReg S) with R := Function.update (embStk tableReg S).R k xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = k
  · subst i; simp [embStk]
  · have hne : tableReg i ≠ tableReg k := fun h => hi (tableReg_injective h)
    simp [embStk,Function.comp_def,hi,hne]

theorem tableProject_updateR_outer {A : ℕ} (S : Stacks 154 A) (k : Fin 154)
    (xs : List (Fin (A+4))) (hk : 151 ≤ k.val) :
    embStk tableReg {S with R := Function.update S.R k xs} = embStk tableReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  have hne : tableReg i ≠ k := by
    intro h
    have hv := congrArg (fun k : Fin 154 => k.val) h
    dsimp [tableReg] at hv
    omega
  simp [embStk,Function.comp_def,hne]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 151 Q A U}

theorem tableExec_twoPorts (p : Pr P 151 Q A U) (v : HS 154 Q A U) (S : Stacks 154 A)
    (v' : HS 151 Q A U) (m : ℕ) (i j : Fin 151) (xs ys : List (Fin (A+4)))
    (hu : v'.user = v.user)
    (he : Exec body p (mk (embDn tableReg v) (embStk tableReg S)) m
      (mk v' {(embStk tableReg S) with R := (Function.update
        (Function.update (embStk tableReg S).R i xs) j ys)})) :
    ∃ v'', v''.user = v.user ∧ Exec (embTab tableReg body) (embProg tableReg id p)
      (mk v S) m (mk v'' {S with R := (Function.update (Function.update S.R (tableReg i) xs) (tableReg j) ys)}) := by
  obtain ⟨v'',hv'',hu'',he''⟩ := exec_emb_ovr (ι := id) (body' := embTab tableReg body)
    tableReg_injective (fun _ => rfl) he v rfl S rfl
  refine ⟨v'',hu''.trans hu,he''.cast rfl ?_⟩
  apply congrArg (mk v'')
  let B := embStk tableReg S
  let B₁ : Stacks 151 A := {B with R := Function.update B.R i xs}
  rw [embOvr_updR tableReg_injective B₁ S j ys,
    embOvr_updR tableReg_injective B S i xs,embOvr_stk]

theorem tableExec_threePorts (p : Pr P 151 Q A U) (v : HS 154 Q A U) (S : Stacks 154 A)
    (v' : HS 151 Q A U) (m : ℕ) (i j k : Fin 151) (xs ys zs : List (Fin (A+4)))
    (hu : v'.user = v.user)
    (he : Exec body p (mk (embDn tableReg v) (embStk tableReg S)) m
      (mk v' {(embStk tableReg S) with R := (Function.update (Function.update
        (Function.update (embStk tableReg S).R i xs) j ys) k zs)})) :
    ∃ v'', v''.user = v.user ∧ Exec (embTab tableReg body) (embProg tableReg id p)
      (mk v S) m (mk v'' {S with R := (Function.update (Function.update (Function.update S.R (tableReg i) xs) (tableReg j) ys) (tableReg k) zs)}) := by
  obtain ⟨v'',hv'',hu'',he''⟩ := exec_emb_ovr (ι := id) (body' := embTab tableReg body)
    tableReg_injective (fun _ => rfl) he v rfl S rfl
  refine ⟨v'',hu''.trans hu,he''.cast rfl ?_⟩
  apply congrArg (mk v'')
  let B := embStk tableReg S
  let B₁ : Stacks 151 A := {B with R := Function.update B.R i xs}
  let B₂ : Stacks 151 A := {B₁ with R := Function.update B₁.R j ys}
  rw [embOvr_updR tableReg_injective B₂ S k zs,
    embOvr_updR tableReg_injective B₁ S j ys,
    embOvr_updR tableReg_injective B S i xs,embOvr_stk]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
