module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Keep the folded boundary page outside the arithmetic register image. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

/-- Arithmetic's three conflicting low registers use fresh physical tapes.
The folded page on 109 and its headers on 115/116 never move. -/
def boundaryArithmeticReg (i : Fin 148) : Fin 151 :=
  if i = 109 then 148 else if i = 115 then 149 else if i = 116 then 150 else ⟨i.val,by omega⟩

theorem boundaryArithmeticReg_injective : Function.Injective boundaryArithmeticReg := by
  intro i j h
  have hv := congrArg (fun k : Fin 151 => k.val) h
  simp only [boundaryArithmeticReg] at hv
  split_ifs at hv <;> simp_all <;> omega

theorem boundaryArithmeticReg_off (i : Fin 148) :
    boundaryArithmeticReg i ≠ 109 ∧ boundaryArithmeticReg i ≠ 115 ∧ boundaryArithmeticReg i ≠ 116 := by
  dsimp [boundaryArithmeticReg]
  split_ifs <;> simp_all only [ne_eq, Fin.ext_iff] <;> omega


/-- Preparing or retaining the folded page leaves the arithmetic view unchanged. -/
theorem boundaryArithmeticProject_page {A : ℕ} (S : Stacks 151 A)
    (page width count : List (Fin (A+4))) :
    embStk boundaryArithmeticReg {S with R := (Function.update (Function.update
      (Function.update S.R 109 page) 115 width) 116 count)} = embStk boundaryArithmeticReg S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  obtain ⟨h109,h115,h116⟩ := boundaryArithmeticReg_off i
  simp [embStk,Function.comp_def,h109,h115,h116]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 148 Q A U}

/-- A single-output arithmetic execution preserves the entire boundary page and
all other physical tapes, including retained component streams. -/
theorem boundaryArithmeticExec_source (p : Pr P 148 Q A U) (v : HS 151 Q A U) (S : Stacks 151 A)
    (v' : HS 148 Q A U) (n : ℕ) (output : List (Fin (A+4)))
    (hu : v'.user = v.user)
    (he : Exec body p (mk (embDn boundaryArithmeticReg v) (embStk boundaryArithmeticReg S)) n
      (mk v' {(embStk boundaryArithmeticReg S) with R := Function.update (embStk boundaryArithmeticReg S).R 110 output})) :
    ∃ v'', v''.user = v.user ∧
      Exec (embTab boundaryArithmeticReg body) (embProg boundaryArithmeticReg id p)
        (mk v S) n (mk v'' {S with R := Function.update S.R 110 output}) := by
  obtain ⟨v'',hv'',hu'',he''⟩ := exec_emb_ovr (ι := id) (body' := embTab boundaryArithmeticReg body)
    boundaryArithmeticReg_injective (fun _ => rfl) he v rfl S rfl
  refine ⟨v'',hu''.trans hu,he''.cast rfl ?_⟩
  apply congrArg (mk v'')
  rw [embOvr_updR boundaryArithmeticReg_injective (embStk boundaryArithmeticReg S) S 110 output,embOvr_stk]
  rfl


theorem boundaryArithmeticProject_updateR_inner {A : ℕ} (S : Stacks 151 A) (k : Fin 148)
    (xs : List (Fin (A+4))) :
    embStk boundaryArithmeticReg {S with R := Function.update S.R (boundaryArithmeticReg k) xs} =
      {(embStk boundaryArithmeticReg S) with R := Function.update (embStk boundaryArithmeticReg S).R k xs} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = k
  · subst i; simp [embStk]
  · have hne : boundaryArithmeticReg i ≠ boundaryArithmeticReg k :=
      fun h => hi (boundaryArithmeticReg_injective h)
    simp [embStk,Function.comp_def,hi,hne]

theorem boundaryArithmeticProject_source {A : ℕ} (S : Stacks 151 A) (output : List (Fin (A+4))) :
    embStk boundaryArithmeticReg {S with R := Function.update S.R 110 output} =
      {(embStk boundaryArithmeticReg S) with R := Function.update (embStk boundaryArithmeticReg S).R 110 output} := by
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi : i = 110
  · subst i; simp [embStk,boundaryArithmeticReg]
  · have hne : boundaryArithmeticReg i ≠ 110 := by
      change boundaryArithmeticReg i ≠ boundaryArithmeticReg 110
      exact fun h => hi (boundaryArithmeticReg_injective h)
    simp [embStk,Function.comp_def,hi,hne]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
