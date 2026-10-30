module

public import IntegerMultBounds.MathlibTM2.Host.Embed

/-! Keep the routed queue and retained headers outside the numerical bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack

/-- Input conversion uses the native bank, except for the queue, replica count
and common coefficient width, which live beyond all 303 numerical registers. -/
def keyBatchInputReg (i : Fin 303) : Fin 306 :=
  if i = 15 then 303 else if i = 16 then 304 else if i = 11 then 305
  else Fin.castLE (by decide) i

theorem keyBatchInputReg_injective : Function.Injective keyBatchInputReg := by
  intro i j he
  apply Fin.ext
  have hv := congrArg Fin.val he
  dsimp [keyBatchInputReg] at hv
  split_ifs at hv <;> subst_vars <;> simp_all <;> omega

/-- The solver uses its ordinary low bank, disjoint from all retained fields. -/
def keyBatchSolverReg : Fin 303 → Fin 306 := Fin.castLE (by decide)

theorem keyBatchSolverReg_injective : Function.Injective keyBatchSolverReg := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 306 => k.val) he

theorem keyBatchSolverReg_retained (j : Fin 306) (hj : 303 ≤ j.val) :
    ∀ i, keyBatchSolverReg i ≠ j := by
  intro i he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val = j.val at hv
  omega

/-- Any execution inside the native solver bank preserves the routed queue,
replica count and common width. Lifting changes neither steps nor user state. -/
theorem keyBatchSolver_exec {Q A : ℕ} {P U : Type}
    {body : P → Pr P 303 Q A U} {bodyLarge : P → Pr P 306 Q A U}
    (hbody : ∀ f, bodyLarge f = embProg keyBatchSolverReg id (body f))
    {run : Pr P 303 Q A U} {v₀ v₁ : HS 303 Q A U} {S₀ S₁ : Stacks 303 A} {n : ℕ}
    (he : Exec body run (mk v₀ S₀) n (mk v₁ S₁))
    (v : HS 306 Q A U) (hv : embDn keyBatchSolverReg v = v₀)
    (S : Stacks 306 A) (hS : embStk keyBatchSolverReg S = S₀) :
    ∃ v' F, Exec bodyLarge (embProg keyBatchSolverReg id run) (mk v S) n (mk v' F) ∧
      embStk keyBatchSolverReg F = S₁ ∧ v'.user = v₁.user ∧
      ∀ j : Fin 306, 303 ≤ j.val → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨v',F,he',hv',hu,hproj,hoff⟩ := exec_emb keyBatchSolverReg_injective hbody he v hv S hS
  exact ⟨v',F,he',hproj,hu,fun j hj => hoff j (keyBatchSolverReg_retained j hj)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
