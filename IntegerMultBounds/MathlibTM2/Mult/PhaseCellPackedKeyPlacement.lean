module

public import IntegerMultBounds.MathlibTM2.Host.EmbedUpdate

/-! Embed the actual packed numerical bank below its local queue workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host

def packedKeySolverReg : Fin 263 → Fin 276 := Fin.castLE (by decide)

theorem packedKeySolverReg_injective : Function.Injective packedKeySolverReg := by
  intro i j he
  apply Fin.ext
  exact congrArg (fun k : Fin 276 => k.val) he

theorem packedKeySolverReg_off (j : Fin 276) (hj : 263 ≤ j.val) :
    ∀ i, packedKeySolverReg i ≠ j := by
  intro i he
  have hv := congrArg Fin.val he
  have hi := i.isLt
  change i.val = j.val at hv
  omega

/-- The input pipeline changes only the RHS in the native packed-bank view;
the external queue update cannot alter numerical setup or factor metadata. -/
theorem packedKeyInput_native_view {A : ℕ} (S : Stacks 276 A)
    (tail xs : List (Fin (A+4))) :
    embStk packedKeySolverReg {S with R := (Function.update (Function.update S.R 263 tail) 110 xs)} =
      {embStk packedKeySolverReg S with R := Function.update (embStk packedKeySolverReg S).R 110 xs} := by
  change embStk packedKeySolverReg
    ({ {S with R := Function.update S.R 263 tail} with
      R := Function.update (Function.update S.R 263 tail) (packedKeySolverReg 110) xs}) = _
  rw [embStk_updateR packedKeySolverReg_injective,
    embStk_updateR_off S 263 tail (packedKeySolverReg_off 263 (by decide))]

/-- Lift a proved packed numerical execution without touching any external
queue/header/scratch field and without adding steps. -/
theorem packedKeySolver_exec {Q A : ℕ} {P U : Type}
    {body : P → Pr P 263 Q A U} {bodyLarge : P → Pr P 276 Q A U}
    (hbody : ∀ f, bodyLarge f = embProg packedKeySolverReg id (body f))
    {run : Pr P 263 Q A U} {v₀ v₁ : HS 263 Q A U} {S₀ S₁ : Stacks 263 A} {n : ℕ}
    (he : Exec body run (mk v₀ S₀) n (mk v₁ S₁))
    (v : HS 276 Q A U) (hv : embDn packedKeySolverReg v = v₀)
    (S : Stacks 276 A) (hS : embStk packedKeySolverReg S = S₀) :
    ∃ v' F, Exec bodyLarge (embProg packedKeySolverReg id run) (mk v S) n (mk v' F) ∧
      embStk packedKeySolverReg F = S₁ ∧ v'.user = v₁.user ∧
      ∀ j : Fin 276, 263 ≤ j.val → F.L j = S.L j ∧ F.R j = S.R j := by
  obtain ⟨v',F,he',hv',hu,hproj,hoff⟩ := exec_emb packedKeySolverReg_injective hbody he v hv S hS
  exact ⟨v',F,he',hproj,hu,fun j hj => hoff j (packedKeySolverReg_off j hj)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
