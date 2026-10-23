module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryActiveProfileFrame

/-! Enumerate source wires directly from a binary counter. No stride, offset,
multiplication workspace or numerical selector table is required. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def counterSourceStepProgram (rg : Fin 5 → Fin T) : Pr P T Q A U :=
  .seq (binaryActiveProfileFrameProgram (rg 0) (rg 1) (rg 2) (rg 3))
    (countIter (rg 0) (rg 2) (rg 4))

def counterSourceStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T) (L i : ℕ) :=
  Function.update (Function.update R (rg 1) (affineProfileFrames L [(true, i)] ++ R (rg 1)))
    (rg 0) (binSyms L (i + 1))

theorem counterSourceStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (L i : ℕ)
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms L i) (htmp : S.R (rg 2) = []) (hwork : S.R (rg 3) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (counterSourceStepProgram rg) (mk v S) (10 * L + 14)
        (mk v' { S with R := counterSourceStepBank S.R rg L i }) := by
  obtain ⟨v₁, hu₁, hx₁⟩ := binaryActiveProfileFrame_exec body (rg 0) (rg 1) (rg 2) (rg 3)
    (by simp [List.nodup_cons, hrg.eq_iff]) L i v S hindex htmp hwork
  let G : Stacks T A := { S with R := Function.update S.R (rg 1) (affineProfileFrames L [(true, i)] ++ S.R (rg 1)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := countIter_exec (body := body) (W := L) (j := i)
    (hrg.ne (by decide : (0 : Fin 5) ≠ 2)) (rg 4) v₁ G
    (by simp [G, hrg.eq_iff, hindex]) (by simp [G, hrg.eq_iff, htmp])
  exact ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq hx₁ hx₂) (by omega) rfl⟩

def counterSourceReverseStepProgram (rg : Fin 5 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (counterSourceStepProgram rg) (moveR (rg 1) dst id)

def counterSourceReverseStepBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 5 → Fin T)
    (dst : Fin T) (L i : ℕ) :=
  Function.update (Function.update R dst ((affineProfileFrames L [(true, i)]).reverse ++ R dst))
    (rg 0) (binSyms L (i + 1))

theorem counterSourceReverseStep_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (dst : Fin T) (hsep : ∀ r, dst ≠ rg r)
    (L i : ℕ) (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms L i) (hframe : S.R (rg 1) = [])
    (htmp : S.R (rg 2) = []) (hwork : S.R (rg 3) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (counterSourceReverseStepProgram rg dst) (mk v S)
        ((10 * L + 14) + (2 * (L + 3) + 2))
        (mk v' { S with R := counterSourceReverseStepBank S.R rg dst L i }) := by
  obtain ⟨v₁, hu₁, hx₁⟩ := counterSourceStep_exec body rg hrg L i v S hindex htmp hwork
  let G : Stacks T A := { S with R := counterSourceStepBank S.R rg L i }
  have hf : G.R (rg 1) = affineProfileFrames L [(true, i)] := by
    simp [G, counterSourceStepBank, hrg.eq_iff, hframe]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) (rg 1) dst (hsep 1).symm id v₁ G
  have hbank : movedR G.R (rg 1) dst id (G.R (rg 1)) = counterSourceReverseStepBank S.R rg dst L i := by
    funext j
    by_cases hj : j = rg 1
    · subst j
      simp [movedR, G, counterSourceStepBank, counterSourceReverseStepBank,
        hrg.eq_iff, (hsep 1).symm, hframe]
    · by_cases hd : j = dst
      · subst j
        simp [movedR, G, counterSourceStepBank, counterSourceReverseStepBank, hrg.eq_iff, hsep, hframe]
      · simp [movedR, G, counterSourceStepBank, counterSourceReverseStepBank, Function.update_apply, hj, hd]
  have hlen : (affineProfileFrames (A := A) L [(true, i)]).length = L + 3 := by
    simp [affineProfileFrames]; omega
  rw [hbank, hf, hlen] at hx₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.seq hx₁ hx₂⟩

end IntegerMultBounds.MathlibTM2.Routing
