module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySelectedSourcePosition
public import IntegerMultBounds.MathlibTM2.Routing.BinaryActiveProfileFrame

/-! Compute and emit one selected-source profile frame, then erase its address.
All source coordinates and arithmetic scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def selectedSourceFrameProgram (rg : Fin 13 → Fin T) (dst : Fin T) : Pr P T Q A U :=
  .seq (binarySelectedSourcePositionProgram rg)
    (.seq (binaryActiveProfileFrameProgram (rg 5) dst (rg 9) (rg 10)) (bclear (rg 5)))

def selectedSourceFrameCost (Li Lk : ℕ) :=
  Li * (12 * (Li + Lk) + 20) + 44 * (Li + Lk) + 55

theorem selectedSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg) (dst : Fin T) (hsep : ∀ j, dst ≠ rg j)
    (Li Lk i k b r : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hbase : S.R (rg 2) = binSyms (Li + Lk) b) (hlocal : S.R (rg 3) = binSyms (Li + Lk) r)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ selectedSourceFrameCost Li Lk ∧
      Exec body (selectedSourceFrameProgram rg dst) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (affineProfileFrames (Li + Lk) [(true, i * k + b + r)] ++ S.R dst) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binarySelectedSourcePosition_exec body rg hrg Li Lk i k b r hi hk hfit
    v S hindex hstride hbase hlocal (fun j h0 h1 h2 h3 _ => hblank j h0 h1 h2 h3)
  rw [hblank 5 (by decide) (by decide) (by decide) (by decide), List.append_nil] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 5) (binSyms (Li + Lk) (i * k + b + r)) }
  have hkeep (j : Fin 13) (hj : j ≠ 5) : G.R (rg j) = S.R (rg j) := by simp [G, hrg.eq_iff, hj]
  obtain ⟨v₂, hu₂, hx₂⟩ := binaryActiveProfileFrame_exec body (rg 5) dst (rg 9) (rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff, hsep, (hsep _).symm]) (Li + Lk) (i * k + b + r) v₁ G
    (by simp [G])
    ((hkeep 9 (by decide)).trans (hblank 9 (by decide) (by decide) (by decide) (by decide)))
    ((hkeep 10 (by decide)).trans (hblank 10 (by decide) (by decide) (by decide) (by decide)))
  have hd : G.R dst = S.R dst := by simp [G, hsep 5]
  rw [hd] at hx₂
  let out := affineProfileFrames (A := A) (Li + Lk) [(true, i * k + b + r)] ++ S.R dst
  let H : Stacks T A := { G with R := Function.update G.R dst out }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 5) v₂ H
  have hp : H.R (rg 5) = binSyms (Li + Lk) (i * k + b + r) := by simp [H, G, (hsep 5).symm]
  have hf : Function.update H.R (rg 5) [] = Function.update S.R dst out := by
    funext j
    by_cases hj : j = rg 5
    · subst j
      simp [(hsep 5).symm, hblank 5 (by decide) (by decide) (by decide) (by decide)]
    · simp [H, G, Function.update_apply, hj]
  rw [hf, hp, length_binSyms] at hx₃
  exact ⟨v₃, m₁ + ((6 * (Li + Lk) + 9) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold selectedSourceFrameCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
