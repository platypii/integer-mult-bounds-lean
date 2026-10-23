module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryActiveProfileFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryAffinePosition

/-! Compute one affine source selector from live index, stride and offset,
emit its active profile frame, and erase the computed selector. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def affineSourceFrameProgram (rg : Fin 12 → Fin T) : Pr P T Q A U :=
  .seq (binaryAffinePositionProgram (rg 0) (rg 1) (rg 3) (rg 2) (rg 4)
    (rg 6) (rg 7) (rg 8) (rg 9) (rg 10) (rg 11))
    (.seq (binaryActiveProfileFrameProgram (rg 4) (rg 5) (rg 8) (rg 9)) (bclear (rg 4)))

def affineSourceFrameCost (Li Lk : ℕ) := Li * (12 * (Li + Lk) + 20) + 34 * (Li + Lk) + 45

theorem affineSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (Li Lk i k o : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → r ≠ 5 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ affineSourceFrameCost Li Lk ∧
      Exec body (affineSourceFrameProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 5) (affineProfileFrames (Li + Lk) [(true, i * k + o)] ++ S.R (rg 5)) }) := by
  have hb (r : Fin 12) (h0 : r ≠ 0) (h1 : r ≠ 1) (h2 : r ≠ 2) (h5 : r ≠ 5) := hblank r h0 h1 h2 h5
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binaryAffinePosition_exec body
    (rg 0) (rg 1) (rg 3) (rg 2) (rg 4) (rg 6) (rg 7) (rg 8) (rg 9) (rg 10) (rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide))
    Li Lk i k o hi hk hfit v S hindex hstride hoffset
    (hb 3 (by decide) (by decide) (by decide) (by decide))
    (hb 4 (by decide) (by decide) (by decide) (by decide))
    (hb 6 (by decide) (by decide) (by decide) (by decide))
    (hb 7 (by decide) (by decide) (by decide) (by decide))
    (hb 8 (by decide) (by decide) (by decide) (by decide))
    (hb 9 (by decide) (by decide) (by decide) (by decide))
    (hb 10 (by decide) (by decide) (by decide) (by decide))
  let S₁ : Stacks T A := { S with R := Function.update S.R (rg 4) (binSyms (Li + Lk) (i * k + o)) }
  have hkeep (r : Fin 12) (hr : r ≠ 4) : S₁.R (rg r) = S.R (rg r) := by simp [S₁, hrg.eq_iff, hr]
  obtain ⟨v₂, hu₂, hx₂⟩ := binaryActiveProfileFrame_exec body (rg 4) (rg 5) (rg 8) (rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff]) (Li + Lk) (i * k + o) v₁ S₁ (by simp [S₁])
    ((hkeep 8 (by decide)).trans (hb 8 (by decide) (by decide) (by decide) (by decide)))
    ((hkeep 9 (by decide)).trans (hb 9 (by decide) (by decide) (by decide) (by decide)))
  rw [hkeep 5 (by decide)] at hx₂
  let out := affineProfileFrames (A := A) (Li + Lk) [(true, i * k + o)] ++ S.R (rg 5)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R (rg 5) out }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 4) v₂ S₂
  have hwire : S₂.R (rg 4) = binSyms (Li + Lk) (i * k + o) := by simp [S₂, S₁, hrg.eq_iff]
  have hf : Function.update S₂.R (rg 4) [] = Function.update S.R (rg 5) out := by
    funext j
    by_cases hj : j = rg 4
    · subst j; simp [hrg.eq_iff, hb 4 (by decide) (by decide) (by decide) (by decide)]
    · simp [S₂, S₁, Function.update_apply, hj]
  rw [hwire, length_binSyms, hf] at hx₃
  exact ⟨v₃, m₁ + ((6 * (Li + Lk) + 9) + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold affineSourceFrameCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
