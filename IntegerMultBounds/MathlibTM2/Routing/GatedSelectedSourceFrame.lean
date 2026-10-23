module

public import IntegerMultBounds.MathlibTM2.Routing.BinarySelectedSourcePosition
public import IntegerMultBounds.MathlibTM2.Routing.ActivityProfileFrame

/-! Compute and emit one selected-source profile frame, then erase its address.
All source coordinates and arithmetic scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def gatedSelectedSourceFrameProgram (rg : Fin 13 → Fin T) (zr : BinaryZeroReg → Fin T) (src saved dst : Fin T) : Pr P T Q A U :=
  .seq (binarySelectedSourcePositionProgram rg)
    (.seq (activityProfileFrameProgram src saved (rg 5) dst (rg 9) (rg 10) zr) (bclear (rg 5)))

def gatedSelectedSourceFrameCost (Lw Li Lk : ℕ) :=
  (Li * (12 * (Li + Lk) + 20) + 36 * (Li + Lk) + 44) +
    (optionalBinaryProfileFrameCost Lw (Li + Lk) + 1) + (2 * (Li + Lk) + 2)

theorem gatedSelectedSourceFrame_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg) (dst : Fin T) (hsep : ∀ j, dst ≠ rg j)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = dst)
    (src saved : Fin T) (hss : src ≠ saved)
    (hsrcRg : ∀ j, src ≠ rg j) (hsavedRg : ∀ j, saved ≠ rg j)
    (hdsrc : dst ≠ src) (hdsaved : dst ≠ saved)
    (hz5 : ∀ j, zr j ≠ rg 5) (hsrcZr : ∀ j, src ≠ zr j) (hsavedZr : ∀ j, saved ≠ zr j)
    (enabled : Bool) (rest : List (Fin (A + 4)))
    (Lw Li Lk i k b r : ℕ) (hwidth : Li + Lk < 2 ^ Lw) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hactivity : S.R src = bitSymbol enabled :: rest)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hbase : S.R (rg 2) = binSyms (Li + Lk) b) (hlocal : S.R (rg 3) = binSyms (Li + Lk) r)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → S.R (rg j) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ j, S.R (zr (.scratch j)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ gatedSelectedSourceFrameCost Lw Li Lk ∧
      Exec body (gatedSelectedSourceFrameProgram rg zr src saved dst) (mk v S) steps
        (mk v' { S with R := activityProfileFrameBank S.R src saved dst (Li + Lk) (i * k + b + r) enabled rest }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binarySelectedSourcePosition_exec body rg hrg Li Lk i k b r hi hk hfit
    v S hindex hstride hbase hlocal (fun j h0 h1 h2 h3 _ => hblank j h0 h1 h2 h3)
  rw [hblank 5 (by decide) (by decide) (by decide) (by decide), List.append_nil] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 5) (binSyms (Li + Lk) (i * k + b + r)) }
  have hkeep (j : Fin 13) (hj : j ≠ 5) : G.R (rg j) = S.R (rg j) := by simp [G, hrg.eq_iff, hj]
  have hzkeep (j : BinaryZeroReg) : G.R (zr j) = S.R (zr j) := by simp [G, hz5 j]
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := activityProfileFrame_exec body src saved (rg 5) dst (rg 9) (rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff, hss, hsrcRg, hsavedRg, hsep,
      hdsrc.symm, hdsaved.symm, (hsep _).symm])
    zr hzr hdst hsrcZr hsavedZr Lw (Li + Lk) (i * k + b + r) hwidth enabled rest v₁ G
    (by simp [G, hsrcRg 5, hactivity]) (by simp [G])
    ((hkeep 9 (by decide)).trans (hblank 9 (by decide) (by decide) (by decide) (by decide)))
    ((hkeep 10 (by decide)).trans (hblank 10 (by decide) (by decide) (by decide) (by decide)))
    ((hzkeep .width).trans hwidthInput) ((hzkeep .unary).trans hunary)
    (fun j => (hzkeep (.scratch j)).trans (hzeroScratch j))
  let H : Stacks T A := { G with R := activityProfileFrameBank G.R src saved dst (Li + Lk) (i * k + b + r) enabled rest }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 5) v₂ H
  have hp : H.R (rg 5) = binSyms (Li + Lk) (i * k + b + r) := by
    simp [H, activityProfileFrameBank, G, (hsep 5).symm, (hsrcRg 5).symm, (hsavedRg 5).symm]
  have hf : Function.update H.R (rg 5) [] = activityProfileFrameBank S.R src saved dst
      (Li + Lk) (i * k + b + r) enabled rest := by
    funext j
    by_cases hj : j = rg 5
    · subst j
      simp [activityProfileFrameBank, (hsep 5).symm, (hsrcRg 5).symm, (hsavedRg 5).symm,
        hblank 5 (by decide) (by decide) (by decide) (by decide)]
    · simp [H, G, activityProfileFrameBank, Function.update_apply, hj, hsavedRg 5, hsep 5]
  rw [hf, hp, length_binSyms] at hx₃
  exact ⟨v₃, m₁ + (m₂ + (2 * (Li + Lk) + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold gatedSelectedSourceFrameCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
