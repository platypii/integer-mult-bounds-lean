module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceFrame
public import IntegerMultBounds.MathlibTM2.Routing.BinaryWordRepeat

/-! Compute one optional affine source frame, repeat it a live binary number
of times, and erase the temporary frame. Only the group output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGroupProgram (rg : Fin 12 → Fin T)
    (zr : BinaryZeroReg → Fin T) (rp : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (optionalAffineSourceFrameProgram rg zr)
    (.seq (binaryWordRepeatProgram (rp 0) (rp 1) (rp 2) (rg 5) (rp 3) (rp 4) (rp 5) (rp 6))
      (bclear (rg 5)))

theorem optionalAffineSourceGroup_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (Lg g : ℕ) (hg : g < 2 ^ Lg)
    (Lw Li Lk i k o : ℕ) (hwidth : Li + Lk < 2 ^ Lw)
    (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk) (hfit : i * k + o < 2 ^ (Li + Lk))
    (enabled : Bool) (v : HS T Q A U) (S : Stacks T A) (hflag : v.flag = enabled)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (hgroup : S.R (rp 0) = binSyms Lg g)
    (hcount : S.R (rp 1) = []) (hsaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ optionalAffineSourceFrameCost Lw Li Lk + binaryWordRepeatCost Lg g (Li + Lk + 3) + (2 * (Li + Lk + 3) + 2) ∧
      Exec body (optionalAffineSourceGroupProgram rg zr rp) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rp 3) (wordCopies (affineProfileFrames (Li + Lk) [(enabled, if enabled then i * k + o else 0)]) g ++ S.R (rp 3)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceFrame_exec body rg hrg zr hzr hdst
    Lw Li Lk i k o hwidth hi hk hfit enabled v S hflag hindex hstride hoffset
    (fun r h0 h1 h2 _ => hblank r h0 h1 h2) hwidthInput hunary hzeroScratch
  let word := affineProfileFrames (A := A) (Li + Lk) [(enabled, if enabled then i * k + o else 0)]
  let G : Stacks T A := { S with R := Function.update S.R (rg 5) (word ++ S.R (rg 5)) }
  have hf : G.R (rg 5) = word := by simp [G, hblank 5 (by decide) (by decide) (by decide)]
  have hkeep (r : Fin 7) : G.R (rp r) = S.R (rp r) := by simp [G, hsep r]
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := binaryWordRepeat_exec body
    (rp 0) (rp 1) (rp 2) (rg 5) (rp 3) (rp 4) (rp 5) (rp 6)
    (by simp [List.nodup_cons, hrp.eq_iff, hsep, (hsep _).symm]) Lg g hg word v₁ G
    ((hkeep 0).trans hgroup) hf ((hkeep 1).trans hcount) ((hkeep 2).trans hsaved)
    ((hkeep 4).trans hwork) ((hkeep 5).trans htmp) ((hkeep 6).trans hctmp)
  let H : Stacks T A := { G with R := Function.update G.R (rp 3) (wordCopies word g ++ G.R (rp 3)) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 5) v₂ H
  have hb : H.R (rg 5) = word := by simp [H, (hsep 3).symm, hf]
  have hbank : Function.update H.R (rg 5) [] = Function.update S.R (rp 3) (wordCopies word g ++ S.R (rp 3)) := by
    funext j
    by_cases hj : j = rg 5
    · subst j
      simp [(hsep 3).symm, hblank 5 (by decide) (by decide) (by decide)]
    · by_cases hd : j = rp 3
      · subst j
        simp [H, G, hsep 3]
      · simp [H, G, Function.update_apply, hj, hd]
  have hlen : word.length = Li + Lk + 3 := by simp [word, affineProfileFrames]; omega
  rw [hbank, hb, hlen] at hx₃
  rw [hlen] at hm₂
  exact ⟨v₃, m₁ + (m₂ + (2 * (Li + Lk + 3) + 2)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
