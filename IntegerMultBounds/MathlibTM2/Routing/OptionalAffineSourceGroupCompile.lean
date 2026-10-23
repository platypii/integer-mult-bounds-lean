module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceGroupTrace

/-! Generate a complete affine source profile from a src tape and live binary
operands. Restore the src and reverse the accumulator into the profile output. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGroupCompileProgram (rg : Fin 12 → Fin T) (zr : BinaryZeroReg → Fin T) (rp : Fin 7 → Fin T) (src saved accum dst : Fin T) : Pr P T Q A U :=
  .seq (.act (peekR src))
    (.seq (.loop (·.flag) (optionalAffineSourceGroupLoopBody rg zr rp src saved accum))
      (.seq (moveR saved src id) (moveR accum dst id)))

theorem optionalAffineSourceGroupCompile_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved accum dst : Fin T)
    (rp : Fin 7 → Fin T) (hrp : Function.Injective rp) (hsep : ∀ r, rp r ≠ rg 5)
    (hpRg : ∀ r, rp 3 ≠ rg r)
    (hsrcRp : ∀ r, src ≠ rp r) (hsavedRp : ∀ r, saved ≠ rp r)
    (haRp : ∀ r, accum ≠ rp r) (hpIndex : ∀ r, rp r ≠ rg 0)
    (hreg : [src, saved, accum, dst].Nodup)
    (hcsep : ∀ r, src ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r)
    (hcz : ∀ r, src ≠ zr r) (hsz : ∀ r, saved ≠ zr r)
    (haz : ∀ r, accum ≠ zr r) (hzIndex : ∀ r, zr r ≠ rg 0)
    (Lg g : ℕ) (hg : g < 2 ^ Lg)
    (Lw Li Lk i k o : ℕ) (input : List Bool) (hwidth : Li + Lk < 2 ^ Lw) (hk : k < 2 ^ Lk)
    (hi : i + input.length ≤ 2 ^ Li)
    (hfit : ∀ j < input.length, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = input.map bitSymbol) (hindex : S.R (rg 0) = binSyms Li i)
    (hstride : S.R (rg 1) = binSyms Lk k) (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hsaved : S.R saved = []) (haccum : S.R accum = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = [])
    (houtput : S.R (rp 3) = []) (hgroup : S.R (rp 0) = binSyms Lg g)
    (hcount : S.R (rp 1) = []) (hrepeatSaved : S.R (rp 2) = [])
    (hwork : S.R (rp 4) = []) (htmp : S.R (rp 5) = []) (hctmp : S.R (rp 6) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * optionalAffineSourceGroupIterationCost Lg g Lw Li Lk + 2 * input.length +
        2 * (input.length * (g * (Li + Lk + 3))) + 6 ∧
      Exec body (optionalAffineSourceGroupCompileProgram rg zr rp src saved accum dst) (mk v S) steps
        (mk v' { S with R := Function.update (Function.update S.R dst
          (optionalAffineSourceGroupWord Li Lk i k o g input ++ S.R dst)) (rg 0) (binSyms Li (i + input.length)) }) := by
  have hn := hreg
  regs_ne hn
  let u := { v with flag := input.head?.isSome }
  have hp : (peekR src : Act T Q A U).run (mk v S) = mk u S := by simp only [peekR_run, hsrc, List.head?_map, Option.isSome_map]; rfl
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := optionalAffineSourceGroupLoop_exec body rg hrg zr hzr hdst
    src saved accum rp hrp hsep hpRg hsrcRp hsavedRp haRp hpIndex ‹src ≠ saved› hcsep hssep hcz hsz hasep
    ‹src ≠ accum›.symm ‹saved ≠ accum›.symm haz hzIndex
    Lg g hg Lw Li Lk i k o input hwidth hk hi hfit u S hsrc hindex hstride hoffset hblank
    hwidthInput hunary hzeroScratch houtput hgroup hcount hrepeatSaved hwork htmp hctmp rfl
  rw [optionalAffineSourceGroupTrace_closed S.R rg rp src saved accum ‹src ≠ saved› ‹src ≠ accum› ‹saved ≠ accum›
    (hcsep 0) (hssep 0) (hasep 0) Li Lk i k o g input hsrc hindex] at hx₁
  let S₁ : Stacks T A := { S with R := optionalAffineSourceGroupClosedBank S.R rg rp src saved accum Li Lk i k o g input }
  have hs : S₁.R saved = (input.map bitSymbol).reverse := by
    simp [S₁, optionalAffineSourceGroupClosedBank, (hssep 0), ‹saved ≠ accum›, hsaved]
  obtain ⟨v₂, hu₂, hx₂⟩ := moveR_exec (body := body) saved src (Ne.symm ‹src ≠ saved›) id v₁ S₁
  let S₂ : Stacks T A := { S₁ with R := movedR S₁.R saved src id (S₁.R saved) }
  have ha : S₂.R accum = (optionalAffineSourceGroupWord Li Lk i k o g input).reverse := by
    simp [S₂, movedR, S₁, optionalAffineSourceGroupClosedBank, (hasep 0), ‹src ≠ accum›.symm, ‹saved ≠ accum›.symm, haccum]
  obtain ⟨v₃, hu₃, hx₃⟩ := moveR_exec (body := body) accum dst ‹accum ≠ dst› id v₂ S₂
  have hf : movedR S₂.R accum dst id (S₂.R accum) = Function.update (Function.update S.R dst
      (optionalAffineSourceGroupWord Li Lk i k o g input ++ S.R dst)) (rg 0) (binSyms Li (i + input.length)) := by
    funext j
    by_cases hj : j = rg 0
    · subst j; simp [movedR, S₂, S₁, optionalAffineSourceGroupClosedBank, (hasep 0).symm, (hdsep 0).symm, (hssep 0).symm, (hcsep 0).symm]
    · by_cases hd : j = dst
      · subst j; simp [movedR, S₂, S₁, optionalAffineSourceGroupClosedBank, hasep, hssep, hdsep, ‹src ≠ accum›.symm, ‹saved ≠ accum›.symm, hsaved, haccum, ‹src ≠ dst›.symm, ‹saved ≠ dst›.symm, ‹accum ≠ dst›.symm]
      · by_cases hc : j = src
        · subst j; simp [movedR, S₂, S₁, optionalAffineSourceGroupClosedBank, hsaved, haccum, hsrc, hcsep, hssep, ‹saved ≠ accum›, ‹src ≠ accum›, ‹src ≠ dst›, ‹src ≠ saved›]
        · by_cases hsj : j = saved
          · subst j; simp [movedR, S₂, S₁, optionalAffineSourceGroupClosedBank, hssep, hsaved, ‹saved ≠ accum›, ‹saved ≠ dst›, ‹src ≠ saved›.symm]
          · by_cases haj : j = accum
            · subst j; simp [movedR, hasep, haccum, ‹accum ≠ dst›]
            · simp [movedR, S₂, S₁, optionalAffineSourceGroupClosedBank, Function.update_apply, hj, hd, hc, hsj, haj]
  have hslen : (S₁.R saved).length = input.length := by rw [hs, List.length_reverse, List.length_map]
  rw [hslen] at hx₂
  rw [hf, ha, List.length_reverse, optionalAffineSourceGroupWord_length] at hx₃
  refine ⟨v₃, 1 + (m₁ + ((2 * input.length + 2) + (2 * (input.length * (g * (Li + Lk + 3))) + 2))),
    hu₃.trans (hu₂.trans (hu₁.trans rfl)), by omega, ?_⟩
  exact Exec.seq (hp ▸ Exec.act (body := body) _ (mk v S)) (Exec.seq hx₁ (Exec.seq hx₂ hx₃))

end IntegerMultBounds.MathlibTM2.Routing
