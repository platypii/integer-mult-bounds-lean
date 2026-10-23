module

public import IntegerMultBounds.MathlibTM2.Routing.OptionalAffineSourceCompile
public import IntegerMultBounds.MathlibTM2.Routing.SparseCursorRestore

/-! Generate affine source profiles from src and scalar operands, restoring
both the complete src and original index. Only the profile output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host

variable {T Q A : ℕ} {P U : Type}

def optionalAffineSourceGenerateProgram (rg : Fin 12 → Fin T) (zr : BinaryZeroReg → Fin T) (src saved accum dst savedIndex : Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) savedIndex (rg 8) (rg 9))
    (.seq (optionalAffineSourceCompileProgram rg zr src saved accum dst)
      (sparseCursorRestoreProgram (rg 0) savedIndex (rg 8) (rg 9)))

theorem optionalAffineSourceGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg)
    (zr : BinaryZeroReg → Fin T) (hzr : Function.Injective zr) (hdst : zr .dst = rg 5)
    (src saved accum dst savedIndex : Fin T)
    (hreg : [src, saved, accum, dst, savedIndex].Nodup)
    (hcsep : ∀ r, src ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (hcz : ∀ r, src ≠ zr r) (hsz : ∀ r, saved ≠ zr r)
    (haz : ∀ r, accum ≠ zr r) (hiz : ∀ r, savedIndex ≠ zr r)
    (hzIndex : ∀ r, zr r ≠ rg 0)
    (Lw Li Lk i k o : ℕ) (input : List Bool) (hwidth : Li + Lk < 2 ^ Lw) (hk : k < 2 ^ Lk)
    (hi : i + input.length ≤ 2 ^ Li)
    (hfit : ∀ j < input.length, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = input.map bitSymbol) (hindex : S.R (rg 0) = binSyms Li i)
    (hstride : S.R (rg 1) = binSyms Lk k) (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = [])
    (hwidthInput : S.R (zr .width) = binSyms Lw (Li + Lk))
    (hunary : S.R (zr .unary) = []) (hzeroScratch : ∀ r, S.R (zr (.scratch r)) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ input.length * optionalAffineSourceIterationCost Lw Li Lk + 2 * input.length +
        2 * (input.length * (Li + Lk + 3)) + 16 * Li + 22 ∧
      Exec body (optionalAffineSourceGenerateProgram rg zr src saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (optionalAffineSourceWord Li Lk i k o input ++ S.R dst) }) := by
  have hn := hreg
  regs_ne hn
  have hcopy : [rg 0, savedIndex, rg 8, rg 9].Nodup := by
    simp [List.nodup_cons, hrg.eq_iff, hisep, (hisep 0).symm]
  obtain ⟨v₁, hu₁, hx₁⟩ := bcopy_exec body hcopy v S
    (hblank 8 (by decide) (by decide) (by decide)) (hblank 9 (by decide) (by decide) (by decide))
  rw [hindex, hsavedIndex, List.append_nil, length_binSyms] at hx₁
  let S₁ : Stacks T A := { S with R := Function.update S.R savedIndex (binSyms Li i) }
  have hrkeep (r : Fin 12) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hisep r).symm _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := optionalAffineSourceCompile_exec body rg hrg zr hzr hdst src saved accum dst
    (by regs_nodup) hcsep hssep hasep hdsep hcz hsz haz hzIndex Lw Li Lk i k o input hwidth hk hi hfit v₁ S₁
    (by simp [S₁, ‹src ≠ savedIndex›, hsrc]) ((hrkeep 0).trans hindex)
    ((hrkeep 1).trans hstride) ((hrkeep 2).trans hoffset)
    (by simp [S₁, ‹saved ≠ savedIndex›, hsaved]) (by simp [S₁, ‹accum ≠ savedIndex›, haccum])
    (fun r h0 h1 h2 => (hrkeep r).trans (hblank r h0 h1 h2))
    (by simpa [S₁, (hiz .width).symm] using hwidthInput)
    (by simpa [S₁, (hiz .unary).symm] using hunary)
    (fun r => by simpa [S₁, (hiz (.scratch r)).symm] using hzeroScratch r)
  have hd : S₁.R dst = S.R dst := by simp [S₁, ‹dst ≠ savedIndex›]
  rw [hd] at hx₂
  let out := optionalAffineSourceWord (A := A) Li Lk i k o input ++ S.R dst
  let S₂ : Stacks T A := { S₁ with R := Function.update (Function.update S₁.R dst out) (rg 0) (binSyms Li (i + input.length)) }
  obtain ⟨v₃, hu₃, hx₃⟩ := sparseCursorRestore_exec body (rg 0) savedIndex (rg 8) (rg 9) hcopy
    Li (i + input.length) i v₂ S₂ (by simp [S₂])
    (by simp [S₂, S₁, hisep, ‹dst ≠ savedIndex›.symm])
    (by simp [S₂, S₁, hrg.eq_iff, (hdsep 8).symm, (hisep 8).symm, hblank 8 (by decide) (by decide) (by decide)])
    (by simp [S₂, S₁, hrg.eq_iff, (hdsep 9).symm, (hisep 9).symm, hblank 9 (by decide) (by decide) (by decide)])
  have hf : Function.update (Function.update S₂.R (rg 0) (binSyms Li i)) savedIndex [] = Function.update S.R dst out := by
    funext j
    by_cases hj : j = savedIndex
    · subst j; simp [‹dst ≠ savedIndex›.symm, hsavedIndex]
    · by_cases hc : j = rg 0
      · subst j; simp [hj, (hdsep 0).symm, hindex]
      · simp [S₂, S₁, Function.update_apply, hj, hc]
  rw [hf] at hx₃
  exact ⟨v₃, (6 * Li + 6) + (m₂ + (10 * Li + 10)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
