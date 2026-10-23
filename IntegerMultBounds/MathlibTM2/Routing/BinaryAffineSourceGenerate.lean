module

public import IntegerMultBounds.MathlibTM2.Routing.AffineSourceGenerate

/-! Generate a complete affine profile from binary count/index/stride/offset
operands. The unary count is generated and erased; only the output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

variable {T Q A : ℕ} {P U : Type}

def binaryAffineSourceGenerateProgram (rg : Fin 12 → Fin T) (src count saved accum dst savedIndex : Fin T) : Pr P T Q A U :=
  .seq (toUnary src count (rg 3) (rg 8) (rg 9))
    (.seq (affineSourceGenerateProgram rg count saved accum dst savedIndex) (bclear count))

def binaryAffineSourceGenerateCost (Lc Li Lk n : ℕ) :=
  (Lc * (4 * n + 11) + 2 * n + 6) +
    (n * affineSourceIterationCost Li Lk + 2 * n + 2 * (n * (Li + Lk + 3)) + 16 * Li + 22) + (2 * n + 2)

theorem binaryAffineSourceGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 12 → Fin T) (hrg : Function.Injective rg) (src count saved accum dst savedIndex : Fin T)
    (hreg : [src, count, saved, accum, dst, savedIndex].Nodup)
    (hsrcsep : ∀ r, src ≠ rg r) (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (Lc Li Lk n i k o : ℕ) (hn : n < 2 ^ Lc) (hk : k < 2 ^ Lk)
    (hi : i + n ≤ 2 ^ Li) (hfit : ∀ j < n, (i + j) * k + o < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lc n) (hindex : S.R (rg 0) = binSyms Li i)
    (hstride : S.R (rg 1) = binSyms Lk k) (hoffset : S.R (rg 2) = binSyms (Li + Lk) o)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 12, r ≠ 0 → r ≠ 1 → r ≠ 2 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ binaryAffineSourceGenerateCost Lc Li Lk n ∧
      Exec body (binaryAffineSourceGenerateProgram rg src count saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (affineSourceWord Li Lk i k o n ++ S.R dst) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := toUnary_exec (body := body) (a := src) (z := count) (w := rg 3) (t := rg 8) (t₂ := rg 9)
    (by simp [List.nodup_cons, hrg.eq_iff, hsrcsep, hcsep, ‹src ≠ count›]) hn v S hsrc
    (hblank 3 (by decide) (by decide) (by decide)) (hblank 8 (by decide) (by decide) (by decide))
    (hblank 9 (by decide) (by decide) (by decide))
  rw [hcount, List.append_nil] at hx₁
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate n tick) }
  have hkeep (r : Fin 12) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hcsep r).symm _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := affineSourceGenerate_exec body rg hrg count saved accum dst savedIndex
    (by regs_nodup) hcsep hssep hasep hdsep hisep Li Lk i k o (List.replicate n tick) hk
    (by simpa only [List.length_replicate] using hi) (by simpa only [List.length_replicate] using hfit) v₁ S₁
    (by simp [S₁]) ((hkeep 0).trans hindex) ((hkeep 1).trans hstride) ((hkeep 2).trans hoffset)
    (by simp [S₁, ‹count ≠ saved›.symm, hsaved]) (by simp [S₁, ‹count ≠ accum›.symm, haccum])
    (by simp [S₁, ‹count ≠ savedIndex›.symm, hsavedIndex])
    (fun r h0 h1 h2 => (hkeep r).trans (hblank r h0 h1 h2))
  have hd : S₁.R dst = S.R dst := by simp [S₁, ‹count ≠ dst›.symm]
  rw [List.length_replicate, hd] at hx₂
  simp only [List.length_replicate] at hm₂
  let out := affineSourceWord (A := A) Li Lk i k o n ++ S.R dst
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R dst out }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body count v₂ S₂
  have hc : S₂.R count = List.replicate n tick := by simp [S₂, S₁, ‹count ≠ dst›]
  have hf : Function.update S₂.R count [] = Function.update S.R dst out := by
    funext j
    by_cases hj : j = count
    · subst j; simp [‹count ≠ dst›, hcount]
    · simp [S₂, S₁, Function.update_apply, hj]
  rw [hf, hc, List.length_replicate] at hx₃
  exact ⟨v₃, m₁ + (m₂ + (2 * n + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryAffineSourceGenerateCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
