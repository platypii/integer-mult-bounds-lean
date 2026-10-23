module

public import IntegerMultBounds.MathlibTM2.Routing.CounterSourceGenerate

/-! Generate consecutive source selectors from binary count and index
operands. The unary count is generated and erased; only the output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing

open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Node (tick)

variable {T Q A : ℕ} {P U : Type}

def binaryCounterSourceGenerateProgram (rg : Fin 5 → Fin T) (src count saved accum dst savedIndex : Fin T) : Pr P T Q A U :=
  .seq (toUnary src count (rg 1) (rg 2) (rg 3))
    (.seq (counterSourceGenerateProgram rg count saved accum dst savedIndex) (bclear count))

def binaryCounterSourceGenerateCost (Lc L n : ℕ) :=
  (Lc * (4 * n + 11) + 2 * n + 6) +
    (n * counterSourceIterationCost L + 2 * n + 2 * (n * (L + 3)) + 16 * L + 22) + (2 * n + 2)

theorem binaryCounterSourceGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 5 → Fin T) (hrg : Function.Injective rg) (src count saved accum dst savedIndex : Fin T)
    (hreg : [src, count, saved, accum, dst, savedIndex].Nodup)
    (hsrcsep : ∀ r, src ≠ rg r) (hcsep : ∀ r, count ≠ rg r) (hssep : ∀ r, saved ≠ rg r)
    (hasep : ∀ r, accum ≠ rg r) (hdsep : ∀ r, dst ≠ rg r) (hisep : ∀ r, savedIndex ≠ rg r)
    (Lc L n i : ℕ) (hn : n < 2 ^ Lc)
    (v : HS T Q A U) (S : Stacks T A)
    (hsrc : S.R src = binSyms Lc n) (hindex : S.R (rg 0) = binSyms L i)
    (hcount : S.R count = []) (hsaved : S.R saved = []) (haccum : S.R accum = []) (hsavedIndex : S.R savedIndex = [])
    (hblank : ∀ r : Fin 5, r ≠ 0 → S.R (rg r) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ binaryCounterSourceGenerateCost Lc L n ∧
      Exec body (binaryCounterSourceGenerateProgram rg src count saved accum dst savedIndex) (mk v S) steps
        (mk v' { S with R := Function.update S.R dst (counterSourceWord L i n ++ S.R dst) }) := by
  have hregs := hreg
  regs_ne hregs
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := toUnary_exec (body := body) (a := src) (z := count) (w := rg 1) (t := rg 2) (t₂ := rg 3)
    (by simp [List.nodup_cons, hrg.eq_iff, hsrcsep, hcsep, ‹src ≠ count›]) hn v S hsrc
    (hblank 1 (by decide)) (hblank 2 (by decide))
    (hblank 3 (by decide))
  rw [hcount, List.append_nil] at hx₁
  let S₁ : Stacks T A := { S with R := Function.update S.R count (List.replicate n tick) }
  have hkeep (r : Fin 5) : S₁.R (rg r) = S.R (rg r) := Function.update_of_ne (hcsep r).symm _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := counterSourceGenerate_exec body rg hrg count saved accum dst savedIndex
    (by regs_nodup) hcsep hssep hasep hdsep hisep L i (List.replicate n tick) v₁ S₁
    (by simp [S₁]) ((hkeep 0).trans hindex)
    (by simp [S₁, ‹count ≠ saved›.symm, hsaved]) (by simp [S₁, ‹count ≠ accum›.symm, haccum])
    (by simp [S₁, ‹count ≠ savedIndex›.symm, hsavedIndex])
    (fun r h0 => (hkeep r).trans (hblank r h0))
  have hd : S₁.R dst = S.R dst := by simp [S₁, ‹count ≠ dst›.symm]
  rw [List.length_replicate, hd] at hx₂
  simp only [List.length_replicate] at hm₂
  let out := counterSourceWord (A := A) L i n ++ S.R dst
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
    by unfold binaryCounterSourceGenerateCost; omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
