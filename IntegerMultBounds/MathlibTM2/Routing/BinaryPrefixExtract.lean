module

public import IntegerMultBounds.MathlibTM2.Mult.ShortConvSlice
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Copy a prefix whose length is supplied in binary. The unary traversal count
is constructed and erased inside the program, with every source and scratch restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {T Q A : ℕ} {P U : Type}

def binaryPrefixExtractProgram (rg : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (toUnary (rg 0) (rg 1) (rg 2) (rg 3) (rg 4))
    (.seq (copyPrefix (rg 1) (rg 5) (rg 6) (rg 7) (rg 3)) (bclear (rg 1)))

def binaryPrefixExtractCost (L N : ℕ) := L * (4 * N + 11) + 14 * N + 18

theorem binaryPrefixExtract_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (L : ℕ)
    (xs rest : List (Fin (A + 4))) (hfit : xs.length < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R (rg 0) = binSyms L xs.length) (hinput : S.R (rg 5) = xs ++ rest)
    (hblank : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ binaryPrefixExtractCost L xs.length ∧
      Exec body (binaryPrefixExtractProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 6) (xs ++ S.R (rg 6)) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := toUnary_exec body
    (a := rg 0) (z := rg 1) (w := rg 2) (t := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) hfit v S hcount
    (hblank 2 (by simp)) (hblank 3 (by simp)) (hblank 4 (by simp))
  rw [hblank 1 (by simp), List.append_nil] at he₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 1) (List.replicate xs.length IntegerMultBounds.MathlibTM2.Node.tick) }
  obtain ⟨v₂, hu₂, he₂⟩ := copyPrefix_exec (body := body)
    (count := rg 1) (src := rg 5) (dst := rg 6) (saved := rg 7) (tmp := rg 3)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ G xs rest
    (by simpa [G, hrg.eq_iff] using hinput) (by simp [G])
    (by simpa [G, hrg.eq_iff] using hblank 7 (by simp))
    (by simpa [G, hrg.eq_iff] using hblank 3 (by simp))
  have hdst : G.R (rg 6) = S.R (rg 6) := by simp [G, hrg.eq_iff]
  rw [hdst] at he₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 6) (xs ++ S.R (rg 6)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec body (rg 1) v₂ H
  have hc : (H.R (rg 1)).length = xs.length := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 1) [] = Function.update S.R (rg 6) (xs ++ S.R (rg 6)) := by
    funext j
    by_cases h1 : j = rg 1
    · subst j; simp [hrg.eq_iff, hblank 1 (by simp)]
    by_cases h6 : j = rg 6
    · subst j; simp [H, G, h1]
    · simp [H, G, h1, h6]
  rw [hc, hf] at he₃
  exact ⟨v₃, m₁ + ((10 * xs.length + 10) + (2 * xs.length + 2)), hu₃.trans (hu₂.trans hu₁),
    by unfold binaryPrefixExtractCost; omega, Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
