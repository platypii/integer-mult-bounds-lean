module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRhsSeed

/-! # Generate the iteration-scaled RHS and its exponent header

The exponent P*(n+1) is computed from ordinary P/n headers, used for seed
emission, and released. Only the RHS prefix changes, including for empty rows.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {T Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ T Q A U}

def generateIterationRhs (rows width precision iteration dst exponent rowRest count saved savedPrefix tmp : Fin T) :
    Pr P₀ T Q A U :=
  .seq (unaryProduct precision iteration exponent saved tmp)
    (.seq (ucopy precision exponent saved)
      (.seq (generateRhsPage rows width exponent dst rowRest count saved savedPrefix tmp) (uclear exponent)))

theorem generateIterationRhs_exec {rows width precision iteration dst exponent rowRest count saved savedPrefix tmp : Fin T}
    (hreg : [rows, width, precision, iteration, dst, exponent, rowRest, count, saved, savedPrefix, tmp].Nodup)
    (L W P n : ℕ) (hscale : P * (n + 1) < W) (v : HS T Q A U) (S : Stacks T A)
    (hrows : (S.R rows).length = L) (hwidth : (S.R width).length = W)
    (hprecision : (S.R precision).length = P) (hiteration : (S.R iteration).length = n)
    (hexponent : S.R exponent = []) (hrest : S.R rowRest = []) (hcount : S.R count = [])
    (hsaved : S.R saved = []) (hprefix : S.R savedPrefix = []) (htmp : S.R tmp = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ 10 * (L * W) + 15 * L + 12 * (P * n) + 21 * P + 49 ∧
      Exec body (generateIterationRhs rows width precision iteration dst exponent rowRest count saved savedPrefix tmp)
        (mk v S) m (mk v' { S with R := (Function.update S.R dst
          (cstream A W ((seedWords (P * (n + 1)) L).reverse) ++ S.R dst)) }) := by
  have hreg' := hreg
  regs_ne hreg'
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := unaryProduct_exec (body := body)
    (show [precision, iteration, exponent, saved, tmp].Nodup by regs_nodup) v S hsaved htmp
  let S₁ : Stacks T A := { S with R := Function.update S.R exponent (List.replicate (P * n) tick) }
  have he₁' : Exec body (unaryProduct precision iteration exponent saved tmp) (mk v S) m₁ (mk v₁ S₁) := by
    simpa only [hprecision, hiteration, hexponent, List.append_nil] using he₁
  obtain ⟨v₂, hu₂, he₂⟩ := ucopy_exec (body := body) ‹precision ≠ exponent› ‹precision ≠ saved›
    ‹exponent ≠ saved› v₁ S₁ (by simpa [S₁, ‹exponent ≠ saved›.symm] using hsaved)
  let S₂ : Stacks T A := { S₁ with R := Function.update S₁.R exponent (List.replicate (P * (n + 1)) tick) }
  have hsize : P + P * n = P * (n + 1) := by ring
  have he₂' : Exec body (ucopy precision exponent saved) (mk v₁ S₁) (4 * P + 4) (mk v₂ S₂) := by
    simpa [S₂, S₁, ‹precision ≠ exponent›, hprecision, List.replicate_append_replicate, hsize] using he₂
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := generateRhsPage_exec (body := body)
    (show [rows, width, exponent, dst, rowRest, count, saved, savedPrefix, tmp].Nodup by regs_nodup)
    L W (P * (n + 1)) hscale v₂ S₂
    (by simpa [S₂, S₁, ‹rows ≠ exponent›] using hrows)
    (by simpa [S₂, S₁, ‹width ≠ exponent›] using hwidth) (by simp [S₂])
    (by simpa [S₂, S₁, ‹exponent ≠ rowRest›.symm] using hrest)
    (by simpa [S₂, S₁, ‹exponent ≠ count›.symm] using hcount)
    (by simpa [S₂, S₁, ‹exponent ≠ saved›.symm] using hsaved)
    (by simpa [S₂, S₁, ‹exponent ≠ savedPrefix›.symm] using hprefix)
    (by simpa [S₂, S₁, ‹exponent ≠ tmp›.symm] using htmp)
  let S₃ : Stacks T A := { S₂ with R := (Function.update S₂.R dst
    (cstream A W ((seedWords (P * (n + 1)) L).reverse) ++ S₂.R dst)) }
  obtain ⟨v₄, hu₄, he₄⟩ := uclear_exec body exponent v₃ S₃
  have hexp₃ : (S₃.R exponent).length = P * (n + 1) := by simp [S₃, S₂, ‹dst ≠ exponent›.symm]
  refine ⟨v₄, m₁ + ((4 * P + 4) + (m₃ + (2 * (P * (n + 1)) + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, ?_⟩
  · rw [hprecision, hiteration] at hm₁
    nlinarith only [hm₁, hm₃]
  · refine (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃ he₄))).cast (by rw [hexp₃]) ?_
    congr 1
    ext1
    · rfl
    · rfl
    · rfl
    funext k
    by_cases hd : k = dst
    · subst k
      simp [S₃, S₂, S₁, ‹dst ≠ exponent›]
    by_cases he : k = exponent
    · subst k
      simp [hexponent, ‹dst ≠ exponent›.symm]
    simp [S₃, S₂, S₁, hd, he]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
