module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicateGeneratorBanks
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackRepeatedGenerators

/-! Expand one generated inverse page to the grouped caller's two repeated banks
and shared scalar. All original borrowed suffixes and temporary stacks return. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def replicateGenerators : Pr P₀ 117 Q A U := .seq replicateGeneratorBanks packRepeatedGenerators

def replicateGeneratorsCost (B L w : ℕ) : ℕ :=
  38 * (B * (L * w)) + 38 * (L * w) + 28 * w + 9 * L + 39 * B + 77

theorem replicateGenerators_exec (B L w : ℕ) (xs ys a tail : List (Fin (A + 4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hbatch : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hxs : xs.length = L * w) (hys : ys.length = L * w) (ha : a.length = w)
    (hsrc : S.R 110 = xs ++ (ys ++ (a ++ tail)))
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ replicateGeneratorsCost B L w ∧
      Exec body replicateGenerators (mk v S) m
        (mk v' { S with R := (Function.update S.R 110
          ((List.replicate B xs).flatten ++ ((List.replicate B ys).flatten ++ (a ++ tail)))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := replicateGeneratorBanks_exec (body := body) B L w xs ys a tail v S
    hbatch hL hw hxs hys ha hsrc (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update (Function.update S.R
    99 (List.replicate (L * w) tick)) 106 a) 111 ((List.replicate B xs).flatten ++ S.R 111))
    113 ((List.replicate B ys).flatten ++ S.R 113)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := packRepeatedGenerators_exec (body := body) B L w xs ys a tail
    (S.R 111) (S.R 113) v₁ S₁ (by simpa [S₁] using hbatch) (by simp [S₁])
    (by simpa [S₁] using hw) hxs hys ha (by simpa [S₁] using hsrc)
    (by simp [S₁]) (by simp [S₁]) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · unfold replicateGeneratorsCost replicateGeneratorBanksCost packRepeatedGeneratorsCost at *
    omega
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      by_cases hk99 : k = 99
      · subst k; simp [S₁, hfresh 99 (by simp)]
      by_cases hk106 : k = 106
      · subst k; simp [S₁, hfresh 106 (by simp)]
      simp only [S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
