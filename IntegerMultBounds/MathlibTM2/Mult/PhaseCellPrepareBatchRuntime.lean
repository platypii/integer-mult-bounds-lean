module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSwapBatchPayload
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallBatchHeaders

/-! Route the raw batch RHS and install the grouped arithmetic ABI. Numerical
pages are retained; all temporary routing counts and construction headers go. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def prepareBatchRuntime : Pr P₀ 117 Q A U := .seq swapBatchPayload installBatchHeaders

def prepareBatchRuntimeCost (P N q l B L w : ℕ) : ℕ :=
  swapBatchPayloadCost B L w + installBatchHeadersCost P N q l B

theorem prepareBatchRuntime_exec (P N q l B L w : ℕ)
    (pre factors rhs tail : List (Fin (A+4))) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hP : (S.R 114).length = P) (hN : (S.R 101).length = N)
    (hq : (S.R 112).length = q) (hl : (S.R 109).length = l)
    (hB : (S.R 96).length = B) (hL : (S.R 103).length = L) (hw : (S.R 94).length = w)
    (hpre : pre.length = (3*(B*L)+1)*w) (hfactors : factors.length = B*L*w) (hrhs : rhs.length = B*L*w)
    (hsrc : S.R 110 = pre ++ (factors ++ (rhs ++ tail)))
    (hfresh : ∀ k ∈ [(97 : Fin 117), 98, 99, 100, 104, 105, 106, 107, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ prepareBatchRuntimeCost P N q l B L w ∧
      Exec body prepareBatchRuntime (mk v S) m
        (mk v' (batchHeaderBank { S with R := (Function.update S.R 110
          (pre ++ (rhs ++ (factors ++ tail)))) } q l B)) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := swapBatchPayload_exec (body := body) B L w pre factors rhs tail v S
    hB hL hw hpre hfactors hrhs hsrc (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals exact hfresh _ (by simp))
  let T : Stacks 117 A := { S with R := Function.update S.R 110 (pre ++ (rhs ++ (factors ++ tail))) }
  obtain ⟨v₂, hu₂, he₂⟩ := installBatchHeaders_exec (body := body) P N q l B v₁ T
    (by simpa [T] using hP) (by simpa [T] using hN) (by simpa [T] using hq)
    (by simpa [T] using hl) (by simpa [T] using hB) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl
      all_goals simpa [T] using hfresh _ (by simp))
  exact ⟨v₂, m₁ + installBatchHeadersCost P N q l B, hu₂.trans hu₁,
    by dsimp only [prepareBatchRuntimeCost]; omega, Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
