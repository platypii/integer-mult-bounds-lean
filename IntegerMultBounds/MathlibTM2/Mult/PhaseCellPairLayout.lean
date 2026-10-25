module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSplitPairs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackPairBanks

/-! Convert an interleaved pair page to the two coordinate orders used by the
cell arithmetic, restoring both temporary banks and every work counter. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def pairLayout : Pr P₀ 117 Q A U := .seq splitPairs packPairBanks

def pairLayoutCost (L w : ℕ) : ℕ := L * (46 * w + 45) + 28

theorem pairLayout_exec (w L : ℕ) (X Y : ℕ → GaussianInt)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A + 4)))
    (hw : (S.R 94).length = w) (hL : (S.R 103).length = L)
    (hsrc : S.R 110 = pairStream A w L X Y ++ tail)
    (hfresh : ∀ k ∈ [(96 : Fin 117), 104, 105, 106, 108], S.R k = []) :
    ∃ v' m, v'.user = v.user ∧ m ≤ pairLayoutCost L w ∧
      Exec body pairLayout (mk v S) m
        (mk v' { S with R := (Function.update S.R 110
          (cstream A w ((List.range L).reverse.map X) ++
            (cstream A w ((List.range L).map Y) ++ tail))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := splitPairs_exec (body := body) w L X Y v S tail hw hL hsrc
    (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hfresh _ (by simp))
  let S₁ : Stacks 117 A := { S with R := (Function.update (Function.update (Function.update S.R 110 tail)
    111 (cstream A w ((List.range L).reverse.map X) ++ S.R 111))
    113 (cstream A w ((List.range L).reverse.map Y) ++ S.R 113)) }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := packPairBanks_exec (body := body) w L X Y v₁ S₁ (S.R 111) (S.R 113)
    (by simpa [S₁] using hw) (by simpa [S₁] using hL) (by simp [S₁]) (by simp [S₁]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂, m₁ + m₂, hu₂.trans hu₁, ?_, (Exec.seq he₁ he₂).cast rfl ?_⟩
  · unfold pairLayoutCost packPairBanksCost at *
    nlinarith only [hm₁, hm₂]
  · congr 1
    ext1
    · rfl
    · rfl
    · rfl
    · funext k
      simp only [S₁, Function.update_apply]
      split_ifs <;> subst_vars <;> simp_all

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
