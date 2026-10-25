module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleaseCellRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBatchRuntimeRegisters
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBranchWords

/-! Complete grouped teardown by treating the retained page as one flat row.
Only the owned row-count header is replaced; existing structural page-release
lemmas then restore the RHS and erase the numerical data without a new parser. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def releaseBatchRuntime : Pr P₀ 117 Q A U :=
  .seq (uclear 102) (.seq (branchWords 108 107 96 103 102 104 105)
    (.seq releaseRuntimePages (clearWords [100, 101, 102, 103, 108])))

def releaseBatchRuntimeCost (B L q l : ℕ) : ℕ :=
  (2*L+2) + (4*(B*L)+17*B+10) + releaseRuntimePagesCost (B*L) q +
    2*(q+l+B*L+L+2*B)+11

theorem releaseBatchRuntime_exec (B L q l : ℕ) (gen outs rhs factors borrowed result : List (Fin (A+4)))
    (v : HS 117 Q A U) (S : Stacks 117 A)
    (hL : ∀ k, S.L k = [])
    (hR : ∀ k, S.R k = batchRuntimeRegisters q l B L
      (gen ++ (outs ++ (rhs ++ (factors ++ borrowed)))) result k)
    (hgen : gen.length = (2*(B*L)+1)*(2*q+8))
    (houts : outs.length = B*L*(2*q+8)) (hrhs : rhs.length = B*L*(2*q+8))
    (hfactors : factors.length = B*L*(2*q+8)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ releaseBatchRuntimeCost B L q l ∧
      Exec body releaseBatchRuntime (mk v S) m
        (mk v' (releasedCellBank rhs borrowed result S.inp S.out)) := by
  obtain ⟨v₁, hu₁, he₁⟩ := uclear_exec body 102 v S
  let S₁ : Stacks 117 A := { S with R := Function.update S.R 102 [] }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := branchWords_exec (body := body)
    (show [(108 : Fin 117), 107, 96, 103, 102, 104, 105].Nodup by decide) B L v₁ S₁
    (by simp [S₁, hR, batchRuntimeRegisters]) (by simp [S₁, hR, batchRuntimeRegisters]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl
      all_goals simp [S₁, hR, batchRuntimeRegisters])
  let S₂ : Stacks 117 A := { S₁ with R := Function.update S₁.R 102 (List.replicate (B*L) tick) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := releaseRuntimePages_exec (body := body) (B*L) q
    gen outs rhs factors borrowed v₂ S₂ (by simp [S₂])
    (by simp [S₂, S₁, hR, batchRuntimeRegisters]) (by simp [S₂, S₁, hR, batchRuntimeRegisters])
    hgen houts hrhs hfactors (by simp [S₂, S₁, hR, batchRuntimeRegisters]) (by
      intro k hk
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals simp [S₂, S₁, hR, batchRuntimeRegisters])
  let S₃ : Stacks 117 A := { S₂ with R := (Function.update (Function.update S₂.R 94 []) 110 (rhs ++ borrowed)) }
  obtain ⟨v₄, hu₄, he₄⟩ := clearWords_exec (body := body)
    [(100 : Fin 117), 101, 102, 103, 108] (by decide) v₃ S₃
  have h102 : (S.R 102).length = L := by simp [hR, batchRuntimeRegisters]
  have hsum : ([(100 : Fin 117), 101, 102, 103, 108].map (fun k => (S₃.R k).length)).sum =
      q+l+B*L+L+2*B := by
    simp [S₃, S₂, S₁, hR, batchRuntimeRegisters]
    omega
  refine ⟨v₄, (2*L+2) + (m₂ + (m₃ + (2*(q+l+B*L+L+2*B)+11))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by dsimp only [releaseBatchRuntimeCost]; omega,
    (Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))).cast (by rw [h102, hsum]; rfl) ?_⟩
  congr 1
  ext1
  · rfl
  · rfl
  · funext k; exact hL k
  · funext k
    by_cases h93 : k.val = 93
    · have he : k = 93 := Fin.ext h93
      subst k; simp [S₃, S₂, S₁, hR, batchRuntimeRegisters, releasedCellBank]
    by_cases h110 : k.val = 110
    · have he : k = 110 := Fin.ext h110
      subst k; simp [S₃, releasedCellBank]
    simp [S₃, S₂, S₁, hR, batchRuntimeRegisters, releasedCellBank,
      Function.update_apply, Fin.ext_iff, h93, h110]
    intro h100 h101 h102 h103 h108 h94
    simp [h100, h101, h102, h103, h108, h94]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
