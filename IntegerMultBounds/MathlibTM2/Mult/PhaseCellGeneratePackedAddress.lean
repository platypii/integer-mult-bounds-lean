module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSuffixAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWithinAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedEntryAddress

/-! Generate a complete packed-entry word address from unary dimension and rank headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def generatePackedAddress : Pr P 154 Q A U := .seq packedSuffixAddress packedWithinAddress

def generatePackedAddressCost (n m W N : ℕ) : ℕ := packedSuffixAddressCost n W N+packedWithinAddressCost n m W N

theorem generatePackedAddress_exec (n m W N : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hn : (S.R 107).length = n) (hm : (S.R 108).length = m)
    (hW : (S.R 94).length = W) (hN : (S.R 116).length = N)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,151,152,153], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ generatePackedAddressCost n m W N ∧
      Exec body generatePackedAddress (mk v S) steps
        (mk v' {S with R := Function.update S.R 0 (List.replicate (packedEntryOffset N W n m) tick++S.R 0)}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedSuffixAddress_exec (body := body) n W N v S hn hW hN hfresh
  let laterWords := packedBandWordCount N W (N-(n+1)) (n+1)
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate laterWords tick++S.R 0)}
  obtain ⟨v₂,hu₂,he₂⟩ := packedWithinAddress_exec (body := body) n m W N v₁ S₁
    (by simpa [S₁] using hn) (by simpa [S₁] using hm)
    (by simpa [S₁] using hW) (by simpa [S₁] using hN) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  refine ⟨v₂,m₁+packedWithinAddressCost n m W N,hu₂.trans hu₁,Nat.add_le_add_right hm₁ _,
    (Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0
  · subst k
    simp only [Function.update_self,S₁]
    rw [← List.append_assoc,List.replicate_append_replicate]
    simp [packedEntryOffset,laterWords,Nat.add_comm]
  · simp [S₁,hk0]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
