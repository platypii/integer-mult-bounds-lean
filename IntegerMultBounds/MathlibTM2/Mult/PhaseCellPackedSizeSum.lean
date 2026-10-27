module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedSizeLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedTableValues

/-! Sum clipped block sizes from runtime unary dimensions with a counted scan. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def packedSizeSum : Pr P 154 Q A U :=
  .seq packedSizeLoop (.seq (uclear 151) (uclear 152))

def packedSizeSumCost (N W start L : ℕ) : ℕ :=
  packedSizeLoopCost N W start L+((2*(L+start)+2)+(2*L+2))

theorem packedSizeSum_exec (N W start L : ℕ) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hN : (S.R 116).length = N) (hW : (S.R 94).length = W)
    (hcursor : (S.R 151).length = start) (hcount : (S.R 152).length = L)
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,153], S.R k = []) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ packedSizeSumCost N W start L ∧
      Exec body packedSizeSum (mk v S) steps
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R 152 []) 0
          (List.replicate (packedBandWordCount N W L start) tick++S.R 0))
          151 [])}) := by
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := packedSizeLoop_exec (body := body) N W start L v S hN hW hcursor hcount hfresh
  let output := List.replicate (packedBandWordCount N W L start) (tick : Fin (A+4))++S.R 0
  let S₁ : Stacks 154 A := {S with R := (Function.update (Function.update S.R 0 output)
    151 (List.replicate L tick++S.R 151))}
  obtain ⟨v₂,hu₂,he₂⟩ := uclear_exec body 151 v₁ S₁
  let S₂ : Stacks 154 A := {S₁ with R := Function.update S₁.R 151 []}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 152 v₂ S₂
  have hlen151 : (S₁.R 151).length = L+start := by simp [S₁,hcursor]
  have hlen152 : (S₂.R 152).length = L := by simpa [S₂,S₁] using hcount
  refine ⟨v₃,m₁+((2*(L+start)+2)+(2*L+2)),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add_right hm₁ _,
    (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by rw [hlen151,hlen152]) ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  by_cases hk0 : k = 0 <;> by_cases hk151 : k = 151 <;> by_cases hk152 : k = 152 <;>
    simp [S₂,S₁,output,hk0,hk151,hk152]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
