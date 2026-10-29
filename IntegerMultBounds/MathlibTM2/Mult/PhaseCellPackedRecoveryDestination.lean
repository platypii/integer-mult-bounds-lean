module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLine
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Release the owned first-pass interior buffer and retain its local row count
for boundary publication. The boundary stream and coefficient page are framed. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedRecoveryDestination : Pr P 248 Q A U :=
  .seq (toUnary 165 246 0 1 2) (retireCountedLine 246 174 132 247 242 243)

def packedRecoveryDestinationCost (V N w : ℕ) : ℕ :=
  6*N+11*V+6+retireCountedLineCost N w

theorem packedRecoveryDestination_exec (V N w : ℕ) (hNV : N < 2^V)
    (words tail : List (Fin (A+4))) (hlen : words.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hw : (S.R 174).length = w)
    (hsrc : S.R 132 = words++tail)
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ packedRecoveryDestinationCost V N w ∧
      Exec body packedRecoveryDestination (mk v S) n
        (mk v' {S with R := (Function.update (Function.update S.R 246
          (List.replicate N tick)) 132 tail)}) := by
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := toUnary_exec_linear (body := body)
    (a := 165) (z := 246) (w := 0) (t := 1) (t₂ := 2) (by decide) hNV v S hN
    (hclean 0 (by decide)) (hclean 1 (by decide)) (hclean 2 (by decide))
  let S₁ : Stacks 248 A := {S with R := Function.update S.R 246 (List.replicate N tick)}
  have he₁' : Exec body (toUnary 165 246 0 1 2) (mk v S) n₁ (mk v₁ S₁) := by
    simpa only [hclean 246 (by decide),List.append_nil] using he₁
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := retireCountedLine_exec (body := body)
    246 174 132 247 242 243 (by decide) N w words tail hlen v₁ S₁
    (by simp [S₁]) (by simpa [S₁] using hw) (by simpa [S₁] using hsrc)
    (by simpa [S₁] using hclean 247 (by decide))
    (by simpa [S₁] using hclean 242 (by decide))
    (by simpa [S₁] using hclean 243 (by decide))
  exact ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,Exec.seq he₁' he₂⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
