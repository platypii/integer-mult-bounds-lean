module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedRecoveryDestination
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellMaskedPackedBoundaryPublish

/-! Replace the first interior output with the local boundary field using the
selector mask already generated for boundary RHS extraction. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 248 Q A U}

def packedRecoveryBoundaryBuffer : Pr P 248 Q A U :=
  .seq packedRecoveryDestination maskedPackedBoundaryPublish

theorem packedRecoveryBoundaryBuffer_exec {s t origin N : ℕ} [NeZero s]
    (hst : s < t) (hA : 4 ≤ A) (V band a b w : ℕ) (hNV : N < 2^V)
    (hb : b ≤ s) (hfit : origin+N ≤ s)
    (hB : ∀ i ∈ haloBoundary s t band a b, origin ≤ i.val ∧ i.val < origin+N)
    (G : ZMod s → GaussianInt) (hoff : ∀ i ∉ haloBoundary s t band a b, G i = 0)
    (words tail : List (Fin (A+4))) (hlen : words.length = N*w)
    (v : HS 248 Q A U) (S : Stacks 248 A)
    (hN : S.R 165 = binSyms V N) (hwidth : (S.R 174).length = w)
    (hsrc : S.R 245 = cstream A w ((bOrder s (haloBoundary s t band a b)).map G))
    (hmask : S.R 167 = couplingSourceIntervalMaskSymbols true A s t band a b origin N)
    (houtput : S.R 132 = words++tail)
    (hclean : ∀ i ∈ ([0,1,2,246,247,242,243,244] : List (Fin 248)), S.R i = []) :
    ∃ v' n, v'.user = v.user ∧
      n ≤ packedRecoveryDestinationCost V N w+(N*(6*w+10)+6) ∧
      Exec body packedRecoveryBoundaryBuffer (mk v S) n
        (mk v' {S with R := (Function.update (Function.update (Function.update S.R
          246 (List.replicate N tick)) 245 []) 132
          (cstream A w (packedInterval origin N G)++tail))}) := by
  have hcleanD : ∀ i ∈ ([0,1,2,246,247,242,243] : List (Fin 248)), S.R i = [] := by
    intro i hi
    exact hclean i (List.mem_append_left [244] hi)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := packedRecoveryDestination_exec V N w hNV words tail
    hlen v S hN hwidth houtput hcleanD
  let S₁ : Stacks 248 A := {S with R := (Function.update (Function.update S.R
    246 (List.replicate N tick)) 132 tail)}
  have hclean₁ : ∀ i ∈ ([242,243,244] : List (Fin 248)), S₁.R i = [] := by
    intro i hi
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl <;> simpa [S₁] using hclean _ (by decide)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := maskedPackedBoundaryPublish_exec hst hA band a b hb hfit hB G hoff
    w [] v₁ S₁ (by simpa [S₁] using hsrc) (by simpa [S₁] using hmask)
    (by simpa [S₁] using hwidth) hclean₁
  refine ⟨v₂,n₁+n₂,hu₂.trans hu₁,Nat.add_le_add hn₁ hn₂,(Exec.seq he₁ he₂).cast rfl ?_⟩
  apply congrArg (mk v₂)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases h132 : i = 132 <;> by_cases h245 : i = 245 <;>
    simp [S₁,h132,h245]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
