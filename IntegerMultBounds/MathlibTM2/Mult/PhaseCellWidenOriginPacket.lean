module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTakePrefix
public import IntegerMultBounds.MathlibTM2.Host.SSMul

/-! Widen one geometry packet for the numerical batch using only linear tape work. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Host.SS IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {U P : Type} {body : P → Pr P 117 Q A U}

def widenOriginPacket : Pr P 117 Q A U :=
  .seq (takePrefix 115 109 20 25 26)
    (.seq (padCopy 19 20 21 25 26 27 (bitSymbol false))
      (.seq (moveR 21 22 id) (uclear 20)))

theorem widenOriginPacket_exec (V W x : ℕ) (hx : x < 2^V) (hVW : V ≤ W)
    (v : HS 117 Q A U) (S : Stacks 117 A) (tail : List (Fin (A+4)))
    (hV : (S.R 115).length = V) (hW : (S.R 19).length = W)
    (hsrc : S.R 109 = binSyms V x++tail)
    (hfresh : ∀ k ∈ [(20 : Fin 117),21,25,26,27], S.R k = []) :
    ∃ v', v'.user = v.user ∧
      Exec body widenOriginPacket (mk v S) (8*W+10*V+18)
        (mk v' {S with R := (Function.update (Function.update S.R 109 tail) 22
          ((binSyms W x).reverse++S.R 22))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := takePrefix_exec (body := body)
    (show [(115 : Fin 117),109,20,25,26].Nodup by decide) v S (binSyms V x) tail hsrc
    (by simpa using hV) (hfresh 25 (by simp)) (hfresh 26 (by simp))
  let S₁ : Stacks 117 A := {S with R := Function.update (Function.update S.R 109 tail) 20 (binSyms V x)}
  have he₁' : Exec body (takePrefix 115 109 20 25 26) (mk v S) (6*V+6) (mk v₁ S₁) := by
    simpa [S₁,hfresh 20 (by simp)] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := padCopy_exec (body := body) (t := 21)
    (show Dist5 (19 : Fin 117) 25 20 26 27 by constructor <;> decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    (bitSymbol false) v₁ S₁
    (by simpa [S₁] using hfresh 25 (by simp))
    (by simpa [S₁] using hfresh 26 (by simp))
    (by simpa [S₁] using hfresh 27 (by simp)) (by simpa [S₁,hW] using hVW)
  let S₂ : Stacks 117 A := {S₁ with R := Function.update S₁.R 21 (binSyms W x)}
  have he₂' : Exec body (padCopy 19 20 21 25 26 27 (bitSymbol false)) (mk v₁ S₁)
      (6*W+2*V+8) (mk v₂ S₂) := by
    simpa [S₂,S₁,hW,hfresh 21 (by simp),binSyms_append_replicate hx hVW] using he₂
  obtain ⟨v₃,hu₃,he₃⟩ := moveR_exec (body := body) 21 22 (by decide) id v₂ S₂
  let S₃ : Stacks 117 A := {S₂ with R := movedR S₂.R 21 22 id (S₂.R 21)}
  have he₃' : Exec body (moveR 21 22 id) (mk v₂ S₂) (2*W+2) (mk v₃ S₃) := by
    simpa [S₃,S₂] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := uclear_exec (body := body) 20 v₃ S₃
  refine ⟨v₄,hu₄.trans (hu₃.trans (hu₂.trans hu₁)),
    (Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' he₄))).cast ?_ ?_⟩
  · simp [S₃,S₂,S₁,movedR]
    omega
  · apply congrArg (mk v₄)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp only [S₃,S₂,S₁,movedR,Function.update_apply,List.map_id]
    split_ifs <;> simp_all [hfresh]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
