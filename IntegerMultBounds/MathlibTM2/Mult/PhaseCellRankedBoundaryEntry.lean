module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratePackedAddress
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBoundaryEntry

/-! Generate an entry address from folded ranks, copy its word and restore every borrowed control. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellMatrix

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

def rankedBoundaryEntry : Pr P 154 Q A U :=
  .seq generatePackedAddress (.seq (moveR 94 137 id) (.seq copyPackedWord
    (.seq (moveR 137 94 id) (uclear 0))))

def rankedBoundaryEntryCost (q n m W N : ℕ) : ℕ :=
  let address := packedEntryOffset N W n m
  generatePackedAddressCost n m W N+((2*W+2)+(copyPackedWordCost q address+((2*W+2)+(2*address+2))))

theorem rankedBoundaryEntry_exec {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) :
    let word := csyms A (2*q+8) (columns[n] (bFoldAt s B m))
    let S' : Stacks 154 A := {S with R := Function.update S.R 143 (word++S.R 143)}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ rankedBoundaryEntryCost q n m W B.card ∧
      Exec body rankedBoundaryEntry (mk v S) steps (mk v' S') ∧
      (value q (decodeWord ((S'.R 143).take (2*q+8)))).re =
        bandBoundaryTable B W (computedBoundaryTable A q (2*q+8) B columns)
          (bFoldAt s B m) (bFoldAt s B n) := by
  dsimp only
  let address := packedEntryOffset B.card W n m
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generatePackedAddress_exec (body := body) n m W B.card v S hcolumn hrow hW hN hfresh
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate address tick)}
  have he₁' : Exec body generatePackedAddress (mk v S) m₁ (mk v₁ S₁) := by simpa [S₁,address,h0] using he₁
  obtain ⟨v₂,hu₂,he₂⟩ := moveR_exec body 94 137 (by decide) id v₁ S₁
  let S₂ : Stacks 154 A := {S₁ with R := Function.update (Function.update S₁.R 94 []) 137 (S.R 94).reverse}
  have he₂' : Exec body (moveR 94 137 id) (mk v₁ S₁) (2*W+2) (mk v₂ S₂) := by
    simpa [S₂,S₁,movedR,hW,hfresh 137 (by simp)] using he₂
  obtain ⟨v₃,m₃,hu₃,hm₃,he₃,hread⟩ := packedBoundaryEntry_exec (body := body) B q W n m columns hlen hn hm tail v₂ S₂
    (by simpa [S₂,S₁] using hq) (by simp [S₂,S₁,address])
    (by simpa [S₂,S₁] using hsource) (by simp [S₂])
    (by simpa [S₂,S₁] using hfresh 135 (by simp)) (by
      intro r hr1 hr7
      have hr0 : r ≠ 0 := by omega
      have hr94 : r ≠ 94 := by omega
      have hr137 : r ≠ 137 := by omega
      simpa [S₂,S₁,hr0,hr94,hr137] using hblank r hr1 hr7)
  let word := csyms A (2*q+8) (columns[n] (bFoldAt s B m))
  let output := word++S.R 143
  let S₃ : Stacks 154 A := {S₂ with R := Function.update S₂.R 143 output}
  have he₃' : Exec body copyPackedWord (mk v₂ S₂) m₃ (mk v₃ S₃) := by simpa [S₃,S₂,S₁,output,word] using he₃
  obtain ⟨v₄,hu₄,he₄⟩ := moveR_exec body 137 94 (by decide) id v₃ S₃
  let S₄ : Stacks 154 A := {S₁ with R := Function.update S₁.R 143 output}
  have he₄' : Exec body (moveR 137 94 id) (mk v₃ S₃) (2*W+2) (mk v₄ S₄) := by
    convert he₄ using 1
    · simp [S₃,S₂,S₁,hW]
    · apply congrArg (mk v₄)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk94 : k = 94 <;> by_cases hk137 : k = 137 <;> by_cases hk143 : k = 143 <;>
        simp [S₄,S₃,S₂,S₁,movedR,hk94,hk137,hk143,hfresh 137 (by simp)]
  obtain ⟨v₅,hu₅,he₅⟩ := uclear_exec body 0 v₄ S₄
  let Sfinal : Stacks 154 A := {S with R := Function.update S.R 143 output}
  have he₅' : Exec body (uclear 0) (mk v₄ S₄) (2*address+2) (mk v₅ Sfinal) := by
    convert he₅ using 1
    · simp [S₄,S₁]
    · apply congrArg (mk v₅)
      refine Stacks.ext rfl rfl rfl ?_
      funext k
      by_cases hk0 : k = 0 <;> by_cases hk143 : k = 143 <;> simp [Sfinal,S₄,S₁,hk0,hk143,h0]
  refine ⟨v₅,m₁+((2*W+2)+(m₃+((2*W+2)+(2*address+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    Nat.add_le_add hm₁ (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _),
    Exec.seq he₁' (Exec.seq he₂' (Exec.seq he₃' (Exec.seq he₄' he₅'))),?_⟩
  simpa [S₃,S₂,S₁,Sfinal,output,word] using hread

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
