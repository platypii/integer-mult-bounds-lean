module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRankedBoundaryEntry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratePackedAddressStock

/-! Lookup of an actual packed table word retains the shared address-generation reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def rankedBoundaryEntryWorkspace (q n m W N : ℕ) : ℕ :=
  generatePackedAddressWorkspace n m W N+8*copyPackedWordCost q (packedEntryOffset N W n m)

theorem rankedBoundaryEntry_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(135 : Fin 154),136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    let word := csyms A (2*q+8) (columns[n] (bFoldAt s B m))
    let S' : Stacks 154 A := {S with R := Function.update S.R 143 (word++S.R 143)}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ rankedBoundaryEntryCost q n m W B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        rankedBoundaryEntryWorkspace q n m W B.card) depth rankedBoundaryEntry (mk v S) steps (mk v' S') ∧
      (value q (decodeWord ((S'.R 143).take (2*q+8)))).re =
        bandBoundaryTable B W (computedBoundaryTable A q (2*q+8) B columns)
          (bFoldAt s B m) (bFoldAt s B n) := by
  dsimp only
  let address := packedEntryOffset B.card W n m
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := generatePackedAddress_exec_within (body := body) n m W B.card v S hcolumn hrow hW hN hfresh depth
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 0 (List.replicate address tick)}
  have he₁' : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
      generatePackedAddressWorkspace n m W B.card) depth generatePackedAddress (mk v S) m₁ (mk v₁ S₁) := by simpa [S₁,address,h0] using he₁
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
  have hcopy : mnNativePushBound 8 (copyPackedWord (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [copyPackedWord,generateWordWidth,copyIndexedWord,copySlice,copyPrefix,copyR,copyStep,
      unaryProduct,transfer,transferAct,ucopy,umulSym,scanP,scanR,drainR,popDo,keepIn,
      pushN,popPush,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
  let bound := mnSize (mk v₁ S₁)+depth+8*copyPackedWordCost q address
  have ht₂ := moveR_within 94 137 id he₂' depth bound (by dsimp only [bound]; omega)
  have hmove := moveR_within 94 137 id he₂' depth (mnSize (mk v₁ S₁)+depth) (Nat.le_refl _)
  have ht₃ := mn_native_exec_within he₃' 8 hcopy depth bound (by
    have hm := Nat.mul_le_mul_left 8 hm₃
    have hb := hmove.final
    change mnSize (mk v₂ S₂)+depth ≤ mnSize (mk v₁ S₁)+depth at hb
    dsimp only [bound,address]
    omega)
  have ht₄ := moveR_within 137 94 id he₄' depth bound ht₃.final
  have ht₅ := mn_native_exec_within he₅' 0 (by
    simp [uclear,drainR,popDo,peekR,mnNativePushBound,mnActPush]) depth bound
    (by simpa only [Nat.zero_mul,Nat.add_zero] using ht₄.final)
  have htail := ExecWithin.seq ht₂ (ExecWithin.seq ht₃ (ExecWithin.seq ht₄ ht₅))
  have ht := (mn_seq_within_add he₁' htail).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+rankedBoundaryEntryWorkspace q n m W B.card)
    (by intro d z hz; unfold rankedBoundaryEntryWorkspace; exact hz)
  refine ⟨v₅,m₁+((2*W+2)+(m₃+((2*W+2)+(2*address+2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))),
    Nat.add_le_add hm₁ (Nat.add_le_add_left (Nat.add_le_add_right hm₃ _) _),
    ht,?_⟩
  simpa [S₃,S₂,S₁,Sfinal,output,word] using hread

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
