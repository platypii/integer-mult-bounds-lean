module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorEntry
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRankedBoundaryEntryStock

/-! Feed an actual looked-up word to the factor input page with its resource trace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def factorEntryWorkspace (q n m W N : ℕ) : ℕ :=
  rankedBoundaryEntryWorkspace q n m W N+8*feedFactorWordCost q

theorem factorEntry_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card) (hformat : ColumnFamilyFormat (2*q+8) columns)
    (hA : 4 ≤ A) (hn : n < B.card) (hm : m ∈ foldedBandIndices B.card W n)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    let word := csyms A (2*q+8) (columns[n] (bFoldAt s B m))
    let S' : Stacks 154 A := {S with R := Function.update S.R 140 (word++S.R 140)}
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorEntryCost q n m W B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorEntryWorkspace q n m W B.card)
        depth factorEntry (mk v S) steps (mk v' S') ∧
      (columns[n] (bFoldAt s B m)).im = 0 ∧ Fits (2*q+8) (columns[n] (bFoldAt s B m)) ∧
      (value q (columns[n] (bFoldAt s B m))).re =
        bandBoundaryTable B W (computedBoundaryTable A q (2*q+8) B columns)
          (bFoldAt s B m) (bFoldAt s B n) := by
  dsimp only
  have hn' : n < columns.length := by omega
  let z := columns[n] (bFoldAt s B m)
  have hzreal : z.im = 0 := (hformat columns[n] (List.getElem_mem hn')).1 _
  have hzfit : Fits (2*q+8) z := (hformat columns[n] (List.getElem_mem hn')).2 _
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hread⟩ := rankedBoundaryEntry_exec_within (body := body)
    B q W n m columns hlen hn hm tail v S hq hW hN hcolumn hrow hsource h0 (by
      intro k hk
      exact hfresh k (by simp only [List.mem_cons,List.not_mem_nil,or_false] at hk ⊢; tauto)) hblank depth
  let word := csyms A (2*q+8) z
  let S₁ : Stacks 154 A := {S with R := Function.update S.R 143 (word++S.R 143)}
  obtain ⟨v₂,hu₂,he₂⟩ := feedFactorWord_exec (body := body) q z (S.R 143) v₁ S₁
    (by simpa [S₁] using hq) (by simp [S₁,word]) (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl <;> simpa [S₁] using hfresh _ (by simp))
  let Sfinal : Stacks 154 A := {S with R := Function.update S.R 140 (word++S.R 140)}
  have he₂' : Exec body feedFactorWord (mk v₁ S₁) (feedFactorWordCost q) (mk v₂ Sfinal) := by
    convert he₂ using 1
    apply congrArg (mk v₂)
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    by_cases hk140 : k = 140 <;> by_cases hk143 : k = 143 <;> simp [Sfinal,S₁,word,hk140,hk143]
  have hfeed : mnNativePushBound 8 (feedFactorWord (P := P) (Q := Q) (A := A) (U := U)) := by
    simp [feedFactorWord,generateWordWidth,movePrefix,transfer,transferAct,ucopy,umulSym,
      scanR,drainR,popDo,keepIn,pushN,uclear,moveR,moveStep,whileR,peekR,
      mnNativePushBound,mnActPush]
  have ht₂ := mn_native_exec_within he₂' 8 hfeed depth _ (Nat.le_refl _)
  have ht := (mn_seq_within_add he₁ ht₂).mono
    (J := fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorEntryWorkspace q n m W B.card)
    (by intro d z hz; unfold factorEntryWorkspace; exact hz)
  refine ⟨v₂,m₁+feedFactorWordCost q,hu₂.trans hu₁,Nat.add_le_add_right hm₁ _,ht,hzreal,hzfit,?_⟩
  have hd : decodeWord (csyms A (2*q+8) z) = z := decodeWord_of_fits hA (by omega) z hzfit
  simpa [S₁,word,z,List.take_append,hd] using hread

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
