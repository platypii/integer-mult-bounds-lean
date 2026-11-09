module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorWord
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorEntryStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFactorChoiceStock

/-! Actual factor words retain branch resources without charging numerical time as space. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 154 Q A U}

@[irreducible] def factorWordWorkspace (q n m W N : ℕ) : ℕ :=
  2*factorChoiceCost n m W N+(factorEntryWorkspace q n m W N+8*factorZeroEntryCost q)

theorem factorWord_exec_within {s : ℕ} [NeZero s] (B : Finset (ZMod s)) (q W n m : ℕ)
    (columns : List (ZMod s → GaussianInt)) (hlen : columns.length = B.card)
    (hformat : ColumnFamilyFormat (2*q+8) columns) (hA : 4 ≤ A)
    (tail : List (Fin (A+4))) (v : HS 154 Q A U) (S : Stacks 154 A)
    (hq : (S.R 119).length = q) (hW : (S.R 94).length = W) (hN : (S.R 116).length = B.card)
    (hcolumn : (S.R 107).length = n) (hrow : (S.R 108).length = m)
    (hsource : S.R 132 = bandTableWords A (2*q+8) B W columns 0++tail) (h0 : S.R 0 = [])
    (hfresh : ∀ k ∈ [(131 : Fin 154),134,135,136,137,138,151,152,153], S.R k = [])
    (hblank : ∀ r : Fin 154, 1 ≤ r.val → r.val < 7 → S.R r = []) (depth : ℕ) :
    ∃ v' steps, v'.user = v.user ∧ steps ≤ factorWordCost q n m W B.card ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+factorWordWorkspace q n m W B.card)
        depth factorWord (mk v S) steps
        (mk v' {S with R := (Function.update S.R 140
          (csyms A (2*q+8) (factorRankWord B W columns n m)++S.R 140))}) := by
  let S' : Stacks 154 A := {S with R := (Function.update S.R 140
    (csyms A (2*q+8) (factorRankWord B W columns n m)++S.R 140))}
  unfold factorWordWorkspace
  apply factorChoice_exec_within (body := body) factorEntry factorZeroEntry n m W B.card
    (factorEntryCost q n m W B.card+factorZeroEntryCost q)
    (factorEntryWorkspace q n m W B.card+8*factorZeroEntryCost q) depth S S' hcolumn hrow hW hN (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact hblank _ (by decide) (by decide)) ?_ v
  intro vi
  by_cases hv : FactorRankValid B.card W n m
  · obtain ⟨hn,hm,hnm,hmn⟩ := hv
    have hv : FactorRankValid B.card W n m := ⟨hn,hm,hnm,hmn⟩
    have hn' : n < columns.length := by omega
    have hmBand : m ∈ foldedBandIndices B.card W n := (mem_foldedBandIndices hn).mpr ⟨hm,hmn,hnm⟩
    obtain ⟨v',steps,hu,hs,he,hreal,hfit,hvalue⟩ := factorEntry_exec_within (body := body)
      B q W n m columns hlen hformat hA hn hmBand tail vi S hq hW hN hcolumn hrow hsource h0 hfresh hblank depth
    refine ⟨v',steps,hu,by omega,?_⟩
    have hz : factorRankWord B W columns n m = columns[n] (bFoldAt s B m) := by
      rw [factorRankWord,if_pos hv,List.getD_eq_getElem _ _ hn']
    have ht := he.mono (J := fun d z => mnSize z+d ≤ mnSize (mk vi S)+depth+
      (factorEntryWorkspace q n m W B.card+8*factorZeroEntryCost q)) (by intro d z hz; omega)
    simpa only [hv,ite_true,S',hz] using ht
  · obtain ⟨v',hu,he⟩ := factorZeroEntry_exec (body := body) q vi S hq
      (hfresh 131 (by simp)) (hfresh 134 (by simp)) (hfresh 135 (by simp))
    have hzero : mnNativePushBound 8 (factorZeroEntry (P := P) (Q := Q) (A := A) (U := U)) := by
      simp [factorZeroEntry,generateWordWidth,copyR,copyStep,ucopy,umulSym,scanR,drainR,popDo,
        keepIn,pushN,uclear,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    have ht := mn_native_exec_within he 8 hzero depth
      (mnSize (mk vi S)+depth+(factorEntryWorkspace q n m W B.card+8*factorZeroEntryCost q)) (by omega)
    exact ⟨v',factorZeroEntryCost q,hu,by omega,by simpa [hv,S',factorRankWord] using ht⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
