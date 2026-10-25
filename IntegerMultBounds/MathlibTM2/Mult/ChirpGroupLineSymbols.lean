module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpGroupTransfers
public import IntegerMultBounds.MathlibTM2.Mult.ChirpDimensionScope

/-! # Compute the shared raw-line symbol counter from retained s and w words

Reuse the source bank's zero slot after all consumer banks have been installed;
restore it immediately after copying the unary counter. Setup is paid once per group.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 640 Q A U}

def lineSymbolsSetup : Pr P 640 Q A U :=
  .seq (tblCompile source (.ins (.mul 14 11 13)))
    (.seq (tblUnaryCopies source [(13, lineSymbols)]) (tblCompile source (.ins (.zero 13))))

/-- Only the one shared line-length counter changes; the complete source bank is restored. -/
theorem lineSymbolsSetup_exec (W w s : ℕ) (hwW : w ≤ W) (hvol : s * w < 2 ^ W)
    (st : TblSt 16 A) (hs : st.val 14 = s) (hw : st.val 11 = w) (hz : st.val 13 = 0)
    (hfit : ∀ i, st.val i < 2 ^ W) (v : HS 640 Q A U) (S : Stacks 640 A)
    (hS : tblHolds source S (tblRho W (List.replicate W tick) (List.replicate w tick) st)) :
    ∃ v' n, v'.user = v.user ∧ n ≤ 2 * tblC W w + (6 * (s * w) + 11 * W + 7) ∧
      Exec body lineSymbolsSetup (mk v S) n
        (mk v' { S with R := Function.update S.R lineSymbols (List.replicate (s * w) tick ++ S.R lineSymbols) }) := by
  let τ := Function.update st.val (13 : Fin 16) (s * w)
  have hrun : TblDo A W w (.ins (.mul 14 11 13)) st
      (fun z => z.val = τ ∧ z.acc = st.acc ∧ ∀ i, z.val i < 2 ^ W) 1 := by
    apply TblDo.block [] (.mul 14 11 13)
    · simpa [tblFitsList, TblIns.fits, hs, hw] using hvol
    · refine ⟨?_, rfl, ?_⟩
      · simp [tblExactList, TblIns.exact, hs, hw, τ]
      · intro i
        by_cases hi : i = 13
        · subst i; simpa [tblExactList, TblIns.exact, hs, hw] using hvol
        · simpa [tblExactList, TblIns.exact, hi] using hfit i
  have hrestore (z : TblSt 16 A) (hv : z.val = τ) :
      TblDo A W w (.ins (.zero 13)) z (fun u => u.val = st.val ∧ u.acc = z.acc) 1 := by
    apply TblDo.block [] (.zero 13)
    · simp [tblFitsList, TblIns.fits]
    · refine ⟨?_, rfl⟩
      funext i
      by_cases hi : i = 13
      · subst i; simp [tblExactList, TblIns.exact, hz]
      · simp [tblExactList, TblIns.exact, hv, τ, hi]
  obtain ⟨v', n, hu, hn, he⟩ := tblComputedUnaryCopies_exec (body := body) source_inj
    (List.replicate W tick) (List.replicate w tick) (by simp) (by simp) hwW
    (.ins (.mul 14 11 13)) (.ins (.zero 13)) st τ 1 1 hrun hrestore hfit [(13, lineSymbols)]
    (by
      intro p hp r
      simp only [List.mem_singleton] at hp
      subst p
      intro h
      have hb := bank_range (ForwardBankPlacement.source r)
      have hv := congrArg Fin.val h
      change (bankTape (ForwardBankPlacement.source r)).val = 543 at hv
      omega) v S hS
  refine ⟨v', n, hu, ?_, ?_⟩
  · simpa [unaryCopiesCost, τ, Nat.add_assoc] using hn
  · simpa only [lineSymbolsSetup, unaryCopiesR, τ, Function.update_self] using he

end IntegerMultBounds.MathlibTM2.Mult.ShortConv.LinePlacement
