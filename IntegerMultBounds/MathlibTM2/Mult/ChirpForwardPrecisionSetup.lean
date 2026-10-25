module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpForwardWindow
public import IntegerMultBounds.MathlibTM2.Fast.TableProg

/-! # Execute the selected forward growth, precision and signed word widths

Only p and the ring logarithm are inputs. The fixed arithmetic program derives
Γ, q and both word widths; its fits require only room for the largest result.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpForwardPrecision : TblCode 6 :=
  .seq (tblBlock 6 [.copy 0 2, .add 2 2 2, .add 2 2 2, .add 2 2 2, .add 2 2 2] (.add 2 2 2))
    (.seq (tblBlock 6 ([.add 2 2 3, .add 3 0 3, .add 3 1 3] ++ List.replicate 12 (.inc 3)) (.inc 3))
      (.seq (tblBlock 6 ([.add 3 1 4, .add 4 2 4] ++ List.replicate 4 (.inc 4)) (.inc 4))
        (tblBlock 6 ([.add 0 1 5, .add 5 2 5] ++ List.replicate 4 (.inc 5)) (.inc 5))))

def chirpForwardPrecisionValues (p l : ℕ) : Fin 6 → ℕ :=
  let Γ := chirpForwardGrowth p
  let q := chirpForwardPrecision p Γ l
  ![p, l, Γ, q, q + l + Γ + 5, p + l + Γ + 5]

/-- All four selected parameter words are generated with 36 table atoms. -/
theorem tblChirpForwardPrecision_do {A W e : ℕ} (st : TblSt 6 A) (p l : ℕ)
    (hp : st.val 0 = p) (hl : st.val 1 = l)
    (hroom : chirpForwardPrecision p (chirpForwardGrowth p) l + l + chirpForwardGrowth p + 5 < 2 ^ W) :
    TblDo A W e tblChirpForwardPrecision st
      (fun z => z.val = chirpForwardPrecisionValues p l ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2 ^ W) 36 := by
  have hroom' : p + 2 * (32 * p) + l + 13 + l + 32 * p + 5 < 2 ^ W := hroom
  unfold tblChirpForwardPrecision
  apply TblDo.seq (K₁ := 6) (K₂ := 30) (P₁ := fun z => z.val 0 = p ∧ z.val 1 = l ∧ z.val 2 = 32 * p ∧ z.acc = st.acc)
  · apply TblDo.block
    · simp [tblFitsList, TblIns.fits, TblIns.exact, hp]
      omega
    · simp [tblExactList, TblIns.exact, hp, hl]
      omega
  · intro z ⟨h0, h1, h2, ha⟩
    apply TblDo.seq (K₁ := 16) (K₂ := 14) (P₁ := fun u => u.val 0 = p ∧ u.val 1 = l ∧ u.val 2 = 32 * p ∧
      u.val 3 = p + 2 * (32 * p) + l + 13 ∧ u.acc = st.acc)
    · apply TblDo.block
      · simp [tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h2, List.replicate_succ]
        omega
      · simp [tblExactList, TblIns.exact, h0, h1, h2, ha, List.replicate_succ]
        omega
    · intro u ⟨h0, h1, h2, h3, ha⟩
      apply TblDo.seq (K₁ := 7) (K₂ := 7) (P₁ := fun x => x.val 0 = p ∧ x.val 1 = l ∧ x.val 2 = 32 * p ∧
        x.val 3 = p + 2 * (32 * p) + l + 13 ∧
        x.val 4 = p + 2 * (32 * p) + l + 13 + l + 32 * p + 5 ∧ x.acc = st.acc)
      · apply TblDo.block
        · simp [tblFitsList, TblIns.fits, TblIns.exact, h1, h2, h3, List.replicate_succ]
          omega
        · simp [tblExactList, TblIns.exact, h0, h1, h2, h3, ha, List.replicate_succ]
      · intro x ⟨h0, h1, h2, h3, h4, ha⟩
        apply TblDo.block
        · simp [tblFitsList, TblIns.fits, TblIns.exact, h0, h1, h2, List.replicate_succ]
          omega
        · refine ⟨?_, ?_, ?_⟩
          · funext i
            fin_cases i <;> simp [chirpForwardPrecisionValues, chirpForwardPrecision,
              chirpForwardGrowth, tblExactList, TblIns.exact, h0, h1, h2, h3, h4, List.replicate_succ]
          · simpa [tblExactList, TblIns.exact] using ha
          · intro i
            fin_cases i <;> simp [tblExactList, TblIns.exact, h0, h1, h2, h3, h4, List.replicate_succ] <;> omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
