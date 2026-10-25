module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpDimensionScope
public import IntegerMultBounds.MathlibTM2.Fast.CMul

/-! # Compute the multiplier's three dimension words from q and w

A doubling loop computes the first power of two greater than 2w, exactly topN w.
No multiplier-size counter or template is supplied. The arithmetic bank retains
q,w and clears its three working words after unary-counter installation.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.Schoenhage.Schedule

def tblChirpMultiplierDimensions : TblCode 5 :=
  .seq (tblBlock 5 [.add 1 1 2, .inc 2, .zero 3, .inc 3] (.zero 4))
    (.loop 3 2 (tblBlock 5 [.add 3 3 3] (.inc 4)))

def chirpMultiplierDimensionValues (q w : ℕ) : Fin 5 → ℕ :=
  ![q, w, 2 * w + 1, topN w, Nat.size (2 * w)]

/-- All multiplier geometry is computed by a dimension-independent doubling program. -/
theorem tblChirpMultiplierDimensions_do {A W e : ℕ} (st : TblSt 5 A) (q w : ℕ)
    (hq : st.val 0 = q) (hw : st.val 1 = w) (hw1 : 1 ≤ w)
    (hroom : 4 * w + 2 < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpMultiplierDimensions st
      (fun z => z.val = chirpMultiplierDimensionValues q w ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2 ^ W) (4 * Nat.size (2 * w) + 7) := by
  let n := Nat.size (2 * w)
  have htop : 2 ^ n ≤ 4 * w := (topN_facts hw1).2.1
  have hn : n ≤ 2 * w := Nat.size_le.mpr Nat.lt_two_pow_self
  have hW : W ≠ 0 := by intro h; subst W; norm_num at hroom
  let st₁ : TblSt 5 A := ⟨Function.update (Function.update
    (Function.update st.val 2 (2 * w + 1)) 3 1) 4 0, st.acc⟩
  have hinit : TblDo A W e (tblBlock 5 [.add 1 1 2, .inc 2, .zero 3, .inc 3] (.zero 4)) st
      (fun z => z = st₁) 5 := TblDo.block _ _
    (by simp [tblFitsList, TblIns.fits, TblIns.exact, hw]; omega)
    (by simp [tblExactList, TblIns.exact, st₁, hw, ← two_mul])
  let Inv := fun j (z : TblSt 5 A) => z.val 0 = q ∧ z.val 1 = w ∧ z.val 2 = 2 * w + 1 ∧
    z.val 3 = 2 ^ j ∧ z.val 4 = j ∧ z.acc = st.acc
  have hloop : TblDo A W e (.loop 3 2 (tblBlock 5 [.add 3 3 3] (.inc 4))) st₁
      (Inv n) (n * 4 + 2) := by
    apply TblDo.loop Inv n 2
    · simp [Inv, st₁, hq, hw]
    · intro j hj z ⟨h0, h1, h2, h3, h4, ha⟩
      have hjpow : 2 ^ j ≤ 2 * w := by
        have hnot : ¬2 * w < 2 ^ j := fun h => Nat.not_le_of_lt hj (Nat.size_le.mpr h)
        omega
      refine ⟨by rw [h3, h2]; omega, TblDo.block _ _ ?_ ?_⟩
      · simp [tblFitsList, TblIns.fits, TblIns.exact, h3, h4]
        constructor <;> omega
      · refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
        · simpa [tblExactList, TblIns.exact] using h0
        · simpa [tblExactList, TblIns.exact] using h1
        · simpa [tblExactList, TblIns.exact] using h2
        · simp [tblExactList, TblIns.exact, h3, pow_succ]; ring
        · simp [tblExactList, TblIns.exact, h4]
        · simpa [tblExactList, TblIns.exact] using ha
    · intro z hz
      refine ⟨?_, hz⟩
      rcases hz with ⟨_, _, h2, h3, _, _⟩
      rw [h3, h2]
      have hlt : 2 * w < 2 ^ n := Nat.lt_size_self _
      omega
  have hr := hinit.seq (fun z hz => by cases hz; exact hloop)
  exact hr.mono (fun z ⟨h0, h1, h2, h3, h4, ha⟩ => ⟨by
    funext i
    fin_cases i <;> simp [chirpMultiplierDimensionValues, h0, h1, h2, h3, h4, topN, bitlen, n], ha,
    by
      intro i
      fin_cases i <;> simp [h0, h1, h2, h3, h4]
      · simpa only [hq] using hfit 0
      · omega
      · omega
      · omega
      · omega⟩) (by omega)

/-- Restore exactly the three binary working words after their counters have been copied. -/
def tblChirpMultiplierDimensionsClear : TblCode 5 := tblBlock 5 [.zero 2, .zero 3] (.zero 4)

theorem tblChirpMultiplierDimensionsClear_do {A W e : ℕ} (st z : TblSt 5 A)
    (hf : ∀ i : Fin 5, i.val < 2 → z.val i = st.val i)
    (hz : ∀ i : Fin 5, 2 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpMultiplierDimensionsClear z (fun u => u.val = st.val ∧ u.acc = z.acc) 3 := by
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits]
  · constructor
    · funext i
      fin_cases i <;> simp (disch := decide) [tblExactList, TblIns.exact, hf, hz]
    · rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
