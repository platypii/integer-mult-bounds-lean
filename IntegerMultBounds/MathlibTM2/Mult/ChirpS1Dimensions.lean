module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpBlockCount

/-! # Compute shared S1 dimension words

A dedicated retained bank stores q,t,m,w,l in slots 0 through 4. The arithmetic
computes p=q+1, the two operand lengths and the ceiling block count in slots 5–8.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpS1Dimensions : TblCode 10 :=
  tblBlock 10 [.zero 9, .inc 9, .sub 1 9 8, .div 8 2 8, .inc 8,
    .copy 0 5, .inc 5, .inc 9, .inc 9, .mul 2 9 6, .inc 6, .inc 9] (.mul 2 9 7)

def chirpS1DimensionValues (q t m w l : ℕ) : Fin 10 → ℕ :=
  ![q, t, m, w, l, q + 1, 3 * m + 1, 4 * m, chirpBlockCount t m, 4]

/-- All intermediate natural arithmetic fits, and every computed dimension is exact. -/
theorem tblChirpS1Dimensions_do {A W e : ℕ} (st : TblSt 10 A) (q t m w l : ℕ)
    (hq : st.val 0 = q) (ht : st.val 1 = t) (hm : st.val 2 = m)
    (hw : st.val 3 = w) (hl : st.val 4 = l) (ht0 : 0 < t) (hm0 : 0 < m)
    (hp : q + 1 < 2 ^ W) (hrow : 3 * m + 1 < 2 ^ W) (hkernel : 4 * m < 2 ^ W)
    (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpS1Dimensions st
      (fun z => z.val = chirpS1DimensionValues q t m w l ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2 ^ W) 13 := by
  have htW : t < 2 ^ W := by simpa only [ht] using hfit 1
  have h4 : 4 < 2 ^ W := (by omega : 4 ≤ 4 * m).trans_lt hkernel
  have hW : W ≠ 0 := by intro h; subst W; norm_num at h4
  have hM : chirpBlockCount t m < 2 ^ W := by
    have hd := Nat.div_le_self (t - 1) m
    unfold chirpBlockCount
    omega
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hq, ht, hm,
      Nat.mul_comm m 3, Nat.mul_comm m 4]
    have hd := Nat.div_le_self (t - 1) m
    omega
  · constructor
    · funext i
      fin_cases i <;> simp [tblExactList, TblIns.exact, chirpS1DimensionValues,
        hq, ht, hm, hw, hl, chirpBlockCount, Nat.mul_comm m 3, Nat.mul_comm m 4]
    constructor
    · rfl
    · intro i
      fin_cases i <;> simp [tblExactList, TblIns.exact, hq, ht, hm, hw, hl,
        Nat.mul_comm m 3, Nat.mul_comm m 4]
      all_goals first
        | simpa only [hq] using hfit 0
        | exact htW
        | simpa only [hm] using hfit 2
        | simpa only [hw] using hfit 3
        | simpa only [hl] using hfit 4
        | exact hp
        | exact hrow
        | exact hkernel
        | simpa only [chirpBlockCount] using hM
        | exact h4

/-- Erase only the five owned arithmetic words, retaining all supplied dimensions. -/
def tblChirpS1DimensionsClear : TblCode 10 :=
  tblBlock 10 [.zero 5, .zero 6, .zero 7, .zero 8] (.zero 9)

theorem tblChirpS1DimensionsClear_do {A W e : ℕ} (st z : TblSt 10 A)
    (hf : ∀ i : Fin 10, i.val < 5 → z.val i = st.val i)
    (hz : ∀ i : Fin 10, 5 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpS1DimensionsClear z (fun u => u.val = st.val ∧ u.acc = z.acc) 5 := by
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits]
  · constructor
    · funext i
      fin_cases i <;> simp (disch := decide) [tblExactList, TblIns.exact, hf, hz]
    · rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
