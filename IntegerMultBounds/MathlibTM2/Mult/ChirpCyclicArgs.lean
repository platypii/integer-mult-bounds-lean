module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpCyclicMath
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
import Mathlib.Tactic.FinCases

/-! # Compute cyclic-source and window counter values from binary dimensions -/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def chirpCyclicSlot : Fin 5 → Fin 10 := ![4, 5, 6, 7, 9]

def chirpCyclicCount (s m w : ℕ) : Fin 5 → ℕ :=
  ![chirpOffset s m * w, (s - chirpOffset s m) * w, chirpPeriods s m,
    (s + 3 * m) * w, (3 * m + 1) * w]

def tblChirpCyclicArgsPrefix : List (TblIns 10) :=
  [.mod 2 0 4, .sub 0 4 4, .mod 4 0 4, .sub 0 4 5, .mul 4 3 4, .mul 5 3 5,
    .add 2 2 7, .add 7 2 7, .add 7 0 7, .zero 8, .inc 8, .sub 7 8 6,
    .div 6 0 6, .inc 6, .mul 7 3 7, .add 2 2 9, .add 9 2 9, .inc 9]

def tblChirpCyclicArgs : TblCode 10 := tblBlock 10 tblChirpCyclicArgsPrefix (.mul 9 3 9)

/-- Nineteen checked atoms compute all five counts; dimensions and accumulator are retained. -/
theorem tblChirpCyclicArgs_do {A W e : ℕ} (st : TblSt 10 A) (s m w : ℕ)
    (hs : st.val 0 = s) (hm : st.val 2 = m) (hw : st.val 3 = w) (hs0 : 0 < s)
    (hsize : s + 3 * m + 1 < 2 ^ W) (hvolume : (s + 3 * m + 1) * w < 2 ^ W)
    (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpCyclicArgs st
      (fun z => (∀ i, z.val (chirpCyclicSlot i) = chirpCyclicCount s m w i) ∧
        (∀ i : Fin 10, i.val < 4 → z.val i = st.val i) ∧ z.acc = st.acc ∧
        (∀ i, z.val i < 2 ^ W)) 19 := by
  have hmod : m % s < s := Nat.mod_lt _ hs0
  have hoff : chirpOffset s m < s := chirpOffset_lt hs0 m
  have hfront : chirpOffset s m * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (show chirpOffset s m ≤ s + 3 * m + 1 by omega)).trans_lt hvolume
  have hback : (s - chirpOffset s m) * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (show s - chirpOffset s m ≤ s + 3 * m + 1 by omega)).trans_lt hvolume
  have hext : (s + 3 * m) * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (by omega : s + 3 * m ≤ s + 3 * m + 1)).trans_lt hvolume
  have hwin : (3 * m + 1) * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (by omega : 3 * m + 1 ≤ s + 3 * m + 1)).trans_lt hvolume
  have hC : chirpPeriods s m < 2 ^ W := by
    have h := Nat.div_le_self (s + 3 * m - 1) s
    unfold chirpPeriods
    omega
  have hthree : m + m + m = 3 * m := by omega
  have hsum : 3 * m + s = s + 3 * m := by omega
  have hW0 : W ≠ 0 := by
    intro he
    rw [he] at hsize
    simp at hsize
  have hcount : (s - m % s) % s = chirpOffset s m := rfl
  apply TblDo.block
  · simp [tblChirpCyclicArgsPrefix, tblFitsList, TblIns.fits, TblIns.exact, hs, hm, hw,
      hthree, hsum, hcount, hfront, hback, hext, hwin]
    have hdiv := Nat.div_le_self (s + 3 * m - 1) s
    omega
  · constructor
    · intro i
      fin_cases i <;> simp [tblChirpCyclicArgsPrefix, tblExactList, TblIns.exact, chirpCyclicSlot,
        chirpCyclicCount, hs, hm, hw, hthree, hsum, chirpOffset, chirpPeriods]
    constructor
    · intro i hi
      fin_cases i <;> first | (simp at hi; done) | simp [tblChirpCyclicArgsPrefix, tblExactList, TblIns.exact]
    constructor
    · rfl
    · have hsW : s < 2 ^ W := by simpa only [hs] using hfit 0
      have hmW : m < 2 ^ W := by simpa only [hm] using hfit 2
      have hwW : w < 2 ^ W := by simpa only [hw] using hfit 3
      intro i
      fin_cases i <;> simp [tblChirpCyclicArgsPrefix, tblExactList, TblIns.exact, hs, hm, hw,
        hthree, hsum, hcount, hfront, hback, hext, hwin, hsW, hmW, hwW]
      all_goals first | exact hfit 0 | exact hfit 1 | exact hfit 2 | exact hfit 3 |
        (simpa [chirpPeriods] using hC) | omega

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
