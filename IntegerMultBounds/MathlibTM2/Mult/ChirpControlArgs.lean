module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpWindows
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
import Mathlib.Tactic.FinCases

/-! # Compute the next chirp gathering advance

Four input words hold `s,t,m,w`. The retained origin and centre advance together;
six arithmetic instructions produce the next symbol count without a supplied schedule.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM

def ChirpControlReady {A : ℕ} (st : TblSt 10 A) (s t m w j : ℕ) : Prop :=
  st.val 0 = s ∧ st.val 1 = t ∧ st.val 2 = m ∧ st.val 3 = w ∧
    st.val 4 = j * m ∧ st.val 5 = chirpCenter s t m j

def tblChirpControlStep : TblCode 10 :=
  tblBlock 10 [.add 4 2 4, .mul 0 4 6, .div 6 1 7, .sub 7 5 8, .mul 8 3 9] (.copy 7 5)

/-- The advancing origin, centre and symbol count are computed in six checked atoms. -/
theorem tblChirpControlStep_do {A W e : ℕ} (st : TblSt 10 A) (s t m w j : ℕ)
    (hready : ChirpControlReady st s t m w j) (hst : s ≤ t) (ht : 0 < t)
    (hk : (j + 1) * m < 2 ^ W) (hnum : s * ((j + 1) * m) < 2 ^ W)
    (hwidth : m * w < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpControlStep st
      (fun z => (ChirpControlReady z s t m w (j + 1) ∧
        z.val 9 = chirpAdvance s t m j * w ∧ z.acc = st.acc) ∧ ∀ i, z.val i < 2 ^ W) 6 := by
  rcases hready with ⟨hs, htval, hm, hw, hj, hc⟩
  have hstep : j * m + m = (j + 1) * m := by ring
  have hcenter : s * ((j + 1) * m) / t < 2 ^ W :=
    (Nat.div_le_self _ _).trans_lt hnum
  have hmono : chirpCenter s t m j ≤ chirpCenter s t m (j + 1) :=
    chirpCenter_mono s t m (by omega)
  have hd : chirpAdvance s t m j * w < 2 ^ W :=
    (Nat.mul_le_mul_right w (chirpAdvance_le hst ht m j)).trans_lt hwidth
  apply TblDo.block
  · simp only [List.cons_append, List.nil_append, tblFitsList, TblIns.fits, TblIns.exact,
      Function.update_self, Function.update_of_ne (by decide : (0 : Fin 10) ≠ 4),
      Function.update_of_ne (by decide : (1 : Fin 10) ≠ 4),
      Function.update_of_ne (by decide : (1 : Fin 10) ≠ 6)]
    simp [hs, htval, hm, hw, hj, hc, hstep,
      hk, hnum, hcenter, chirpAdvance, chirpCenter] at hd hmono ⊢
    exact ⟨hmono, hd⟩
  · constructor
    · simp [tblExactList, TblIns.exact, ChirpControlReady, hs, htval, hm, hw, hj, hc,
        hstep, chirpCenter, chirpAdvance]
    · have hmW : m < 2 ^ W := by simpa only [hm] using hfit 2
      have hdW : chirpAdvance s t m j < 2 ^ W := (chirpAdvance_le hst ht m j).trans_lt hmW
      have hsW : s < 2 ^ W := by simpa only [hs] using hfit 0
      have htW : t < 2 ^ W := by simpa only [htval] using hfit 1
      have hwW : w < 2 ^ W := by simpa only [hw] using hfit 3
      simp only [chirpCenter, chirpAdvance] at hcenter hdW hd
      intro i
      fin_cases i <;> simp [tblExactList, TblIns.exact, hs, htval, hm, hw, hj, hc,
        hstep, chirpCenter, hsW, htW, hmW, hwW, hk, hnum, hcenter, hdW, hd]

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
