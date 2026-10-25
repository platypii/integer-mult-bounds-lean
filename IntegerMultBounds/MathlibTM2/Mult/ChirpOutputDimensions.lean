module

public import IntegerMultBounds.MathlibTM2.Mult.ChirpUnaryCopies
public import IntegerMultBounds.MathlibTM2.Fast.TableProg
import Mathlib.Tactic.FinCases

/-! # Compute all shift, round and crop dimensions from binary inputs

Slots 0–5 retain p,q,l,Γ,w,t. The eight working slots compute the output width,
precision drop, unused high bits, crop volume and both numerator-shift controls.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.Mult.ShortConv

open IntegerMultBounds.MathlibTM2.Fast.TableVM

def tblChirpOutputDimensions : TblCode 14 :=
  tblBlock 14 [.zero 13, .inc 13, .inc 13, .inc 13, .inc 13, .inc 13,
    .add 0 2 6, .add 6 3 6, .add 6 13 6, .sub 1 0 7, .sub 4 7 8, .sub 8 6 8,
    .mul 5 6 9, .copy 2 10, .inc 10, .sub 4 10 11] (.sub 4 3 12)

def chirpOutputDimensionValues (p q l Γ w t : ℕ) : Fin 14 → ℕ :=
  ![p, q, l, Γ, w, t, p + l + Γ + 5, q - p,
    w - (q - p) - (p + l + Γ + 5), t * (p + l + Γ + 5),
    l + 1, w - (l + 1), w - Γ, 5]

/-- Every dimension is computed with checked arithmetic, retaining the six caller inputs. -/
theorem tblChirpOutputDimensions_do {A W e : ℕ} (st : TblSt 14 A) (p q l Γ w t : ℕ)
    (hp : st.val 0 = p) (hq : st.val 1 = q) (hl : st.val 2 = l)
    (hΓ : st.val 3 = Γ) (hw : st.val 4 = w) (ht : st.val 5 = t)
    (hpq : p ≤ q) (hwidth : q + l + Γ + 5 ≤ w)
    (hvolume : t * (p + l + Γ + 5) < 2 ^ W) (hfit : ∀ i, st.val i < 2 ^ W) :
    TblDo A W e tblChirpOutputDimensions st
      (fun z => z.val = chirpOutputDimensionValues p q l Γ w t ∧ z.acc = st.acc ∧
        ∀ i, z.val i < 2 ^ W) 17 := by
  have hwW : w < 2 ^ W := by simpa only [hw] using hfit 4
  have hqW : q < 2 ^ W := by simpa only [hq] using hfit 1
  have hW : W ≠ 0 := by
    intro h
    subst W
    norm_num at hwW
    omega
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits, TblIns.exact, hp, hq, hl, hΓ, hw, ht]
    omega
  · constructor
    · funext i
      fin_cases i <;> simp [tblExactList, TblIns.exact, chirpOutputDimensionValues,
        hp, hq, hl, hΓ, hw, ht]
    constructor
    · rfl
    · intro i
      fin_cases i <;> simp [tblExactList, TblIns.exact, hp, hq, hl, hΓ, hw, ht]
      all_goals first
        | simpa only [hp] using hfit 0
        | exact hqW
        | simpa only [hl] using hfit 2
        | simpa only [hΓ] using hfit 3
        | exact hwW
        | simpa only [ht] using hfit 5
        | exact hvolume
        | omega

/-- Erase the eight computed words after their unary copies have been installed. -/
def tblChirpOutputDimensionsClear : TblCode 14 :=
  tblBlock 14 [.zero 6, .zero 7, .zero 8, .zero 9, .zero 10, .zero 11, .zero 12] (.zero 13)

theorem tblChirpOutputDimensionsClear_do {A W e : ℕ} (st z : TblSt 14 A)
    (hf : ∀ i : Fin 14, i.val < 6 → z.val i = st.val i)
    (hz : ∀ i : Fin 14, 6 ≤ i.val → st.val i = 0) :
    TblDo A W e tblChirpOutputDimensionsClear z (fun u => u.val = st.val ∧ u.acc = z.acc) 8 := by
  apply TblDo.block
  · simp [tblFitsList, TblIns.fits]
  · constructor
    · funext i
      fin_cases i <;> simp (disch := decide) [tblExactList, TblIns.exact, hf, hz]
    · rfl

end IntegerMultBounds.MathlibTM2.Mult.ShortConv
