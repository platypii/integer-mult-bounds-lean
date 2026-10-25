module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightInit
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightTableStream

/-! Initialize and execute the complete weight table from ordinary numeric
headers. Pi, doubled modulus, denominator and scales are generated internally. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

def numericalWeightStream : TblCode 48 := weightInitCode ;; weightStreamCode

def numericalWeightAtoms (P q L : ℕ) : ℕ := 158 * P + 8 * q + L * (310 * P + 124) + 427

theorem numericalWeightStream_do {A V w q P s t u lo L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hu : st.val 36 = u) (hq : st.val 45 = q) (hL : st.val 46 = L) (hlo : st.val 47 = lo)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t)
    (hloV : lo + L < 2 ^ V) (hLV : L < 2 ^ V)
    (hsV : 2 * s < 2 ^ V) (htV : t < 2 ^ V)
    (hsq : s ^ 2 < 2 ^ V) (huV : u * s ^ 2 < 2 ^ V)
    (hdV : similarityDenominator s t < 2 ^ V)
    (hV : 13 * P + 8 ≤ V) (hqV : q + P + 2 ≤ V)
    (hargs : ∀ j < s, 2 * t * j + s < 2 ^ V ∧
      similarityNumerator s t u j * 2 ^ (5 * P + 2) < 2 ^ V) :
    TblDo A V w numericalWeightStream st (fun st' =>
      st'.acc = ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).reverse ++ st.acc)
      (numericalWeightAtoms P q L) := by
  have hinit := weightInitCode_do (A := A) (V := V) (w := w) st hP' hq hs ht
    hst.le hP hV hqV hsV htV hdV
  have hcore : TblDo A V w numericalWeightStream st (fun st' =>
      st'.acc = ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).reverse ++ st.acc)
      ((158 * P + 8 * q + 424) + (L * (310 * P + 124) + 3)) := by
    unfold numericalWeightStream
    refine hinit.seq (fun s₁ ⟨⟨gpi, gneg, gdouble, gden, gq, gP, gqp⟩, ga, gf⟩ => ?_)
    have hstream := weightStreamCode_do (A := A) (V := V) (w := w) s₁ gpi
      ((gf 19 (by decide) (by simp)).trans hP') gneg
      ((gf 34 (by decide) (by simp)).trans hs)
      ((gf 35 (by decide) (by simp)).trans ht)
      ((gf 36 (by decide) (by simp)).trans hu)
      gdouble gden gq gP gqp
      ((gf 46 (by decide) (by simp)).trans hL)
      ((gf 47 (by decide) (by simp)).trans hlo)
      hP hs0 hst hloV hLV hsV hsq huV hV hqV hargs
    exact hstream.mono (fun s' h => by rw [h.1, ga]) le_rfl
  exact hcore.mono (fun _ h => h) (by unfold numericalWeightAtoms; omega)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
