module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightTableStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Execute the complete interleaved weight stream on the fixed 117-tape bank,
then release the owned binary table workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Resampling IntegerMultBounds.Resampling.WeightNat
  IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellRationalArgs

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def weightHost : Pr P₀ 117 Q A U := coefficientTableHost weightStreamCode

theorem weightHost_exec {V w q P s t u lo L : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hdouble : st.val 38 = 2 * s) (hden : st.val 39 = similarityDenominator s t)
    (hq : st.val 42 = 2 ^ q) (hpowP : st.val 43 = 2 ^ P)
    (hqp : st.val 44 = 2 ^ (q + P)) (hL : st.val 46 = L) (hlo : st.val 47 = lo)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t)
    (hloV : lo + L < 2 ^ V) (hLV : L < 2 ^ V)
    (hsV : 2 * s < 2 ^ V) (hsq : s ^ 2 < 2 ^ V) (huV : u * s ^ 2 < 2 ^ V)
    (hV : 13 * P + 8 ≤ V) (hqV : q + P + 2 ≤ V)
    (hargs : ∀ j < s, 2 * t * j + s < 2 ^ V ∧
      similarityNumerator s t u j * 2 ^ (5 * P + 2) < 2 ^ V)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (L * (310 * P + 124) + 3) * tblC V w + 2 * (L * (2 * w)) + 126 * V + 129 ∧
      Exec body weightHost (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          ((List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110) else S.R k) }) := by
  have hcode := (weightStreamCode_do (A := A) (V := V) (w := w) st hpi hP' hneg hs ht hu hdouble hden hq hpowP hqp
    hL hlo hP hs0 hst hloV hLV hsV hsq huV hV hqV hargs).mono (fun _ h => h.1) le_rfl
  have hlen : ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).length = L * (2 * w) := by
    simp [List.length_flatMap, weightPairSymbols, two_mul]
  have hrun := coefficientTableHost_exec (body := body) weightStreamCode st
    ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)) hcode
    hstV hacc wl nl hwl hnl hw v S hS
  simpa only [weightHost, hlen] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
