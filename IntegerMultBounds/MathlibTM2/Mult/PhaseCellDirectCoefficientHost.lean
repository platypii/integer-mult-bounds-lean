module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDirectCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Execute the direct coefficient body in the finite host machine and release
its owned table bank. The emitted coefficient precedes an arbitrary suffix. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellRationalArgs
  IntegerMultBounds.Resampling.WeightNat

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def directCoefficientHost : Pr P₀ 117 Q A U := coefficientTableHost directCoefficientBody

theorem directCoefficientHost_exec {V w q P s t u j k : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k) (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P)
    (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V) (hsV : 2*s < 2^V)
    (hnjV : s*nearestNatural s t j < 2^V) (hnkV : s*nearestNatural s t k < 2^V)
    (hdjV : latticeDistance s t j k^2 < 2^V) (hdkV : latticeDistance s t k k^2 < 2^V)
    (hsqV : s^2 < 2^V) (hV : 13*P+8 ≤ V)
    (haV : latticeNumerator s t u j k*2^(5*P+2) < 2^V) (hqV : q+P+2 ≤ V)
    (hstV : ∀ r, st.val r < 2^V) (hacc : st.acc = [])
    (wl nl : List (Fin (A+4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (310*P+129)*tblC V w+2*w+126*V+129 ∧
      Exec body directCoefficientHost (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 63 then [] else if r = 110 then
          csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u j k))++S.R 110 else S.R r)}) := by
  have hc := directCoefficientBody_do (w := w) st hpi hP' hneg hs ht hu hj hk hq hpowP hs0 hst hP
    hjV hkV hsV hnjV hnkV hdjV hdkV hsqV hV haV hqV
  obtain ⟨v',m,hu',hm,he⟩ := coefficientTableHost_exec (body := body) directCoefficientBody st
    (csyms A w (rationalWord q (PhaseCellCrossCell.direct P s t u j k)))
    (hc.mono (fun _ h => h.1) le_rfl) hstV hacc wl nl hwl hnl hw v S hS
  exact ⟨v',m,hu',by simpa [csyms] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
