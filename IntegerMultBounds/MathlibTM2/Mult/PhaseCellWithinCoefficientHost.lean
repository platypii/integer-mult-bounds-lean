module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWithinCoefficient
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Execute the within-cell coefficient body in the finite host machine and release
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

def withinCoefficientHost : Pr P₀ 117 Q A U := coefficientTableHost withinCoefficientBody

theorem withinCoefficientHost_exec {V w q P s t u band j k : ℕ} (st : TblSt 48 A)
    (hpi : st.val 18 = piN P) (hP' : st.val 19 = P) (hneg : st.val 22 = 1)
    (hs : st.val 34 = s) (ht : st.val 35 = t) (hu : st.val 36 = u)
    (hj : st.val 37 = j) (hk : st.val 38 = k)
    (hq : st.val 39 = 2^q) (hpowP : st.val 40 = 2^P)
    (hs0 : 0 < s) (hst : s < t) (hP : 13 ≤ P)
    (hjk : j ≠ k) (hband : ((k : ℤ)-(j : ℤ)).natAbs ≤ band)
    (hjV : 2*t*j+s < 2^V) (hkV : 2*t*k+s < 2^V)
    (hsV : 2*s < 2^V) (htV : t < 2^V)
    (hsq : s^2 < 2^V) (huV : u*s^2 < 2^V)
    (hdenV : similarityDenominator s t < 2^V)
    (hV : 13*P+8 ≤ V) (hqV : q+2*P+4 ≤ V)
    (haj : similarityNumerator s t u j*2^(5*P+2) < 2^V)
    (hak : similarityNumerator s t u k*2^(5*P+2) < 2^V)
    (hdV : naturalDistance j k^2 < 2^V)
    (htdV : t*naturalDistance j k^2 < 2^V)
    (hudV : u*(t*naturalDistance j k^2) < 2^V)
    (had : (u*t*naturalDistance j k^2)*2^(5*P+2) < 2^V)
    (hstV : ∀ r, st.val r < 2^V) (hacc : st.acc = [])
    (wl nl : List (Fin (A+4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧ m ≤ (930*P+352)*tblC V w+2*w+126*V+129 ∧
      Exec body withinCoefficientHost (mk v S) m
        (mk v' {S with R := (fun r => if r.val < 63 then [] else if r = 110 then
          csyms A w (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band j k))++S.R 110 else S.R r)}) := by
  have hc := withinCoefficientBody_do (w := w) st hpi hP' hneg hs ht hu hj hk hq hpowP hs0 hst hP
    hjk hband hjV hkV hsV htV hsq huV hdenV hV hqV haj hak hdV htdV hudV had
  obtain ⟨v',m,hu',hm,he⟩ := coefficientTableHost_exec (body := body) withinCoefficientBody st
    (csyms A w (rationalWord q (PhaseCellConcreteCoefficients.entry P s t u band j k)))
    (hc.mono (fun _ h => h.1) le_rfl) hstV hacc wl nl hwl hnl hw v S hS
  exact ⟨v',m,hu',by simpa [csyms] using hm,he⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
