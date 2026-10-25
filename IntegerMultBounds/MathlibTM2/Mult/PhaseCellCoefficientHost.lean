module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoefficientStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! Execute the numerical coefficient stream in the shared table workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def coefficientHost : Pr P₀ 117 Q A U :=
  coefficientTableHost coefficientStreamCode

/-- The only non-workspace change is the constructed distance vector. -/
theorem coefficientHost_exec {V w P s t u band L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs' : st.val 34 = s) (ht' : st.val 35 = t)
    (hu' : st.val 36 = u) (hb' : st.val 38 = band) (hL' : st.val 42 = L)
    (hP : 13 ≤ P) (hs : 0 < s) (hst : s ≤ t) (hu : 1 ≤ u)
    (hV : u * t * (L + 1) ^ 2 * 2 ^ (13 * P + 8) < 2 ^ V)
    (hstV : ∀ j, st.val j < 2 ^ V) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = V) (hnl : nl.length = w) (hw : w ≤ V)
    (v : HS 117 Q A U) (S : Stacks 117 A) (hS : tblHolds coefficientReg S (tblRho V wl nl st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ (L * (310 * P + 114) + (160 * P + 450)) * tblC V w + 2 * (L * w) + 126 * V + 129 ∧
      Exec body coefficientHost (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          (cstream A w (distanceFactorWords P s t u band L) ++ S.R 110) else S.R k) }) := by
  have hrun := coefficientTableHost_exec (body := body) coefficientStreamCode st
    (cstream A w (distanceFactorWords P s t u band L))
    (coefficientStreamCode_do st hP' hs' ht' hu' hb' hL' hP hs hst hu hV)
    hstV hacc wl nl hwl hnl hw v S hS
  simpa only [coefficientHost, length_cstream, distanceFactorWords_length] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
