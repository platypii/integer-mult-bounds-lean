module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNumericalWeightStream
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellWeightWidth
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellTableHost

/-! The numerical weight factory generates every pi, exponent and scale value.
A dimension-based workspace width proves all arithmetic fits uniformly. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN

variable {Q A : ℕ} {P₀ U : Type} {body : P₀ → Pr P₀ 117 Q A U}

def numericalWeightHost : Pr P₀ 117 Q A U := coefficientTableHost numericalWeightStream

theorem numericalWeightHost_exec {w q P s t u lo L : ℕ} (st : TblSt 48 A)
    (hP' : st.val 19 = P) (hs : st.val 34 = s) (ht : st.val 35 = t)
    (hu' : st.val 36 = u) (hq : st.val 45 = q) (hL' : st.val 46 = L) (hlo' : st.val 47 = lo)
    (hP : 13 ≤ P) (hs0 : 0 < s) (hst : s < t) (hu : 1 ≤ u)
    (hlo : lo < s) (hL : L ≤ s)
    (hstV : ∀ j, st.val j < 2 ^ weightWorkspaceWidth P q w t u) (hacc : st.acc = [])
    (wl nl : List (Fin (A + 4))) (hwl : wl.length = weightWorkspaceWidth P q w t u)
    (hnl : nl.length = w) (v : HS 117 Q A U) (S : Stacks 117 A)
    (hS : tblHolds coefficientReg S (tblRho (weightWorkspaceWidth P q w t u) wl nl st)) :
    ∃ v' m, v'.user = v.user ∧
      m ≤ numericalWeightAtoms P q L * tblC (weightWorkspaceWidth P q w t u) w +
        4 * L * w + 126 * weightWorkspaceWidth P q w t u + 129 ∧
      Exec body numericalWeightHost (mk v S) m
        (mk v' { S with R := (fun k => if k.val < 63 then [] else if k = 110 then
          ((List.range L).flatMap (weightPairSymbols A w q P s t u lo) ++ S.R 110) else S.R k) }) := by
  obtain ⟨hw, hV, hqV, hloV, hLV, hsV, htV, hsq, huV, hdV, hargs⟩ :=
    weightWorkspaceWidth_facts (q := q) (w := w) hP hs0 hst hu hlo hL
  have hcode := numericalWeightStream_do (A := A) (V := weightWorkspaceWidth P q w t u) (w := w)
    st hP' hs ht hu' hq hL' hlo' hP hs0 hst hloV hLV hsV htV hsq huV hdV hV hqV hargs
  have hlen : ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)).length = L * (2 * w) := by
    simp [List.length_flatMap, weightPairSymbols, two_mul]
  have hrun := coefficientTableHost_exec (body := body) numericalWeightStream st
    ((List.range L).flatMap (weightPairSymbols A w q P s t u lo)) hcode
    hstV hacc wl nl hwl hnl hw v S hS
  simpa only [numericalWeightHost, hlen, show 2 * (L * (2 * w)) = 4 * L * w by ring] using hrun

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
