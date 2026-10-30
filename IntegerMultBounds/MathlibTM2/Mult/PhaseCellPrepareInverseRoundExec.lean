module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundView
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareRoundScalars

/-! Execute rounding preparation in the fixed inverse workspace, preserving its core. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem prepareInverseRound_exec {W p u l target s t a b : ℕ} [NeZero s]
    (wl : List (Fin (A+4))) (hwl : wl.length = W) (st : TblSt 25 A)
    (h0 : st.val 0 = p) (h1 : st.val 1 = u) (h2 : st.val 2 = l) (h3 : st.val 3 = target)
    (h4 : st.val 4 = s) (h5 : st.val 5 = t) (h6 : st.val 6 = a) (h7 : st.val 7 = b)
    (hst : s < t) (haS : a ≤ s) (hbS : b ≤ s) (hbandS : PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
      (PhaseCellBand.width p u) < 2^W) (hfit : ∀ i, st.val i < 2^W)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S (tblRho W wl [] st)) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let E := inverseExecutionExponent p l target N band
    ∃ v' S' n z, v'.user = v.user ∧
      n ≤ (inverseScalarAtoms p s t u a b+(4*Nat.size (4*p)+22))*tblC W 0 ∧
      Exec body (tblCompile familyInverseScalarReg tblPrepareInverseRound) (mk v S) n (mk v' S') ∧
      tblHolds familyInverseScalarReg S' (tblRho W wl [] z) ∧
      tblHolds inverseRoundScalarReg S' (tblRho W wl [] (z.restrict inverseRoundVariables)) ∧
      (z.restrict inverseRoundVariables).val = ![8*E+8,4*E,p,inverseNormalizationShift p,p+8,0,0,0] ∧
      (∀ i : Fin 8, z.val ⟨i.val,by omega⟩ = st.val ⟨i.val,by omega⟩) ∧
      z.acc = st.acc ∧ (∀ i, z.val i < 2^W) ∧
      S'.inp = S.inp ∧ S'.out = S.out ∧ S'.L = S.L ∧
      (∀ i, S'.R (familyInverseCoreReg i) = S.R (familyInverseCoreReg i)) := by
  obtain ⟨v',S',n,z,hu,hn,he,hh,hview,hval,hkeep,hacc,hfitZ,hin,hout,hL,hframe⟩ :=
    prepareRoundScalars_exec (body := body) familyInverseScalarReg familyInverseScalarReg_injective
      wl hwl st h0 h1 h2 h3 h4 h5 h6 h7 hst haS hbS hbandS
      hbandRoom hgeometryRoom hprecisionRoom hfit v S hS
  refine ⟨v',S',n,z,hu,hn,he,hh,hview,hval,hkeep,hacc,hfitZ,hin,hout,hL,?_⟩
  intro i
  exact hframe _ (fun r => familyInverseScalarReg_core r i)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
