module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseInputScalarFits
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller

/-! Close normalization sizing and scalar fits for an ordinary inverse input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}


theorem inverseRoundBatch_derived_exec (hA : 4 ≤ A) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (xs : List GaussianInt) (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8] : List (Fin 303)), S.R r = []) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let q := 4*E
    let j := inverseNormalizationShift p
    S.R 132 = cstream A w xs →
    ∃ v' n, v'.user = v.user ∧
      n ≤ inverseRoundBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length ∧
      Exec body inverseRoundBatch (mk v S) n
        (mk v' {S with R := (Function.update S.R 132 (cstream A (2*p+13) (xs.map (finalRoundWord w q p j))))}) := by
  obtain ⟨hbandRoom,hgeometryRoom,hprecisionRoom⟩ := inverseCallerWordWidth_fits_cuts p u l target s t a b
  exact inverseRoundBatch_exec (body := body) (W := inverseCallerWordWidth p u l target s t)
    (p := p) (u := u) (l := l) (target := target) (s := s) (t := t) (a := a) (b := b) hA wl hwl (inverseInputScalars p u l target s t a b)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | simp [inverseInputScalars])
    hst ha hb hband hbandRoom hgeometryRoom hprecisionRoom
    (inverseInputScalars_fit hst ha hb hbandRoom hgeometryRoom hprecisionRoom) xs v S hS hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
