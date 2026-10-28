module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputShiftBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellDerivedInverseRoundBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseBatchCaller

/-! Close normalization sizing and scalar fits for an ordinary inverse input bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def inputShiftBatchCost (W p u l target s t a b count : ℕ) [NeZero s] : ℕ :=
  let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
  (inverseScalarAtoms p s t u a b+22)*tblC W 0+16*(8*E+8)+33*W+34+count*(20*(8*E+8)+44)

theorem inputShiftBatch_derived_exec (hA : 4 ≤ A) (restore : Bool) {p u l target s t a b : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ s)
    (wl : List (Fin (A+4))) (hwl : wl.length = inverseCallerWordWidth p u l target s t)
    (xs : List GaussianInt) (hxs : ∀ z ∈ xs, ‖value p z‖ ≤ 1)
    (v : HS 303 Q A U) (S : Stacks 303 A)
    (hS : tblHolds familyInverseScalarReg S
      (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t a b)))
    (hblank : ∀ r ∈ ([0,1,2,3,4,5,6,7,8,9,10] : List (Fin 303)), S.R r = []) :
    let E := inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)
    let w := 8*E+8
    let d := 4*E-p-1
    S.R 110 = cstream A w (inputShiftSource restore d xs) →
    ∃ v' n, v'.user = v.user ∧
      n ≤ inputShiftBatchCost (inverseCallerWordWidth p u l target s t) p u l target s t a b xs.length ∧
      Exec body (inputShiftBatch restore) (mk v S) n
        (mk v' {S with R := Function.update S.R 110 (cstream A w (inputShiftResult restore d xs))}) := by
  dsimp only
  intro hsrc
  obtain ⟨hbandRoom,hgeometryRoom,hprecisionRoom⟩ := inverseCallerWordWidth_fits_cuts p u l target s t a b
  exact inputShiftBatch_exec (body := body) (W := inverseCallerWordWidth p u l target s t)
    (p := p) (u := u) (l := l) (target := target) (s := s) (t := t) (a := a) (b := b) hA restore wl hwl (inverseInputScalars p u l target s t a b)
    rfl rfl rfl rfl rfl rfl rfl rfl
    (by intro i hi; fin_cases i <;> first | (simp at hi; done) | simp [inverseInputScalars])
    hst ha hb hband hbandRoom hgeometryRoom hprecisionRoom
    (inverseInputScalars_fit hst ha hb hbandRoom hgeometryRoom hprecisionRoom) v S hS xs hxs hsrc hblank

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
