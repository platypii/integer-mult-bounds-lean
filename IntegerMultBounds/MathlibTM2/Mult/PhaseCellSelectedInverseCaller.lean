module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellClosedInverseCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseCallerSizing

/-! The complete inverse caller with a derived scalar width and no supplied readiness or room witnesses. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

theorem closedInverseCaller_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 264 Q A U) (S : Stacks 264 A) (tail wl : List (Fin (A+4))) (hwl : wl.length = (inverseCallerWordWidth p u l target s t))
    (hscalar : tblHolds inverseScalarReg S (tblRho (inverseCallerWordWidth p u l target s t) wl [] (inverseInputScalars p u l target s t 0 s)))
    (hleft : ∀ i, S.L (inverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (inverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A (executionWidth p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2)
        (chirpLine s F)++tail) :
    let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    ∀ z : ZMod s → ℂ,
      Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z = (fun i => value q (F i)) →
      ∃ v' n, ∃ G : ZMod s → GaussianInt,
        v'.user = v.user ∧ n ≤ closedInverseCallerCost (inverseCallerWordWidth p u l target s t) p u l target s t ∧
        Exec (embTab inverseCoreReg (embTab boundaryFactorLegacyReg (embTab tableReg
          (embTab boundaryArithmeticReg (embTab componentReg (embTab groupReg body))))))
          (closedInverseCaller hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) ∧
        ∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)++S.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  obtain ⟨hbandRoom,hgeometryRoom,hprecisionRoom⟩ := inverseCallerWordWidth_fits p u l target s t
  exact closedInverseCaller_sized_spec (body := body) hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget
    hband hpad hbandRoom hgeometryRoom hprecisionRoom F hF v S tail wl hwl hscalar hleft hblank hsource

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
