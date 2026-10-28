module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFamilyDensityFast

/-! The complete inverse caller with its axis-density kernel allowance. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

theorem familyInverseCaller_selected_density_spec (ct cG : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p u target s t dimension : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hdimension : 0 < dimension) (haxis : IntegerMultBounds.MathlibTM2.Mult.Moduli.AxisBounds dimension s t)
    (hband : PhaseCellBand.width p u ≤ s)
    (htarget : target ≤ ct*p) (hgeometry : Nat.size (2*s+1) ≤ cG*p)
    (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value (executionPrecision p (haloInverseRingLog s t) (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 303 Q A U) (S : Stacks 303 A) (tail wl : List (Fin (A+4))) (hwl : wl.length = (inverseCallerWordWidth p u (haloInverseRingLog s t) target s t))
    (hscalar : tblHolds familyInverseScalarReg S (tblRho (inverseCallerWordWidth p u (haloInverseRingLog s t) target s t) wl [] (inverseInputScalars p u (haloInverseRingLog s t) target s t 0 s)))
    (hleft : ∀ i, S.L (familyInverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (familyInverseCoreReg i) = [])
    (hsource : S.R 110 = cstream A (executionWidth p (haloInverseRingLog s t) (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2)
        (chirpLine s F)++tail),
    let B := haloBoundary s t (PhaseCellBand.width p u) 0 s
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 B.card
    let q := executionPrecision p (haloInverseRingLog s t) (initialSchurTarget p u bits 2) 2
    let w := executionWidth p (haloInverseRingLog s t) (initialSchurTarget p u bits 2) 2
    ∀ z : ZMod s → ℂ,
      Matrix.mulVec (fun i j => (realMatrix s t p u i j : ℂ)) z = (fun i => value q (F i)) →
      ∃ v', ∃ n : ℕ, ∃ G : ZMod s → GaussianInt,
        v'.user = v.user ∧ (n : ℝ) ≤ (familyInverseControlRemainingCost A (inverseCallerWordWidth p u (haloInverseRingLog s t) target s t) p u target s t : ℝ)+
          C*(t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/dimension)*(p : ℝ)^(129/128 : ℝ) ∧
        Exec body
          (familyInverseCaller recovery hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) ∧
        ∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)++S.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  obtain ⟨C,hC,hprice⟩ := familyInverseCaller_selected_density_fast_le ct cG
  refine ⟨C,hC,?_⟩
  intro recovery hR hQ hA p u target s t dimension _ α d hp hwidth hα hst hu hαu hθ hgap hbudget hdimension haxis hband
    htarget hgeometry F hF v S tail wl hwl hscalar hleft hblank hsource
  dsimp only
  intro z hz
  obtain ⟨v',n,G,huser,hcost,hexec,herror⟩ := familyInverseCaller_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband
    (haloInverseRingLog_fits s t (PhaseCellBand.width p u)) F hF v S tail wl hwl hscalar hleft hblank hsource z hz
  have hbound := hprice A (inverseCallerWordWidth p u (haloInverseRingLog s t) target s t)
    p u target s t dimension (by omega) hst hdimension haxis hband hθ htarget hgeometry
  exact ⟨v',n,G,huser,((Nat.cast_le (α := ℝ)).mpr hcost).trans hbound,hexec,herror⟩

end IntegerMultBounds.MathlibTM2.Cost
