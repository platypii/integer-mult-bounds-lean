module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedFamilyBatchGeometryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseCaller

/-! The raw inverse execution theorem with the geometry-separated resource ledger. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 303 Q A U}

noncomputable def familyInverseCallerGeometryCost (A W p u l target s t : ℕ) [NeZero s] : ℕ :=
  inverseScalarAtoms p s t u 0 s*tblC W 0+
    inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
    (generatedFamilyComplexSetupCostBound A p u l s t 0 s target+
      generatedFamilyComplexGeometryLineCost p u l s t 0 s target+5)+
    inverseReleaseCost W (inverseMasterValues p u l target s t 0 s)

theorem familyInverseCallerCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (A W p u l target : ℕ) :
    familyInverseCallerCost A W p u l target s t ≤
      familyInverseCallerGeometryCost A W p u l target s t := by
  have h := generatedClosedFamilyComplexBatchCost_full_geometry_le hst A p u l 0 s target 1 le_rfl
  dsimp only [familyInverseCallerCost,familyInverseCallerGeometryCost]
  simp only [one_mul] at h
  omega

theorem familyInverseCaller_geometry_spec (recovery : Bool) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {W p u l target s t : ℕ} [NeZero s] {α d : ℝ}
    (hp : 2 ≤ p) (hwidth : 8*p ≤ 2^u) (hα : 0 < α) (hst : s < t) (hu : 1 ≤ u) (hαu : α^2 = (u : ℝ))
    (hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudget : α^2*d ≤ p)
    (hband : PhaseCellBand.width p u ≤ s)
    (hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (hbandRoom : 64*(p+1)+u < 2^W)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^W)
    (hprecisionRoom : inversePrecisionRoom p l target (haloBoundary s t (PhaseCellBand.width p u) 0 s).card
      (PhaseCellBand.width p u) < 2^W)
    (F : ZMod s → GaussianInt)
    (hF : ∀ i, ‖value (executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (haloBoundary s t (PhaseCellBand.width p u) 0 s).card) 2) 2) (F i)‖ ≤ (2 : ℝ)^2)
    (v : HS 303 Q A U) (S : Stacks 303 A) (tail wl : List (Fin (A+4))) (hwl : wl.length = W)
    (hscalar : tblHolds familyInverseScalarReg S (tblRho W wl [] (inverseInputScalars p u l target s t 0 s)))
    (hleft : ∀ i, S.L (familyInverseCoreReg i) = [])
    (hblank : ∀ i, i ≠ 110 → i ≠ 132 → S.R (familyInverseCoreReg i) = [])
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
        v'.user = v.user ∧ n ≤ familyInverseCallerGeometryCost A W p u l target s t ∧
        Exec body
          (familyInverseCaller recovery hR hQ) (mk v S) n
          (mk v' {S with R := Function.update S.R 132 (cstream A w (chirpLine s G)++S.R 132)}) ∧
        ∀ i, ‖pairedCellRead q w (cstream A w (chirpLine s G)++S.R 132) i-z i‖ ≤ 1/(2 : ℝ)^target := by
  dsimp only
  intro z hz
  obtain ⟨v',n,G,huser,hcost,hexec,herror⟩ := familyInverseCaller_sized_spec (body := body)
    recovery hR hQ hA hp hwidth hα hst hu hαu hθ hgap hbudget hband hpad
    hbandRoom hgeometryRoom hprecisionRoom F hF v S tail wl hwl hscalar hleft hblank hsource z hz
  exact ⟨v',n,G,huser,hcost.trans (familyInverseCallerCost_geometry_le hst A W p u l target),hexec,herror⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
