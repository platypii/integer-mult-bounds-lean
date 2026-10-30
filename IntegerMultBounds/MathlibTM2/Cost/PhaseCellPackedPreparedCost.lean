module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedInteriorCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPassEnvelope
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedRecoveryCost
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedResidualCost

/-! The prepared solver retains its two interior arithmetic passes and its
existing residual-solve bill. Remaining input and disposal work is polynomial. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedBoundaryDataCost_poly {V N n w t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hV : V ≤ Z) (hN : N ≤ t) (hn : n ≤ t) (hw : w ≤ Z) :
    packedBoundaryDataCost V N n w ≤ 100000*t*Z^3 := by
  have hmono : packedBoundaryDataCost V N n w ≤ packedBoundaryDataCost Z t t Z := by
    unfold packedBoundaryDataCost metadataPackedBoundaryRhsCost closedPackedBoundaryRhsFoldCost
      preparePackedBoundaryFoldCost moveCountedLineCost boundaryFoldCountersCost tblC
    gcongr
  apply hmono.trans
  unfold packedBoundaryDataCost metadataPackedBoundaryRhsCost closedPackedBoundaryRhsFoldCost
    preparePackedBoundaryFoldCost moveCountedLineCost boundaryFoldCountersCost tblC
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₂ := Nat.mul_le_mul_left t h₂
  have ht₃ := Nat.mul_le_mul_left t h₃
  have hZt := Nat.mul_le_mul_left (Z^3) ht
  have htZ := Nat.mul_le_mul_left t hZ
  nlinarith only [ht,hZ,h₂,h₃,ht₂,ht₃,hZt,htZ]

/-- Per-input tape conversion and disposal; no numerical or factor work. -/
theorem packedHaloInputTapeCost_poly {P q w s t u band a b V n Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : b-a ≤ t) (hn : n ≤ t)
    (hw : w ≤ Z) (hband : band ≤ Z) (hV : V ≤ Z) :
    packedBoundaryDataCost V (b-a) n w+4*n*w+4+
      packedRecoveryReleaseCost (couplingCoefficientPageInterval P q s t u band a b a (b-a)).length (2*band+1) w+
      packedInputAdvanceCost V (b-a) w+(2*w+3) ≤ 1000000*t*Z^3 := by
  have hdata := packedBoundaryDataCost_poly ht hZ hV hN hn hw
  have hlen := couplingCoefficientPageInterval_length_le P q s t u band a b a (b-a)
  have hprod := Nat.mul_le_mul hN (show 2*band+1 ≤ 3*Z by omega)
  have hwords : (couplingCoefficientPageInterval P q s t u band a b a (b-a)).length ≤ 3*t*Z := by
    nlinarith only [hlen,hprod]
  have htail : 4*n*w+4+
      packedRecoveryReleaseCost (couplingCoefficientPageInterval P q s t u band a b a (b-a)).length (2*band+1) w+
      packedInputAdvanceCost V (b-a) w+(2*w+3) ≤
        4*t*Z+4+packedRecoveryReleaseCost (3*t*Z) (2*Z+1) Z+packedInputAdvanceCost Z t Z+(2*Z+3) := by
    unfold packedRecoveryReleaseCost releaseCouplingCoefficientPageCost packedInputAdvanceCost retireCountedLineCost
    gcongr
  unfold packedRecoveryReleaseCost releaseCouplingCoefficientPageCost packedInputAdvanceCost retireCountedLineCost at htail
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₂ := Nat.mul_le_mul_left t h₂
  have ht₃ := Nat.mul_le_mul_left t h₃
  have hZt := Nat.mul_le_mul_left (Z^3) ht
  have htZ := Nat.mul_le_mul_left t hZ
  unfold packedRecoveryReleaseCost releaseCouplingCoefficientPageCost packedInputAdvanceCost retireCountedLineCost
  nlinarith only [hdata,htail,ht,hZ,h₂,h₃,ht₂,ht₃,hZt,htZ]

/-- The actual prepared input bill, specialized to the RHS exponent used by
normalization. Its arithmetic stages are preserved for reuse of their bounds. -/
theorem packedHaloPreparedInputCost_le_stages {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l target a b V Z : ℕ) (hb : b ≤ s) (hZ : 1 ≤ Z) (hV : V ≤ Z) :
    let band := PhaseCellBand.width p u
    let n := (haloBoundary s t band a b).card
    let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 n) 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    w ≤ Z → band ≤ Z →
    packedHaloPreparedInputCost p u l target 2 s t a b V ≤
      packedHaloInteriorCoefficientsCost p l s t u stage 2 a b V+
      packedBoundaryRecoveryCost p u l target 2 s t a b V q w+
      preparedResidualSolveCost q w n (12*band+1)+
      preparedSharedLocalFeedCouplingIntervalCost false (2^15*p) q w s t u band a b a (b-a) V+
      1000000*t*Z^3 := by
  dsimp only
  intro hw hband
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hn : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ t :=
    (show (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s by
      simpa only [ZMod.card] using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hst.le
  have hcontrols := packedHaloInputTapeCost_poly (P := 2^15*p) (s := s) (u := u) (a := a) (b := b)
    (q := executionPrecision p l (initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p target) 2 (haloBoundary s t (PhaseCellBand.width p u) a b).card) 2) 2)
    ht hZ hN hn hw hband hV
  simp only [packedHaloPreparedInputCost,packedHaloPreparedBoundaryCost,packedHaloRealBoundaryDataCost,
    packedHaloBoundaryDataCost,packedHaloResidualCost,boundaryHaloTarget,Nat.add_sub_cancel]
  omega

/-- Reuse the prepared residual kernel's row/bandwidth bound and the existing
scalar multiplication estimate. No factor construction is included. -/
theorem preparedResidualSolveCost_poly {q n band t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hn : n ≤ t) (hw : 2*q+8 ≤ Z) (hband : band ≤ Z) :
    preparedResidualSolveCost q (2*q+8) n (12*band+1) ≤ 8000000*(ssMulConst+1)*t*Z^4 := by
  let S := ssMulConst+1
  have hS : 1 ≤ S := by dsimp only [S]; omega
  have hkernel := preparedResidualSolveCost_le q n (12*band+1) (by omega)
  have hmul := band_rmul_le hw hZ
  have hcube : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have hunit : 1 ≤ Z^3 := one_le_pow₀ hZ
  have hscale : Z^3 ≤ S*Z^3 := Nat.le_mul_of_pos_left _ hS
  have hscalar : rmulCost (2*q+8)+(2*q+8)+1 ≤ 290*S*Z^3 := by
    dsimp only [S] at hscale ⊢
    nlinarith only [hmul,hw,hcube,hunit,hscale]
  have hrows : n+1 ≤ 2*t := by omega
  have hwidth : 12*band+1 ≤ 13*Z := by omega
  have hsize : 1000*(n+1)*(12*band+1) ≤ 1000*(2*t)*(13*Z) := by
    simpa only [Nat.mul_assoc] using Nat.mul_le_mul_left 1000 (Nat.mul_le_mul hrows hwidth)
  have hcost := hkernel.trans (Nat.mul_le_mul hsize hscalar)
  dsimp only [S] at hcost
  nlinarith only [hcost]

/-- Compose the actual prepared solver using one envelope for each precision.
Factor setup is absent; the residual kernel reuses its established scalar bound. -/
theorem packedHaloPreparedInputCost_weights_poly {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l target a b V Z : ℕ) (ha : a ≤ s) (hb : b ≤ s) :
    let band := PhaseCellBand.width p u
    let n := (haloBoundary s t band a b).card
    let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 n) 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    let k := boundaryHaloRecoveryTarget p (boundaryRecoveryTarget p target) n
    let e := recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u)
    PackedHaloPassEnvelope p l s t u stage 2 a b V Z →
    PackedHaloPassEnvelope p l s t u k e a b V Z →
    liftedCoefficientWidth (2^15*p) q w s t u band ≤ Z →
    packedHaloPreparedInputCost p u l target 2 s t a b V ≤
      familyHaloInteriorGeometryCost p l s t u stage 2 a b+
      familyHaloInteriorGeometryCost p l s t u k e a b+
      50000000*(ssMulConst+1)*t*Z^4 := by
  dsimp only
  intro initial recovery hlift
  let band := PhaseCellBand.width p u
  let n := (haloBoundary s t band a b).card
  let stage := initialSchurTarget p u (boundaryTableBits p (boundaryRecoveryTarget p target) 2 n) 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  have hstages := packedHaloPreparedInputCost_le_stages hst p u l target a b V Z hb initial.positive
    initial.workspace initial.width initial.band
  have hinit := packedHaloInteriorCoefficientsCost_weights_poly hst p l u stage 2 a b V Z ha hb
    initial.positive initial.parameter initial.stage initial.precision initial.ringLog initial.exponent
    initial.width initial.band initial.workspace initial.familyWorkspace hlift initial.candidates initial.keys
  have hwpos : 1 ≤ w := by dsimp only [w,executionWidth]; omega
  have hrec := packedBoundaryRecoveryCost_weights_poly hst p u l target 2 a b V q w Z hb initial.positive
    initial.parameter initial.ringLog initial.exponent initial.precision initial.width hwpos initial.band initial.workspace
    recovery.stage recovery.precision recovery.width recovery.familyWorkspace recovery.candidates recovery.keys
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hcoupling := preparedSharedLocalFeedCouplingIntervalCost_poly (P := 2^15*p) (s := s) (u := u)
    (a := a) (b := b) (origin := a) ht initial.positive hN initial.precision initial.width hwpos initial.band initial.workspace false
  have hpow : Z^3 ≤ Z^4 := Nat.pow_le_pow_right initial.positive (by decide)
  have hscale := Nat.mul_le_mul_left t hpow
  have hS : 1 ≤ ssMulConst+1 := by omega
  have hshared : t*Z^4 ≤ (ssMulConst+1)*t*Z^4 := by
    simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (t*Z^4) hS
  have hn : n ≤ t := (show n ≤ s by
    simpa only [n,ZMod.card] using (haloBoundary s t band a b).card_le_univ).trans hst.le
  have hwidth : w = 2*q+8 := by dsimp only [w,q,executionPrecision,executionWidth]; omega
  have hresidual := preparedResidualSolveCost_poly ht initial.positive hn
    (by rw [←hwidth]; exact initial.width) initial.band
  rw [←hwidth] at hresidual
  dsimp only [q,w,stage,n,band] at hinit hrec hcoupling hresidual
  nlinarith only [hstages,hinit,hrec,hcoupling,hresidual,hscale,hshared]

end IntegerMultBounds.MathlibTM2.Cost
