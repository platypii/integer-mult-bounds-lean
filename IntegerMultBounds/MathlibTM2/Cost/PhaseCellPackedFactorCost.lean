module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundarySetupPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloSolve

/-! Price packed factor disposal and shared setup controls. Factor construction
is retained as an existing bill rather than reproved. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedFactorReleaseCost_le (D : ℕ) : packedFactorReleaseCost D ≤ 448*D+449 := by
  have hcount : packedFactorOwnedIndices.length ≤ 224 := by
    exact (List.length_filter_le _ (List.finRange 224)).trans_eq List.length_finRange
  have hregs : packedFactorOwnedRegs.length = packedFactorOwnedIndices.length := by
    simp only [packedFactorOwnedRegs,List.length_map]
  unfold packedFactorReleaseCost
  rw [hregs]
  nlinarith only [hcount,Nat.mul_le_mul_right D hcount]

theorem packedHaloFinalReleaseCost_poly {q band N t Z : ℕ}
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hN : N ≤ t)
    (hq : q ≤ Z) (hw : 2*q+8 ≤ Z) (hW : 12*band+1 ≤ Z) :
    retirePackedBandTableCost N (12*band+1) (2*q+8)+
      packedFactorReleaseCost (boundaryFactorStockBound q (2*q+8) band N) ≤ 200000*t^2*Z^3 := by
  have hperm := boundaryPermanentSizeBound_poly ht hZ hN hq hw hW
  have hprod := Nat.mul_le_mul (show 12*band ≤ Z by omega) hw
  have htable := Nat.mul_le_mul hN hW
  have hstock : boundaryFactorStockBound q (2*q+8) band N ≤ 100*t*Z^3+Z^2+t*Z := by
    unfold boundaryFactorStockBound
    nlinarith only [hperm,hprod,htable]
  have hrelease := packedFactorReleaseCost_le (boundaryFactorStockBound q (2*q+8) band N)
  have hretire := retirePackedBandTableCost_poly ht hZ hN hW hw
  have h₁₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₂₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₁₂ := Nat.mul_le_mul_left t h₁₂
  have ht₂₃ := Nat.mul_le_mul_left t h₂₃
  have htt : t ≤ t^2 := Nat.le_self_pow (by decide) t
  have htScale := Nat.mul_le_mul_right (Z^3) htt
  have hZScale := Nat.mul_le_mul_left (t^2) h₂₃
  have hunit : 1 ≤ t*Z := Nat.mul_pos ht hZ
  nlinarith only [hstock,hrelease,hretire,ht₁₂,ht₂₃,htScale,hZScale,hunit]

/-- Shared construction and disposal, with the factor arithmetic left intact. -/
theorem packedHaloSetupReleaseCost_poly {p u l target rhsExp s t a b V Z : ℕ} [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hb : b ≤ s) (hZ : 1 ≤ Z) (hV : V ≤ Z) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    q ≤ Z → w ≤ Z → 12*band+1 ≤ Z → publicationGeometryWidth t band ≤ Z →
    packedHaloSetupReleaseCost true p u l target rhsExp s t a b V ≤
      constructedBoundaryFactorCost p u l s t a b (boundaryRecoveryTarget p target) rhsExp+
        300000*t^2*Z^3 := by
  dsimp only
  intro hq hw hW hG
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) rhsExp N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hN : N ≤ t := (show N ≤ s by simpa only [N,ZMod.card] using (haloBoundary s t band a b).card_le_univ).trans hst.le
  have hwidth : w = 2*q+8 := by dsimp only [w,q,executionPrecision,executionWidth]; omega
  have hrelease := packedHaloFinalReleaseCost_poly ht hZ hN hq (by rw [←hwidth]; exact hw) hW
  rw [←hwidth] at hrelease
  have hband : band ≤ Z := by dsimp only [band] at hW ⊢; omega
  have hsT := hst.le
  have haT := ha.trans hst.le
  have hbT := hb.trans hst.le
  have hcontrols :
      (2*(N*publicationGeometryWidth t band+publicationGeometryWidth t band+N)+7)+
        ((s+t+band+a+b)*(4*V+10)+56*V+77) ≤ 10000*t^2*Z^2 := by
    have hmono :
        (2*(N*publicationGeometryWidth t band+publicationGeometryWidth t band+N)+7)+
          ((s+t+band+a+b)*(4*V+10)+56*V+77) ≤
        (2*(t*Z+Z+t)+7)+((t+t+Z+t+t)*(4*Z+10)+56*Z+77) := by gcongr
    have htZ := Nat.mul_le_mul_left t hZ
    have hZt := Nat.mul_le_mul_left Z ht
    have hscale := Nat.mul_le_mul (Nat.le_self_pow (by decide : 2 ≠ 0) t)
      (Nat.le_self_pow (by decide : 2 ≠ 0) Z)
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have hZZt := Nat.mul_le_mul_left (Z^2) (show 1 ≤ t^2 from one_le_pow₀ ht)
    nlinarith only [hmono,htZ,hZt,hscale,hpow,hZZt,ht,hZ]
  have hscale := Nat.mul_le_mul_left (t^2) (Nat.pow_le_pow_right hZ (by decide : 2 ≤ 3))
  dsimp only [packedHaloSetupReleaseCost]
  simp only [ite_true]
  dsimp only [q,w,bits,N,band] at hrelease hcontrols
  nlinarith only [hrelease,hcontrols,hscale]

end IntegerMultBounds.MathlibTM2.Cost
