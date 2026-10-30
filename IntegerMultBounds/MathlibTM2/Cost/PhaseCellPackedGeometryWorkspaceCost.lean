module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWorkspaceCost

/-! The zero-replica geometry workspace is one setup/disposal bill, one live
numerical iteration and polynomial header/output storage. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem packedHaloGeometryWorkspace_zero_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p u l target a b V coreWidth k radius Z : ℕ) (hb : b ≤ s) (hZ : 1 ≤ Z) (hV : V ≤ Z)
    (hhalo : coreLength s coreWidth k+2*radius ≤ b-a) :
    let band := PhaseCellBand.width p u
    let N := (haloBoundary s t band a b).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
    let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
    let w := executionWidth p l (initialSchurTarget p u bits 2) 2
    q ≤ Z → w ≤ Z →
    packedHaloGeometryWorkspace p u l s t a b V (boundaryRecoveryTarget p target) target 2 coreWidth k radius 0 ≤
      packedHaloSetupReleaseCost true p u l target 2 s t a b V+
        packedHaloPreparedInputCost p u l target 2 s t a b V+10000*t*Z^2 := by
  dsimp only
  intro hq hw
  let band := PhaseCellBand.width p u
  let N := (haloBoundary s t band a b).card
  let bits := boundaryTableBits p (boundaryRecoveryTarget p target) 2 N
  let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
  let w := executionWidth p l (initialSchurTarget p u bits 2) 2
  let L := coreLength s coreWidth k
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hlength : b-a ≤ t := (Nat.sub_le b a).trans (hb.trans hst.le)
  have hcore : L ≤ t := by dsimp only [L]; omega
  have hradius : radius ≤ t := by omega
  have hvolume : L+2*radius ≤ t := by dsimp only [L]; omega
  let controls := packedFreshOutputCost V (b-a) w+prepareCoreDimensionsCost V (L+2*radius) radius+
    2*V+8*q+2*w+2*(radius+L)+100*((L+2*radius)*w+1)+22
  have hcontrols : controls ≤ 10000*t*Z^2 := by
    have hmono : controls ≤ packedFreshOutputCost Z t Z+prepareCoreDimensionsCost Z t t+
        2*Z+8*Z+2*Z+2*(t+t)+100*(t*Z+1)+22 := by
      dsimp only [controls]
      unfold packedFreshOutputCost prepareCoreDimensionsCost
      gcongr
    unfold packedFreshOutputCost prepareCoreDimensionsCost at hmono
    have htZ := Nat.mul_le_mul_left t hZ
    have hZt := Nat.mul_le_mul_left Z ht
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have hscale := Nat.mul_le_mul_left t hpow
    nlinarith only [hmono,htZ,hZt,hscale,hZ,ht]
  have heq : packedHaloGeometryWorkspace p u l s t a b V (boundaryRecoveryTarget p target) target 2 coreWidth k radius 0 =
      packedHaloSetupReleaseCost true p u l target 2 s t a b V+
        packedHaloPreparedInputCost p u l target 2 s t a b V+controls := by
    simp only [packedHaloGeometryWorkspace,packedHaloSetupReleaseCost,ite_true,Nat.mul_zero,Nat.zero_mul]
    dsimp only [controls,q,w,bits,N,band,L]
    ring
  rw [heq]
  exact Nat.add_le_add_left hcontrols _

end IntegerMultBounds.MathlibTM2.Cost
