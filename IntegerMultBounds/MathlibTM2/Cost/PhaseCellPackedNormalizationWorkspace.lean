module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedWorkspaceCost

/-! Scalar normalization and the complex wrapper add only polynomial shared
storage to the geometry solver's already certified workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem preparedNormalizePackedBatchCost_zero_poly
    {B p u l target s t a b W L Z : ℕ} [NeZero s]
    (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t) (hB : B ≤ Z) (hp : p ≤ Z)
    (hW : W ≤ Z) (hL : L ≤ t) (hband : PhaseCellBand.width p u ≤ Z)
    (hnative : 8*inverseExecutionExponent p l target
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8 ≤ Z) :
    preparedNormalizePackedBatchCost B p u l target s t a b W 0 L ≤ 1000000*t*Z^3 := by
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ t :=
    (show (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s by
      simpa only [ZMod.card] using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hs
  have hbitsP : Nat.size (8*p) ≤ 8*p := Nat.size_le.mpr Nat.lt_two_pow_self
  have hbitsN : Nat.size (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ t :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hN
  have hbitsBand : Nat.size (2*PhaseCellBand.width p u+1) ≤ 2*Z+1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hbits4 : Nat.size (4*p) ≤ 4*p := Nat.size_le.mpr Nat.lt_two_pow_self
  have htZ := Nat.mul_le_mul_left t hZ
  have hZt := Nat.mul_le_mul_left Z ht
  have hatoms : inverseScalarAtoms p s t u a b+(4*Nat.size (4*p)+39) ≤ 300*t*Z := by
    unfold inverseScalarAtoms inversePrecisionAtoms
    nlinarith only [hbitsP,hbitsN,hbitsBand,hbits4,hp,hband,hs,htZ,hZt,ht,hZ]
  have htable : tblC B 0 ≤ 800*Z^2 := by
    have hsq := Nat.pow_le_pow_left (show B+4 ≤ 5*Z by omega) 2
    unfold tblC
    nlinarith only [hsq]
  have hsetup := Nat.mul_le_mul hatoms htable
  have hsub : W-(2*p+13) ≤ Z := (Nat.sub_le _ _).trans hW
  have hnorm : normalizePackedBatchCost B
      (8*inverseExecutionExponent p l target (haloBoundary s t (PhaseCellBand.width p u) a b).card
        (PhaseCellBand.width p u)+8) p W 0 L ≤
      13*(800*Z^2)+16*Z+44*Z+54+
        (4*Z+4*(2*Z+13)+2*Z+24+6+8*Z+t*(6*(2*Z+13)+9)+2*(2*Z+13)+17) := by
    unfold normalizePackedBatchCost roundPackedKeyCost publishRoundedKeyCost widenPackedKeyCost widenPackedPrefixCost
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    gcongr
  have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have ht₂ := Nat.mul_le_mul_left t h₂
  have ht₃ := Nat.mul_le_mul_left t h₃
  have hZ₃t := Nat.mul_le_mul_left (Z^3) ht
  unfold preparedNormalizePackedBatchCost
  dsimp only
  nlinarith only [hsetup,hnorm,h₂,h₃,ht₂,ht₃,hZ₃t,htZ,hZt,ht,hZ]

/-- The complete wrapper's shared bill is the geometry workspace plus bounded
scalar setup, row headers, conversion controls and cleanup. -/
theorem packedKeyNormalizedWorkspace_zero_le_geometry
    {B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius Z : ℕ}
    [NeZero s] (ht : 1 ≤ t) (hZ : 1 ≤ Z) (hs : s ≤ t)
    (hB : B ≤ Z) (hp : p ≤ Z) (hq : q ≤ Z) (hW : W ≤ Z) (hband : PhaseCellBand.width p u ≤ Z)
    (hnative : 8*inverseExecutionExponent p l targetOut
      (haloBoundary s t (PhaseCellBand.width p u) a b).card (PhaseCellBand.width p u)+8 ≤ Z) :
    packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0 ≤
      packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        2000000*t*Z^3 := by
  let L := coreLength s coreWidth k
  have hL : L ≤ t := (Nat.min_le_right _ _).trans ((Nat.sub_le s _).trans hs)
  have hnorm := preparedNormalizePackedBatchCost_zero_poly ht hZ hs hB hp hW hL hband hnative
  have hd : q-p-1 ≤ Z := (Nat.sub_le _ _).trans ((Nat.sub_le q p).trans hq)
  have hsub : W-(2*q+8) ≤ Z := (Nat.sub_le _ _).trans hW
  have hrest : (2*q+8)-(q-p-1) ≤ 2*Z+8 := (Nat.sub_le _ _).trans (by omega)
  have hinput : packedKeyInputCost p q W 0 (b-a) ≤ 10000*Z := by
    unfold packedKeyInputCost packedInputConversionCost
    simp only [Nat.zero_mul,Nat.mul_zero,Nat.add_zero,Nat.zero_add]
    nlinarith only [hq,hp,hW,hd,hsub,hrest,hZ]
  let controls := preparePackedCoreRowsCost B q L+packedKeyInputCost p q W 0 (b-a)+214*B+
    2*L*((2*q+8)+1)+281
  have hcontrols : controls ≤ 100000*t*Z^2 := by
    have hmono : controls ≤ preparePackedCoreRowsCost Z Z t+10000*Z+214*Z+2*t*((2*Z+8)+1)+281 := by
      dsimp only [controls]
      unfold preparePackedCoreRowsCost
      gcongr
    unfold preparePackedCoreRowsCost at hmono
    have htZ := Nat.mul_le_mul_left t hZ
    have hZt := Nat.mul_le_mul_left Z ht
    have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have hscale := Nat.mul_le_mul_left t hpow
    nlinarith only [hmono,htZ,hZt,hscale,hZ,ht]
  have heq : packedKeyNormalizedWorkspace B p q W u l s t a b V boundaryTarget finalTarget rhsExp targetOut coreWidth k radius 0 =
      packedHaloGeometryWorkspace p u l s t a b V boundaryTarget finalTarget rhsExp coreWidth k radius 0+
        preparedNormalizePackedBatchCost B p u l targetOut s t a b W 0 L+controls := by
    simp only [packedKeyNormalizedWorkspace,packedKeyComplexWorkspace,Nat.mul_zero,Nat.zero_mul]
    dsimp only [controls,L]
    ring
  rw [heq]
  have hscale := Nat.mul_le_mul_left t (Nat.pow_le_pow_right hZ (by decide : 2 ≤ 3))
  nlinarith only [hnorm,hcontrols,hscale]

end IntegerMultBounds.MathlibTM2.Cost
