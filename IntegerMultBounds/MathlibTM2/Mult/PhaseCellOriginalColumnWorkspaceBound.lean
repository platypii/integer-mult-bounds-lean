module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellArbitraryOriginalColumnStock
import Mathlib.Tactic.GCongr

/-! One original-column reserve covers every selected coordinate without enumerating rows. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {Q A : ℕ} {P₀ U : Type}

def couplingSourceSetupBound (s t band w : ℕ) : ℕ :=
  4000*(s+t+band+s+s+1)*(publicationGeometryWidth t band+4)^2+
    maskCouplingSourceCost s w+padCouplingSourceCost s band w

def couplingGuardSetupBound (s t band : ℕ) : ℕ :=
  5000*(s+t+2*band+s+s+1)*(publicationGeometryWidth t (2*band)+4)^2+8*band+6

theorem prepareSpatialCouplingSourceCost_le_uniform (s t band a b w : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) :
    prepareSpatialCouplingSourceCost s t band a b w ≤ couplingSourceSetupBound s t band w := by
  have h := closedCouplingSourceMaskCost_le s t band a b
  unfold prepareSpatialCouplingSourceCost prepareMaskedCouplingSourceCost couplingSourceSetupBound
  have hmask : closedCouplingSourceMaskCost s t band a b ≤
      4000*(s+t+band+s+s+1)*(publicationGeometryWidth t band+4)^2 := by
    apply h.trans
    gcongr
  omega

theorem prepareCouplingGuardCost_le_uniform (s t band a b : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) :
    prepareCouplingGuardCost s t band a b ≤ couplingGuardSetupBound s t band := by
  have h := closedRecoveryGuardMaskCost_le s t (2*band) a b
  unfold prepareCouplingGuardCost generateRecoveryCouplingMaskCost couplingGuardSetupBound
  have hmask : closedRecoveryGuardMaskCost s t (2*band) a b ≤
      5000*(s+t+2*band+s+s+1)*(publicationGeometryWidth t (2*band)+4)^2 := by
    apply h.trans
    gcongr
  omega

@[irreducible] def generatedOriginalColumnUniformWorkspace (R p q w s t u : ℕ) : ℕ :=
  let band := PhaseCellBand.width p u
  3*originalColumnInputsCost s w q+
    ((3*(26*s*w+9*s+26)+
      ((spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) true*
          couplingSourceSetupBound s t band w+
        ((couplingGuardPush (Q := Q) (A := A) (U := U)*couplingGuardSetupBound s t band+
          (retainedCouplingPacketPush (Q := Q) (A := A) (U := U)*
              buildMarkedRowCoefficientPacketCost (2^15*p) q w s t u band 0+
            runPreparedPacketCouplingRowsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
              R (2^15*p) q w s t u band))+
          3*retireSpatialCouplingSourceCost s band w))+
        3*(12*s*w+9*s+12)))+3*releaseColumnSourcesCost s w)

theorem generatedOriginalColumnWorkspace_le_uniform (R p q w s t u a b : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) :
    generatedOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q w s t u a b ≤
      generatedOriginalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q w s t u := by
  have hs := prepareSpatialCouplingSourceCost_le_uniform s t (PhaseCellBand.width p u) a b w ha hb
  have hg := prepareCouplingGuardCost_le_uniform s t (PhaseCellBand.width p u) a b ha hb
  unfold generatedOriginalColumnWorkspace borrowedCouplingPassWorkspace spatialCouplingRowsWorkspace
    runSpatialCouplingRowsWorkspace generatedOriginalColumnUniformWorkspace
  dsimp only
  gcongr

@[irreducible] def originalColumnUniformWorkspace (R p q s t u : ℕ) : ℕ :=
  3*(4*s+4)+(3*(4*s+4)+(1+
    (8*installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) s s+
      (3*(4*s+4)+generatedOriginalColumnUniformWorkspace
        (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q (2*q+8) s t u))))

theorem arbitraryOriginalColumnWorkspace_le_uniform (R p q s t u j : ℕ) (hj : j < s) :
    arbitraryOriginalColumnWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u j ≤
      originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u := by
  have hcore := generatedOriginalColumnWorkspace_le_uniform (P₀ := P₀) (Q := Q) (A := A) (U := U)
    R p q (2*q+8) s t u j (j+1) hj.le (by omega)
  have hheader : installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) j (j+1) ≤
      installCouplingHeadersCost (2^15*p) q s t u (PhaseCellBand.width p u) s s := by
    unfold installCouplingHeadersCost
    omega
  unfold arbitraryOriginalColumnWorkspace restoredOriginalColumnWorkspace originalColumnUniformWorkspace
  gcongr

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
