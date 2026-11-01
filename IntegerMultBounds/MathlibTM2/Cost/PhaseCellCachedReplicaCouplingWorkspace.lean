module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaCouplingResidualStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedCouplingWorkspacePolynomial

/-! A replica row reuses the interval worker's polynomial scratch. The bound
is independent of replica count and applies before staging/loop composition. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem cachedReplicaLocalCouplingWorkspace_poly {P K q w s t u band a b origin N V Z : ℕ}
    (hZ : 1 ≤ Z) (hK : K ≤ Z) (hw : w ≤ Z) (hN : N ≤ Z) (hV : V ≤ Z)
    (hband : band ≤ Z) (hrows : 2*band+1 ≤ Z)
    (hpage : (couplingCoefficientPageInterval P q s t u band a b origin N).length ≤ Z)
    (hprepare : mnProgPush (cachedPreparedLocalRibbon (P := Empty) (Q := Q) (A := A) (U := U) 159) ≤ Z)
    (hrelease : mnProgPush (releaseCouplingRibbon (P := Empty) (Q := Q) (A := A) (U := U)) ≤ Z)
    (hfeed : mnProgPush (feedPackedCouplingResult (P₀ := Empty) (Q := Q) (A := A) (U := U)) ≤ Z) :
    cachedReplicaLocalCouplingWorkspace (Q := Q) (A := A) (U := U) P K q w s t u band a b origin N V+
      2*finishReplicaCouplingRowCost (N*w) ≤ 400000*(ssMulConst+1)*Z^4 := by
  have hl := cachedLocalCouplingWorkspace_poly hZ hK hw hN hV hband hrows hpage hprepare hrelease
  have hnw := Nat.mul_le_mul hN hw
  have hfeedCost : 28*N*w+36*N+11*V+26 ≤ 28*Z^2+47*Z+26 := by nlinarith only [hnw,hN,hV]
  have hf := Nat.mul_le_mul hfeed hfeedCost
  have hfinish : 2*finishReplicaCouplingRowCost (N*w) ≤ 24*Z^2+24 := by
    unfold finishReplicaCouplingRowCost
    nlinarith only [hnw]
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  have hs : Z^4 ≤ (ssMulConst+1)*Z^4 := Nat.le_mul_of_pos_left _ (by omega)
  unfold cachedReplicaLocalCouplingWorkspace
  nlinarith only [hl,hf,hfinish,h3,h2,h1,h0,hs]

end IntegerMultBounds.MathlibTM2.Cost
