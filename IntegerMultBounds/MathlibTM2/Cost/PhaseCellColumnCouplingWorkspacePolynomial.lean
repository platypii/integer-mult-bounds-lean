module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPacketCouplingWorkspacePolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFeedCouplingWorkspaceBound

/-! Original columns and residual feeds share one packet-coupling space language. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

theorem originalColumnUniformWorkspace_le_feed (R p q s t u : ℕ) :
    originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) R p q s t u ≤
      feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        true R (2^15*p) q (2*q+8) s t u (PhaseCellBand.width p u)+
      10000000*(p+q+s+t+u+PhaseCellBand.width p u+1)*(2*q+9) := by
  unfold originalColumnUniformWorkspace generatedOriginalColumnUniformWorkspace feedCouplingUniformWorkspace
    originalColumnInputsCost releaseColumnSourcesCost installCouplingHeadersCost
  norm_num
  ring_nf
  omega

theorem feedCouplingUniformWorkspace_poly {K P q w s t u band Z : ℕ} (boundary : Bool)
    (hZ : 1 ≤ Z) (htpos : 1 ≤ t) (hst : s ≤ t) (hwpos : 1 ≤ w)
    (hdim : ∀ x ∈ [K,P,q,w,s,t,u,band,2*band+1,
      liftedCoefficientWidth P q w s t u band,publicationGeometryWidth t band,
      publicationGeometryWidth t (2*band)], x ≤ Z)
    (hpush : ∀ x ∈ [packetCoefficientPush (Q := Q) (A := A) (U := U),
      zeroPacketSpatialCouplingRowPush (P₀ := P₀) (Q := Q) (A := A) (U := U),
      spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary,
      couplingGuardPush (Q := Q) (A := A) (U := U),retainedCouplingPacketPush (Q := Q) (A := A) (U := U)],
      x ≤ Z) :
    feedCouplingUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      boundary K P q w s t u band ≤ 10000000*(ssMulConst+1)*Z^5 := by
  have hK := hdim K (by simp)
  have hP := hdim P (by simp)
  have hq := hdim q (by simp)
  have hw := hdim w (by simp)
  have hs := hdim s (by simp)
  have ht := hdim t (by simp)
  have hu := hdim u (by simp)
  have hb := hdim band (by simp)
  have hrows := hdim (2*band+1) (by simp)
  have hV := hdim (liftedCoefficientWidth P q w s t u band) (by simp)
  have hG := hdim (publicationGeometryWidth t band) (by simp)
  have hG₂ := hdim (publicationGeometryWidth t (2*band)) (by simp)
  have hworker := runPreparedPacketCouplingRowsWorkspace_poly (P₀ := P₀) (Q := Q) (A := A) (U := U) hZ hK hP hq hw hwpos hs hb hrows hV
    (hpush _ (by simp)) (hpush _ (by simp))
  have hpacket := buildMarkedRowCoefficientPacketCost_zero_poly htpos hZ hst hP hq hw hu hb hV
  have hpacketScaled := Nat.mul_le_mul (hpush (retainedCouplingPacketPush (Q := Q) (A := A) (U := U)) (by simp)) hpacket
  have hpacketDim := Nat.mul_le_mul_left (Z*(1000000*Z^3)) ht
  have h₂ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have h₁ : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have h₀ : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have hsourceMono : couplingSourceSetupBound s t band w ≤
      4000*(Z+Z+Z+Z+Z+1)*(Z+4)^2+(Z*(28*Z+28)+24)+((Z+Z)*(38*Z+9)+68) := by
    unfold couplingSourceSetupBound maskCouplingSourceCost padCouplingSourceCost
    gcongr
  have hsource : couplingSourceSetupBound s t band w ≤ 1000000*Z^3 := by
    nlinarith only [hsourceMono,h₂,h₁,h₀]
  have hguardMono : couplingGuardSetupBound s t band ≤
      5000*(Z+Z+2*Z+Z+Z+1)*(Z+4)^2+8*Z+6 := by
    unfold couplingGuardSetupBound
    gcongr
  have hguard : couplingGuardSetupBound s t band ≤ 1000000*Z^3 := by
    nlinarith only [hguardMono,h₂,h₁,h₀]
  have hsourceScaled := Nat.mul_le_mul (hpush (spatialCouplingSourcePush (P₀ := P₀) (Q := Q) (A := A) (U := U) boundary) (by simp)) hsource
  have hguardScaled := Nat.mul_le_mul (hpush (couplingGuardPush (Q := Q) (A := A) (U := U)) (by simp)) hguard
  have hretireMono : 3*retireSpatialCouplingSourceCost s band w+500*(s+1)*(w+1) ≤
      3*((Z+2*Z)*(12*Z+9)+12+6*Z+8*Z+10)+500*(Z+1)*(Z+1) := by
    unfold retireSpatialCouplingSourceCost retireCountedLineCost
    gcongr
  have h₄₅ : Z^4 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have h₃₅ : Z^3 ≤ Z^5 := Nat.pow_le_pow_right hZ (by decide)
  have hscale : Z^5 ≤ (ssMulConst+1)*Z^5 := Nat.le_mul_of_pos_left _ (by omega)
  unfold feedCouplingUniformWorkspace
  nlinarith only [hworker,hpacketScaled,hpacketDim,hsourceScaled,hguardScaled,hretireMono,
    h₂,h₁,h₀,h₄₅,h₃₅,hscale]

end IntegerMultBounds.MathlibTM2.Cost
