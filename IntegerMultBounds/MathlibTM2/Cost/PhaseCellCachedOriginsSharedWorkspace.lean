module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInteriorSharedNumericalWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedOriginsStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaSharedSetupPolynomial

/-! Shared cached origins need native setup/retirement stock and one numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def cachedOriginsSharedPush (hQ : SS.states ≤ Q) : ℕ :=
  mnProgPush (discardBatchOrigins (P₀ := Empty) (Q := Q) (A := A) (U := U))+
    mnProgPush (cachedGeneratedBatchSetup (P₀ := Empty) (A := A) (U := U) hQ)+
    mnProgPush (releaseBatchRuntime (P₀ := Empty) (Q := Q) (A := A) (U := U))

theorem cachedOriginsWorkspace_zero_le (hQ : SS.states ≤ Q) (R K p l L s t u target rhsExp : ℕ) :
    cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp ≤
      cachedOriginsSharedPush (A := A) (U := U) hQ*cachedBatchFromOriginsCost p l 0 L s t u target rhsExp+
      stagedCellWorkspace R K (executionPrecision p l target rhsExp) (sourceExponent l target rhsExp)
        (8*p+1) l (executionWidth p l target rhsExp) 0 L := by
  have hn (a b c d x y v n : ℕ) (hd : d ≤ n) (hx : x ≤ n) (hy : y ≤ n) :
      a*d+(b*x+v+c*y) ≤ (a+b+c)*n+v := by
    have ha := Nat.mul_le_mul_left a hd
    have hb := Nat.mul_le_mul_left b hx
    have hc := Nat.mul_le_mul_left c hy
    nlinarith only [ha,hb,hc]
  unfold cachedOriginsWorkspace cachedClosedWorkspace cachedSetupWorkspace cachedOriginsSharedPush
  dsimp only
  apply hn
  · unfold cachedBatchFromOriginsCost; exact Nat.le_add_right _ _
  · unfold cachedBatchFromOriginsCost cachedClosedBatchCost
    dsimp only
    omega
  · unfold cachedBatchFromOriginsCost cachedClosedBatchCost
    dsimp only
    omega

@[irreducible] noncomputable def cachedOriginsSharedWorkspaceConstant : ℕ :=
  4*ringSharedWorkspaceConstant+1000000*(ssMulConst+1)+
    (1000000*(ssMulConst+1)+8*mtCvKf 10+4000000)

theorem cachedOriginsWorkspace_zero_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K : ℕ)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Z) (L : ℕ)
    (hkey : L ∈ PhaseCellDiscreteGeometry.haloLengthKeys s H.t H.band H.origin (H.origin+H.span))
    (hr : 2^H.l ≤ Z) (hR : R ≤ Z) (hK : K ≤ Z)
    (hpush : cachedOriginsSharedPush (A := A) (U := U) hQ ≤ Z)
    (hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ Z)
    (hC : coefficientWorkspaceWidth (2^15*H.p)
      (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ Z) :
    cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K H.p H.l 0 L s H.t H.u H.target H.rhsExp ≤
      cachedOriginsSharedWorkspaceConstant*Z^11 := by
  have hd := hE.keys L hkey
  have hs : s ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have ht : H.t ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hL : L ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hspan : H.span ≤ Z := by have := H.span_fit; omega
  have horigin : H.origin ≤ Z := by have := H.span_fit; omega
  have hend : H.origin+H.span ≤ Z := H.span_fit.trans hs
  have hphase : PhaseCellDiscreteGeometry.haloPhaseCount s H.t H.origin (H.origin+H.span) ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hB : (PhaseCellDiscreteGeometry.haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length ≤ Z :=
    hd _ (by simp [packedHaloKeyDimensions,ReplicaHaloProblem.band])
  have hgen := generatedHaloReplicaSharedTime_poly hE.positive hE.workspace horigin hspan hL hs ht
    hE.exponent hE.parameter hE.ringLog hE.stage hE.precision hE.width hE.band hend hphase hB
    hE.familyWorkspace (NeZero.pos s) H.s_lt_t hr hW hC
  have htime : cachedBatchFromOriginsCost H.p H.l 0 L s H.t H.u H.target H.rhsExp ≤
      generatedHaloReplicaSharedTime H.p H.l H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp := by
    unfold generatedHaloReplicaSharedTime releasedReplicaSharedTime
    dsimp only
    omega
  have hnumeric := stagedCellWorkspace_zero_poly
    (q := executionPrecision H.p H.l H.target H.rhsExp)
    (cExp := sourceExponent H.l H.target H.rhsExp) (e := 8*H.p+1) (l := H.l)
    (w := executionWidth H.p H.l H.target H.rhsExp) hE.positive hR hK
    (by unfold executionPrecision executionExponent inputExponent sourceExponent; omega)
    (by unfold executionPrecision executionExponent inputExponent sourceExponent; omega)
    (by unfold executionWidth executionPrecision executionExponent inputExponent sourceExponent; omega)
    (by unfold executionWidth; omega) hE.width hL hr (by
      have hw := hE.width
      simp only [executionPrecision,executionWidth,executionExponent,inputExponent,sourceExponent] at hw ⊢
      omega)
  have hresource := cachedOriginsWorkspace_zero_le (A := A) (U := U) hQ R K H.p H.l L s H.t H.u H.target H.rhsExp
  have hn := Nat.mul_le_mul hpush (htime.trans hgen)
  have hpow := Nat.pow_le_pow_right hE.positive (show 7 ≤ 11 by decide)
  have hscale := Nat.mul_le_mul_left
    (1000000*(ssMulConst+1)+8*mtCvKf 10+4000000) hpow
  unfold cachedOriginsSharedWorkspaceConstant
  nlinarith only [hresource,hnumeric,hn,hscale]

end IntegerMultBounds.MathlibTM2.Cost
