module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedOriginsSharedWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaStock

/-! Shared interior-class storage composes native setup with one cached numerical reserve. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def replicaClassSharedPush : ℕ :=
  4+mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))+
    mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U))

private theorem classSharedStock_le (a b f g h w o p v d c e : ℕ) :
    3*f+2*g+2*h+(a*w+(c+3*d+1500*v+38)+(b*p+20))+60 ≤
      c+(4+a+b)*(f+g+h+w+o+(p+e)+500*v+d+39) := by
  ring_nf
  omega

private theorem classSharedStock_zero_le (a b tf cV f g h weight o pages adv cached B L w span r : ℕ) :
    let X := B*(L+r)*w+span*w+1
    3*f+2*g+2*h+
      ((a*weight+(cached+3*adv+1500*(B*L*w)+38+tf*0*X)+
        (b*pages+2*((0*(6*(span*w)+13)+6)+(0*(41*(span*w)+13)+4)))+
        (2*a+146)*0*X)+96*0*X+60)+2*((10*cV+19)*0*(B*L*w)) ≤
      cached+(4+a+b)*(f+g+h+
        (weight+o+(pages+(((4*0+4)+((0*(41*(span*w)+13)+4)+(2*0+2)))+
          (4*span*w+2*L*w+4)))+500*B*L*w+adv+39)) := by
  dsimp only
  have hc := classSharedStock_le a b f g h weight o pages (B*L*w) adv cached (10+(4*span*w+2*L*w+4))
  simp only [Nat.mul_zero,Nat.zero_mul,Nat.zero_add,Nat.add_zero]
  nlinarith only [hc]

theorem generatedHaloReplicaClassLinearWorkspace_zero_le (hQ : SS.states ≤ Q)
    (R K p l V origin span L s t u target rhsExp cV : ℕ) :
    generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K p l 0 V origin span L s t u target rhsExp cV ≤
      cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp+
        replicaClassSharedPush (Q := Q) (A := A) (U := U)*
          generatedHaloReplicaSharedTime p l V origin span L s t u target rhsExp := by
  exact classSharedStock_zero_le
    (mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U)))
    (mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := A) (U := U)))
    (1872+cachedOriginsTrafficFactor (P₀ := Empty) (A := A) (U := U) hQ R cV) cV
    (preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L)
    (releasePairedOriginPagesCost (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length V)
    (replicaClassReloadCost p l 0 (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length L s t u target rhsExp)
    (generateReplicaWeightPageCost 0 (2^15*p) s t u (executionPrecision p l target rhsExp) L
      (executionWidth p l target rhsExp) (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length)
    (cachedBatchFromOriginsCost p l 0 L s t u target rhsExp)
    (prepareReplicaPublicationPagesCost V span L (executionWidth p l target rhsExp)
      (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length)
    (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp)
      (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length+
      2*(span*executionWidth p l target rhsExp)+2*(haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length+10)
    (cachedOriginsWorkspace (P₀ := Empty) (A := A) (U := U) hQ R K p l 0 L s t u target rhsExp)
    (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length L
    (executionWidth p l target rhsExp) span (2^l)

@[irreducible] noncomputable def replicaClassSharedWorkspaceConstant : ℕ :=
  cachedOriginsSharedWorkspaceConstant+(1000000*(ssMulConst+1)+8*mtCvKf 10+4000000)

theorem generatedHaloReplicaClassSharedWorkspace_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Z) (L : ℕ)
    (hkey : L ∈ PhaseCellDiscreteGeometry.haloLengthKeys s H.t H.band H.origin (H.origin+H.span))
    (hr : 2^H.l ≤ Z) (hR : R ≤ Z) (hK : K ≤ Z)
    (hpush : cachedOriginsSharedPush (A := A) (U := U) hQ ≤ Z)
    (hclass : replicaClassSharedPush (Q := Q) (A := A) (U := U) ≤ Z)
    (hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ Z)
    (hC : coefficientWorkspaceWidth (2^15*H.p)
      (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ Z) :
    generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K H.p H.l 0 H.metadataWidth
      H.origin H.span L s H.t H.u H.target H.rhsExp cV ≤ replicaClassSharedWorkspaceConstant*Z^11 := by
  have ho := cachedOriginsWorkspace_zero_poly H hQ R K hE L hkey hr hR hK hpush hW hC
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
  have hc := generatedHaloReplicaClassLinearWorkspace_zero_le (A := A) (U := U) hQ R K H.p H.l
    H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp cV
  have hn := Nat.mul_le_mul hclass hgen
  have hs := Nat.mul_le_mul_left (1000000*(ssMulConst+1)+8*mtCvKf 10+4000000)
    (Nat.pow_le_pow_right hE.positive (show 7 ≤ 11 by decide))
  unfold replicaClassSharedWorkspaceConstant
  nlinarith only [ho,hc,hn,hs]

end IntegerMultBounds.MathlibTM2.Cost
