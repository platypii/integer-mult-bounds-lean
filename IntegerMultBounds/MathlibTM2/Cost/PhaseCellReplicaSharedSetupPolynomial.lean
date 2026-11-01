module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPassEnvelope
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellWeightSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedSetupPolynomial

/-! Shared replica setup reuses the numerical factory bounds; native controls use one envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.Spec.SignedRingProduct IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

/-- All nonnumerical controls of one retained replica class share a polynomial bill. -/
theorem replicaSharedControls_poly {p l V origin span L s t u target rhsExp Z : ℕ}
    (hZ : 1 ≤ Z) (hV : V ≤ Z) (horigin : origin ≤ Z) (hspan : span ≤ Z)
    (hL : L ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z) (hu : u ≤ Z)
    (hP : 2^15*p ≤ Z) (hl : l ≤ Z)
    (hstage : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hw : executionWidth p l target rhsExp ≤ Z)
    (hband : PhaseCellBand.width p u ≤ Z)
    (hend : origin+span ≤ Z)
    (hphase : haloPhaseCount s t origin (origin+span) ≤ Z)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≤ Z)
    (hfamily : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z) :
    let B := (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length
    preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L+
      releasePairedOriginPagesCost B V+replicaClassReloadCost p l 0 B L s t u target rhsExp+
      discardBatchOriginsCost (2^15*p) (executionPrecision p l target rhsExp) t u 0+
      accumulatingGatheredPublicationCost 0 V span L (executionWidth p l target rhsExp) B+
      500*B*L*executionWidth p l target rhsExp+
      (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
        2*(span*executionWidth p l target rhsExp)+2*B+10)+39 ≤ 100000*Z^4 := by
  dsimp only
  have hword : 2*executionPrecision p l target rhsExp+8 = executionWidth p l target rhsExp := by
    unfold executionPrecision executionWidth
    omega
  let B := (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length
  have hmono : preparedPairedLocalHaloClassCost V s t (PhaseCellBand.width p u) origin (origin+span) L+
      releasePairedOriginPagesCost B V+replicaClassReloadCost p l 0 B L s t u target rhsExp+
      discardBatchOriginsCost (2^15*p) (executionPrecision p l target rhsExp) t u 0+
      accumulatingGatheredPublicationCost 0 V span L (executionWidth p l target rhsExp) B+
      500*B*L*executionWidth p l target rhsExp+
      (preparedOriginAdvanceCost V span (executionWidth p l target rhsExp) B+
        2*(span*executionWidth p l target rhsExp)+2*B+10)+39 ≤
      ((104*Z+137)+((Z+Z+Z+Z+Z+Z)*(4*Z+10)+36*Z+61)+
        ((37*Z+16)*tblC Z Z+Z*(12*Z+6)+10)+(62*Z+63))+
      (18*(Z*Z)+11*Z+20)+
      (4*(Z+Z+Z+Z+Z+Z+Z+Z+2*Z+0+Z+Z)+53+(0*(10*(Z*Z)+15)+16*(Z*Z)+9*Z+20))+
      ((4*Z+5)+(4*Z+4*Z+4*Z+19*(Z+Z+Z+Z)+45)+(0*(4*Z+9)+4)+(8*(0*Z)+8)+(2*(Z+Z)+5))+
      (((Z*(4*Z+9)+4)+(((32*Z+41)+(Z*(4*Z+10)+6*Z+10)+
        (Z*(3*tblC Z Z+29*Z+30)+8*Z*Z+11)+(38*Z+39))+37*Z*Z+2*Z+29))+
        (((4*0+4)+(0*(41*(Z*Z)+13)+4+(2*0+2)))+(4*Z*Z+2*Z*Z+4)))+
      500*Z*Z*Z+(((32*Z+41)+(Z*(4*Z+10)+6*Z+10)+
        (Z*(3*tblC Z Z+29*Z+30)+8*Z*Z+11)+(38*Z+39))+2*(Z*Z)+2*Z+10)+39 := by
    unfold preparedPairedLocalHaloClassCost haloClassHeadersCost pairedLocalHaloControllerCost
      releasePairedOriginPagesCost replicaClassReloadCost reloadReplicaFactoryInputCost
      replicaFactoryHeaderCost reloadReplicaOriginPacketsCost discardBatchOriginsCost
      accumulatingGatheredPublicationCost prepareReplicaPublicationPagesCost
      preparedOriginAdvanceCost retainedEncodedPublicationCost symbolEncodedPublicationCost weightWidthCost
    rw [hword]
    dsimp only [B]
    unfold tblC
    gcongr; omega
  apply hmono.trans
  unfold tblC
  have h1 : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  have h2 : Z^2 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h3 : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
  have h0 : 1 ≤ Z^4 := Nat.one_le_pow _ _ hZ
  nlinarith only [h0,h1,h2,h3]

theorem generatedHaloReplicaSharedTime_poly {p l V origin span L s t u target rhsExp Z : ℕ}
    (hZ : 1 ≤ Z) (hV : V ≤ Z) (horigin : origin ≤ Z) (hspan : span ≤ Z)
    (hL : L ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z) (hu : u ≤ Z)
    (hP : 2^15*p ≤ Z) (hl : l ≤ Z)
    (hstage : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hw : executionWidth p l target rhsExp ≤ Z)
    (hband : PhaseCellBand.width p u ≤ Z)
    (hend : origin+span ≤ Z)
    (hphase : haloPhaseCount s t origin (origin+span) ≤ Z)
    (hB : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≤ Z)
    (hfamily : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z)
    (hspos : 1 ≤ s) (hst : s < t) (hr : 2^l ≤ Z)
    (hW : integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionStagePrecision p l target rhsExp+2) 0 ≤ Z)
    (hC : coefficientWorkspaceWidth (2^15*p)
      (integerSetupWidth (2^15*p) (executionPrecision p l target rhsExp)
        (executionStagePrecision p l target rhsExp+2) 0) t u (PhaseCellBand.width p u) L ≤ Z) :
    generatedHaloReplicaSharedTime p l V origin span L s t u target rhsExp ≤
      (1000000*(ssMulConst+1)+8*mtCvKf 10+4000000)*Z^6 := by
  have hc := replicaSharedControls_poly hZ hV horigin hspan hL hs ht hu hP hl hstage hq hw hband hend hphase hB hfamily
  dsimp only at hc
  have hBt : (haloLengthGroup s t (PhaseCellBand.width p u) origin (origin+span) L).length ≤ t :=
    (haloLengthGroup_length_le s t (PhaseCellBand.width p u) origin (origin+span) L).trans (by omega)
  have hweight := sharedBatchWeightSetupCost_poly hZ (by omega : 1 ≤ t) hst.le hBt hP hu hq hL hw hfamily
  have hpZ : p ≤ Z := by omega
  have hb := cachedClosedBatchCost_zero_poly (s := s) (t := t) (u := u) hZ hpZ hl hL hr hw hW
  have hheader := headerGeneratorSetupCost_poly (s := s) hZ hP hstage hq hu hL (by simpa only [Nat.add_assoc] using hW)
    (by simpa only [Nat.add_assoc] using hC)
  have hpow (j : ℕ) (hj : j ≤ 6) : Z^j ≤ Z^6 := Nat.pow_le_pow_right hZ hj
  have htz := Nat.mul_le_mul_right (Z^4) ht
  have hZ5 : Z^5 ≤ Z^6 := hpow 5 (by decide)
  have hscaled := Nat.mul_le_mul_left (8*mtCvKf 10+1000000) (hpow 3 (by decide))
  have hBL := Nat.mul_le_mul hB hL
  unfold generatedHaloReplicaSharedTime releasedReplicaSharedTime cachedBatchFromOriginsCost
    generateReplicaWeightPageCost prepareReplicaFactoryDimensionsCost
  dsimp only
  nlinarith only [hc,hweight,hb,hheader,hscaled,htz,hZ5,hBL,hs,ht,hband,hL,hB,
    hpow 0 (by decide),hpow 1 (by decide),hpow 2 (by decide),hpow 4 (by decide)]

theorem replicaHaloKeySharedTime_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Z) (L : ℕ)
    (hkey : L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span))
    (hr : 2^H.l ≤ Z)
    (hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ Z)
    (hC : coefficientWorkspaceWidth (2^15*H.p)
      (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ Z) :
    replicaHaloKeySharedTime H L ≤ (1000000*(ssMulConst+1)+8*mtCvKf 10+4100000)*Z^6 := by
  have hd := hE.keys L hkey
  have hs : s ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have ht : H.t ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hL : L ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hspan : H.span ≤ Z := by have := H.span_fit; omega
  have horigin : H.origin ≤ Z := by have := H.span_fit; omega
  have hend : H.origin+H.span ≤ Z := H.span_fit.trans hs
  have hphase : haloPhaseCount s H.t H.origin (H.origin+H.span) ≤ Z := hd _ (by simp [packedHaloKeyDimensions])
  have hB : (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length ≤ Z :=
    hd _ (by simp [packedHaloKeyDimensions,ReplicaHaloProblem.band])
  have hg := generatedHaloReplicaSharedTime_poly hE.positive hE.workspace horigin hspan hL hs ht
    hE.exponent hE.parameter hE.ringLog hE.stage hE.precision hE.width hE.band hend hphase hB
    hE.familyWorkspace (NeZero.pos s) H.s_lt_t hr hW hC
  have hpaired : preparedPairedLocalHaloClassCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span) L ≤
      generatedHaloReplicaSharedTime H.p H.l H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp := by
    unfold generatedHaloReplicaSharedTime
    dsimp only [ReplicaHaloProblem.band]
    omega
  have hb : replicaHaloKeySharedTime H L ≤ replicaLengthKeyParserCost H.metadataWidth L+
      (generatedHaloReplicaSharedTime H.p H.l H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp+23)+(2*L+2) := by
    unfold replicaHaloKeySharedTime
    split_ifs <;> omega
  have h1 : Z ≤ Z^6 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^6 := Nat.one_le_pow _ _ hE.positive
  unfold replicaLengthKeyParserCost at hb
  nlinarith only [hb,hg,hL,hE.workspace,h1,h0]

theorem placedHaloLengthKeysCost_poly {s t band a b V Z : ℕ} (hZ : 1 ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (hband : band ≤ Z) (ha : a ≤ Z) (hb : b ≤ Z) (hV : V ≤ Z) :
    placedHaloLengthKeysCost s t band a b V ≤ 300000*Z^3 := by
  have hm : placedHaloLengthKeysCost s t band a b V ≤ placedHaloLengthKeysCost Z Z Z Z Z Z := by
    unfold placedHaloLengthKeysCost retainedHaloLengthKeysCost preparedHaloLengthCandidatesCost haloHeadersCost tblC
    gcongr
  apply hm.trans
  unfold placedHaloLengthKeysCost retainedHaloLengthKeysCost preparedHaloLengthCandidatesCost haloHeadersCost tblC
  have h0 : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have h1 : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have h2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  nlinarith only [h0,h1,h2]

/-- The real six-key schedule pays shared numerical setup once per key. -/
theorem initializedReplicaHaloSharedTime_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Z) (ht : H.t+2 ≤ Z) (hr : 2^H.l ≤ Z)
    (hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ Z)
    (hC : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span),
      coefficientWorkspaceWidth (2^15*H.p)
        (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ Z) :
    initializedReplicaHaloSharedTime H ≤
      (6*(1000000*(ssMulConst+1)+8*mtCvKf 10+4100000)+400000)*Z^6 := by
  let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
  let K := 1000000*(ssMulConst+1)+8*mtCvKf 10+4100000
  have hsum := List.sum_le_length_nsmul
    (keys.map (fun L => replicaHaloKeySharedTime H L+3)) (K*Z^6+3) (by
      intro x hx
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
      exact Nat.add_le_add_right (replicaHaloKeySharedTime_poly H hE L hL hr hW (hC L hL)) 3)
  have hsum' : (keys.map (fun L => replicaHaloKeySharedTime H L+3)).sum ≤ 6*(K*Z^6+3) :=
    hsum.trans (by simpa only [List.length_map,nsmul_eq_mul,Nat.cast_id] using
      Nat.mul_le_mul_right (K*Z^6+3) (haloLengthKeys_length_le s H.t H.band H.origin (H.origin+H.span)))
  have hs : s ≤ Z := by have := H.s_lt_t; omega
  have ha : H.origin ≤ Z := by have := H.span_fit; omega
  have hb : H.origin+H.span ≤ Z := H.span_fit.trans hs
  have hm := placedHaloLengthKeysCost_poly hE.positive hs (by omega : H.t ≤ Z) hE.band ha hb hE.workspace
  have h3 : Z^3 ≤ Z^6 := Nat.pow_le_pow_right hE.positive (by decide)
  have h0 : 1 ≤ Z^6 := Nat.one_le_pow _ _ hE.positive
  change 10+placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
    ((keys.map (fun L => replicaHaloKeySharedTime H L+3)).sum+2) ≤ (6*K+400000)*Z^6
  dsimp only [ReplicaHaloProblem.band]
  nlinarith only [hsum',hm,h3,h0]

end IntegerMultBounds.MathlibTM2.Cost
