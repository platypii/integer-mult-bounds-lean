module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaSharedSetupPolynomial

/-! Computed factory widths fit a quadratic enlargement of the common pass envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem PackedHaloPassEnvelope.mono {p l s t u target rhsExp a b V Y Z : ℕ}
    (h : PackedHaloPassEnvelope p l s t u target rhsExp a b V Y) (hYZ : Y ≤ Z) :
    PackedHaloPassEnvelope p l s t u target rhsExp a b V Z :=
  ⟨h.positive.trans hYZ,h.parameter.trans hYZ,h.stage.trans hYZ,h.precision.trans hYZ,
    h.ringLog.trans hYZ,h.exponent.trans hYZ,h.width.trans hYZ,h.band.trans hYZ,
    h.workspace.trans hYZ,h.familyWorkspace.trans hYZ,
    fun L hL => (h.candidates L hL).trans hYZ,
    fun L hL x hx => (h.keys L hL x hx).trans hYZ⟩

theorem PackedHaloPassEnvelope.factoryWidths {s Y : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Y) (ht : H.t+2 ≤ Y) :
    integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ 64*Y^2 ∧
      ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span),
        coefficientWorkspaceWidth (2^15*H.p)
          (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ 64*Y^2 := by
  have hY := hE.positive
  have hY2 : Y ≤ Y^2 := Nat.le_self_pow (by decide) Y
  have h1 : 1 ≤ Y^2 := Nat.one_le_pow _ _ hY
  have hP := hE.parameter
  have hM := hE.stage
  have hq : H.precision ≤ Y := hE.precision
  have hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ 9*Y^2 := by
    have hstage : H.stage+3 ≤ 3*Y := by change H.stage+1 ≤ Y at hM; omega
    have hh := Nat.mul_le_mul hP hstage
    unfold integerSetupWidth
    change (2^15*H.p)*(H.stage+3)+H.precision+0+5 ≤ 9*Y^2
    nlinarith only [hh,hq,hY2,h1]
  have hC : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span),
      coefficientWorkspaceWidth (2^15*H.p)
        (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ 64*Y^2 := by
    intro L hL
    have hlength : L ≤ Y := hE.keys L hL L (by simp [packedHaloKeyDimensions])
    have htbits : Nat.size H.t ≤ Y := (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
    have hubits : Nat.size H.u ≤ Y := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hE.exponent
    have hLbits : Nat.size L ≤ Y := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hlength
    have hbbits : Nat.size H.band ≤ Y := (Nat.size_le.mpr Nat.lt_two_pow_self).trans hE.band
    unfold coefficientWorkspaceWidth
    nlinarith only [hW,hP,htbits,hubits,hLbits,hbbits,hY2,h1]
  exact ⟨hW.trans (Nat.mul_le_mul_right (Y^2) (by decide : 9 ≤ 64)),hC⟩

theorem initializedReplicaHaloSharedTime_envelope_le {s Y : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Y) (ht : H.t+2 ≤ Y) (hr : 2^H.l ≤ Y) :
    initializedReplicaHaloSharedTime H ≤
      ((6*(1000000*(ssMulConst+1)+8*mtCvKf 10+4100000)+400000)*64^6)*Y^12 := by
  have hY := hE.positive
  have hY2 : Y ≤ Y^2 := Nat.le_self_pow (by decide) Y
  have hYZ : Y ≤ 64*Y^2 := by omega
  obtain ⟨hW,hC⟩ := hE.factoryWidths H ht
  have hc := initializedReplicaHaloSharedTime_poly H (hE.mono hYZ) (ht.trans hYZ) (hr.trans hYZ)
    hW hC
  have heq : (64*Y^2)^6 = 64^6*Y^12 := by ring
  rw [heq] at hc
  simpa only [Nat.mul_assoc] using hc

end IntegerMultBounds.MathlibTM2.Cost
