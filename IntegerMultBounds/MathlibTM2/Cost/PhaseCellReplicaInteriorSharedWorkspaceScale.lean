module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaInteriorSharedWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaSharedSetupScale

/-! Actual computed factory widths and fixed push coefficients determine shared interior stock. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem replicaInteriorSharedWorkspace_envelope_le {s Y : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Y) (ht : H.t+2 ≤ Y) (hr : 2^H.l ≤ Y)
    (hR : R ≤ Y) (hK : K ≤ Y)
    (hpush : cachedOriginsSharedPush (A := A) (U := U) hQ ≤ Y)
    (hclass : replicaClassSharedPush (Q := Q) (A := A) (U := U) ≤ Y) :
    replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cV ≤
      (replicaInteriorSharedWorkspaceConstant*64^11)*Y^22 := by
  have hY2 : Y ≤ Y^2 := Nat.le_self_pow (by decide) Y
  have hYZ : Y ≤ 64*Y^2 := by have := hE.positive; omega
  obtain ⟨hW,hC⟩ := hE.factoryWidths H ht
  have hc := replicaInteriorSharedWorkspace_poly H hQ R K cV (hE.mono hYZ) (ht.trans hYZ) (hr.trans hYZ)
    (hR.trans hYZ) (hK.trans hYZ) (hpush.trans hYZ) (hclass.trans hYZ) hW hC
  have heq : (64*Y^2)^11 = 64^11*Y^22 := by rw [mul_pow,←pow_mul]
  rw [heq] at hc
  simpa only [Nat.mul_assoc] using hc

end IntegerMultBounds.MathlibTM2.Cost
