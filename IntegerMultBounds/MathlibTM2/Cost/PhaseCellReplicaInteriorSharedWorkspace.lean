module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaClassSharedWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCachedRecoveryWorkspace

/-! One shared polynomial reserve covers the actual six-key interior workspace schedule. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem replicaHaloKeySharedWorkspace_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
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
    replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV ≤
      (replicaClassSharedWorkspaceConstant+1000)*Z^11 := by
  have hc := generatedHaloReplicaClassSharedWorkspace_poly H hQ R K cV hE L hkey hr hR hK hpush hclass hW hC
  have hpaired : 3*preparedPairedLocalHaloClassCost H.metadataWidth s H.t H.band H.origin (H.origin+H.span) L ≤
      generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K H.p H.l 0 H.metadataWidth
        H.origin H.span L s H.t H.u H.target H.rhsExp cV := by
    have hh (a b c d e : ℕ) : a ≤ a+b+c+d+e := by omega
    exact hh _ _ _ _ _
  have hb : replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV ≤
      2*replicaLengthKeyParserCost H.metadataWidth L+
        (generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K H.p H.l 0 H.metadataWidth
          H.origin H.span L s H.t H.u H.target H.rhsExp cV+40) := by
    unfold replicaHaloKeySharedWorkspace
    split_ifs
    · exact Nat.add_le_add_left (Nat.add_le_add_right hpaired 40) _
    · exact Nat.add_le_add_left (Nat.le_add_right _ 40) _
  have hL : L ≤ Z := hE.keys L hkey L (by simp [packedHaloKeyDimensions])
  have hV := hE.workspace
  have h1 : Z ≤ Z^11 := Nat.le_self_pow (by decide) Z
  have h0 : 1 ≤ Z^11 := Nat.one_le_pow _ _ hE.positive
  unfold replicaLengthKeyParserCost at hb
  nlinarith only [hb,hc,hL,hV,h1,h0]

@[irreducible] noncomputable def replicaInteriorSharedWorkspaceConstant : ℕ :=
  6*(replicaClassSharedWorkspaceConstant+1000)+1000000

theorem replicaInteriorSharedWorkspace_poly {s Z : ℕ} [NeZero s] (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ)
    (hE : PackedHaloPassEnvelope H.p H.l s H.t H.u H.target H.rhsExp H.origin
      (H.origin+H.span) H.metadataWidth Z) (ht : H.t+2 ≤ Z) (hr : 2^H.l ≤ Z)
    (hR : R ≤ Z) (hK : K ≤ Z)
    (hpush : cachedOriginsSharedPush (A := A) (U := U) hQ ≤ Z)
    (hclass : replicaClassSharedPush (Q := Q) (A := A) (U := U) ≤ Z)
    (hW : integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0 ≤ Z)
    (hC : ∀ L ∈ haloLengthKeys s H.t H.band H.origin (H.origin+H.span),
      coefficientWorkspaceWidth (2^15*H.p)
        (integerSetupWidth (2^15*H.p) H.precision (H.stage+2) 0) H.t H.u H.band L ≤ Z) :
    replicaInteriorSharedWorkspace (A := A) (U := U) H hQ R K cV ≤ replicaInteriorSharedWorkspaceConstant*Z^11 := by
  let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
  let C := replicaClassSharedWorkspaceConstant+1000
  have hs := List.sum_le_length_nsmul
    (keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV))
    (C*Z^11) (by
      intro x hx
      obtain ⟨L,hL,rfl⟩ := List.mem_map.mp hx
      exact replicaHaloKeySharedWorkspace_poly H hQ R K cV hE L hL hr hR hK hpush hclass hW (hC L hL))
  have hs' : (keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum ≤ 6*(C*Z^11) :=
    hs.trans (by simpa only [List.length_map,nsmul_eq_mul,Nat.cast_id] using
      Nat.mul_le_mul_right (C*Z^11) (haloLengthKeys_length_le s H.t H.band H.origin (H.origin+H.span)))
  have hsZ : s ≤ Z := by have := H.s_lt_t; omega
  have ha : H.origin ≤ Z := by have := H.span_fit; omega
  have hb := H.span_fit.trans hsZ
  have hm := placedHaloLengthKeysCost_poly hE.positive hsZ (by omega : H.t ≤ Z) hE.band ha hb hE.workspace
  have h3 : Z^3 ≤ Z^11 := Nat.pow_le_pow_right hE.positive (by decide)
  unfold replicaInteriorSharedWorkspace replicaInteriorSharedWorkspaceConstant
  change 3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
    (keys.map (fun L => replicaHaloKeySharedWorkspace (A := A) (U := U) H hQ R K L cV)).sum ≤ (6*C+1000000)*Z^11
  dsimp only [ReplicaHaloProblem.band]
  nlinarith only [hs',hm,h3]

end IntegerMultBounds.MathlibTM2.Cost
