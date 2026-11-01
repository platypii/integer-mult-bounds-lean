module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaHaloLoop
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedHaloReplicaResources

/-! Transport the actual all-key execution to the sum of linear class envelopes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} {U : Type}

noncomputable def replicaHaloKeyLinearWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K L cV : ℕ) :=
  2*replicaLengthKeyParserCost H.metadataWidth L+
    generatedHaloReplicaClassLinearWorkspace (A := A) (U := U) hQ R K H.p H.l H.Fs.length H.metadataWidth
      H.origin H.span L s H.t H.u H.target H.rhsExp cV

theorem replicaHaloKeyWorkspace_le_linear (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K L cV : ℕ) (hL : 0 < L) (hne : H.offsets L ≠ []) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    H.keyWorkspace (A := A) (U := U) hQ R K L ≤ replicaHaloKeyLinearWorkspace (A := A) (U := U) H hQ R K L cV := by
  have hB : 1 ≤ (haloLengthGroup s H.t H.band H.origin (H.origin+H.span) L).length := by
    have hpos := List.length_pos_iff_ne_nil.mpr hne
    have hh : 1 ≤ (H.offsets L).length := by omega
    simpa only [ReplicaHaloProblem.offsets,haloPackedOffsets_length] using hh
  have hc := generatedHaloReplicaClassWorkspace_le_linear (A := A) (U := U) hQ
    R K H.p H.l H.Fs.length H.metadataWidth H.origin H.span L s H.t H.u H.target H.rhsExp cV hB (by omega) hV
  exact Nat.add_le_add_left hc _

theorem replicaHaloLoopWorkspace_le_linear (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K cV : ℕ) (keys : List ℕ)
    (hbounds : ∀ L ∈ keys, 0 < L ∧ H.offsets L ≠ []) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum ≤
      (keys.map (fun L => replicaHaloKeyLinearWorkspace (A := A) (U := U) H hQ R K L cV)).sum := by
  induction keys with
  | nil => simp
  | cons L keys ih =>
    have hL := hbounds L (by simp)
    have hh := replicaHaloKeyWorkspace_le_linear (A := A) (U := U) H hQ R K L cV hL.1 hL.2 hV
    have ht := ih (fun J hJ => hbounds J (by simp [hJ]))
    simpa only [List.map_cons,List.sum_cons] using Nat.add_le_add hh ht

theorem runReplicaHaloLoop_within_linear {T : ℕ} {P : Type} {body : P → Pr P T Q A U}
    (H : ReplicaHaloProblem s) (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) {R K cV depth steps : ℕ} (keys : List ℕ)
    {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      (keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum) depth
      (runReplicaHaloLoop plan dst hR hQ) z steps z')
    (hbounds : ∀ L ∈ keys, 0 < L ∧ H.offsets L ≠ []) (hV : H.metadataWidth ≤ cV*H.wordWidth) :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      (keys.map (fun L => replicaHaloKeyLinearWorkspace (A := A) (U := U) H hQ R K L cV)).sum) depth
      (runReplicaHaloLoop plan dst hR hQ) z steps z' := by
  apply he.mono
  intro d state hs
  have hb := replicaHaloLoopWorkspace_le_linear (A := A) (U := U) H hQ R K cV keys hbounds hV
  omega

end IntegerMultBounds.MathlibTM2.Cost
