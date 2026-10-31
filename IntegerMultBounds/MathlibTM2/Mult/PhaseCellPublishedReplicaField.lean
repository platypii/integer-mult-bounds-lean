module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRange

/-! Supply packed recovery with a fitting Gaussian-integer field extracted from
the actual published replica, and transfer its existing read error unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A w q e span L s origin : ℕ} [NeZero s]

theorem publicationReplicas_field_read (windows : PublicationWindows span L)
    (hA : 4 ≤ A) (hw : 0 < w) (hfit : origin+span ≤ s) (hbudget : q+e+2 ≤ w)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (hrange : EncodedRange A w q e (replicas.flatMap (PublicationReplica.output windows w)))
    (r : Fin replicas.length) :
    ∃ D : ZMod s → GaussianInt,
      ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)).take (span*w) =
        cstream A w (packedInterval origin span D) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (D i)) ∧
      ∀ k : ZMod s, origin ≤ k.val → k.val < origin+span →
        packedIntervalRead q w origin
          ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)) k = value q (D k) := by
  obtain ⟨D,hD,hbound,hfits⟩ := publicationReplicas_packedField windows hw hfit hbudget replicas hvalid hrange r
  let raw := (replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)
  have hsplit : raw = cstream A w (packedInterval origin span D)++raw.drop (span*w) := by
    rw [←hD]
    exact (List.take_append_drop (span*w) raw).symm
  refine ⟨D,hD,hbound,hfits,?_⟩
  intro k hklo hkhi
  change packedIntervalRead q w origin raw k = _
  rw [hsplit,packedIntervalRead_eq q w origin span D (raw.drop (span*w)) [] hfit k hklo hkhi,
    pairedCellRead_encodedField hA hw D [] k (hfits k)]

/-- Recovery consumes the same field and accuracy already proved for physical
packed reads; extracting the field introduces no extra error. -/
theorem publicationReplicas_field_errorOn (windows : PublicationWindows span L)
    (hA : 4 ≤ A) (hw : 0 < w) (hfit : origin+span ≤ s) (hbudget : q+e+2 ≤ w)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (hrange : EncodedRange A w q e (replicas.flatMap (PublicationReplica.output windows w)))
    (r : Fin replicas.length) (core : Finset (ZMod s)) (x : ZMod s → ℝ) (error : ℝ)
    (hcore : ∀ k ∈ core, origin ≤ k.val ∧ k.val < origin+span)
    (herror : PhaseCellInterface.ErrorOn core
      (fun k => (packedIntervalRead q w origin
        ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)) k).re) x error) :
    ∃ D : ZMod s → GaussianInt,
      ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)).take (span*w) =
        cstream A w (packedInterval origin span D) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (D i)) ∧
      PhaseCellInterface.ErrorOn core (fun k => (value q (D k)).re) x error := by
  obtain ⟨D,hD,hbound,hfits,hread⟩ := publicationReplicas_field_read windows hA hw hfit hbudget replicas hvalid hrange r
  refine ⟨D,hD,hbound,hfits,?_⟩
  intro k hk
  have hh := herror k hk
  dsimp only at hh
  rw [hread k (hcore k hk).1 (hcore k hk).2] at hh
  exact hh

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
