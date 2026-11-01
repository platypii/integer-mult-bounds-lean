module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRange

/-! Recover each bounded output row from the bounded flattened accumulator. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A w q e span L : ℕ}

theorem EncodedRange.of_flatten_uniform (rows : List (List (Fin (A+4))))
    (hlen : ∀ row ∈ rows, row.length = span*w) (h : EncodedRange A w q e rows.flatten) :
    ∀ row ∈ rows, EncodedRange A w q e row := by
  induction rows with
  | nil => simp
  | cons row rows ih =>
    have hrow := hlen row (by simp)
    have hh := h.take_words span
    have ht := h.drop_words span
    simp only [List.flatten_cons,←hrow,List.take_left] at hh
    simp only [List.flatten_cons,←hrow,List.drop_left] at ht
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hh
    · exact ih (fun x hx => hlen x (by simp [hx])) ht x hx

theorem publicationReplicas_output_rows (windows : PublicationWindows span L) (w : ℕ)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (hrange : EncodedRange A w q e (replicas.flatMap (PublicationReplica.output windows w))) :
    let rows := replicas.map (PublicationReplica.output windows w)
    rows.length = replicas.length ∧ (∀ row ∈ rows, row.length = span*w) ∧
      (∀ row ∈ rows, EncodedRange A w q e row) ∧
      rows.flatten = replicas.flatMap (PublicationReplica.output windows w) := by
  dsimp only
  have hlen : ∀ row ∈ replicas.map (PublicationReplica.output windows w), row.length = span*w := by
    intro row hr
    obtain ⟨r,hrMem,rfl⟩ := List.mem_map.mp hr
    exact (hvalid r hrMem).output_length
  refine ⟨by simp,hlen,?_,?_⟩
  · apply EncodedRange.of_flatten_uniform _ hlen
    simpa only [List.flatMap_def] using hrange
  · rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
