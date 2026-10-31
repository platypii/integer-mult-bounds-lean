module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaPublicationRead
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellEncodedScatter
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedField

/-! Bounded integer-word encodings survive aligned scatter and replica
publication. The resulting local fields require no ambient-sized allocation. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
variable {A w q e span L : ℕ}

theorem EncodedRange.append {xs ys : List (Fin (A+4))}
    (hx : EncodedRange A w q e xs) (hy : EncodedRange A w q e ys) :
    EncodedRange A w q e (xs++ys) := by
  obtain ⟨zs,rfl,hzs⟩ := hx
  obtain ⟨ts,rfl,hts⟩ := hy
  refine ⟨zs++ts,(by rw [cstream_append]),?_⟩
  intro z hz
  exact (List.mem_append.mp hz).elim (hzs z) (hts z)

theorem EncodedRange.take_words {xs : List (Fin (A+4))}
    (h : EncodedRange A w q e xs) (n : ℕ) : EncodedRange A w q e (xs.take (n*w)) := by
  obtain ⟨zs,rfl,hzs⟩ := h
  rw [cstream_take]
  exact ⟨zs.take n,rfl,fun z hz => hzs z (List.mem_of_mem_take hz)⟩

theorem EncodedRange.drop_words {xs : List (Fin (A+4))}
    (h : EncodedRange A w q e xs) (n : ℕ) : EncodedRange A w q e (xs.drop (n*w)) := by
  obtain ⟨zs,rfl,hzs⟩ := h
  rw [cstream_drop]
  exact ⟨zs.drop n,rfl,fun z hz => hzs z (List.mem_of_mem_drop hz)⟩

theorem PublicationWindows.gaps_scale (windows : PublicationWindows span L) (w : ℕ) :
    windows.gaps w = (windows.gaps 1).map (fun d => d*w) := by
  simpa [PublicationWindows.gaps,PublicationWindows.symbolOrigins] using windowGaps_scale L 0 w windows.origins

theorem PublicationWindows.scatter_range (windows : PublicationWindows span L)
    (E X : List (Fin (A+4))) (hE : EncodedRange A w q e E) (hX : EncodedRange A w q e X) :
    EncodedRange A w q e (scatterRows (L*w) E X (windows.gaps w)) := by
  obtain ⟨es,rfl,hes⟩ := hE
  obtain ⟨xs,rfl,hxs⟩ := hX
  rw [windows.gaps_scale,scatterRows_cstream]
  refine ⟨_,rfl,?_⟩
  intro z hz
  exact (scatterRows_mem L es xs _ z hz).elim (hes z) (hxs z)

/-- The stream witness splits structurally at the actual replica boundaries. -/
theorem publicationReplicas_output_range (windows : PublicationWindows span L)
    (replicas : List (PublicationReplica A)) (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (hambient : ∀ r ∈ replicas, EncodedRange A w q e r.ambient)
    (hinput : EncodedRange A w q e (replicas.flatMap (PublicationReplica.input w))) :
    EncodedRange A w q e (replicas.flatMap (PublicationReplica.output windows w)) := by
  induction replicas with
  | nil => exact ⟨[],by simp [cstream],by simp⟩
  | cons r replicas ih =>
    have hr := hvalid r (by simp)
    have hlen : (r.input w).length = (windows.origins.length*L)*w := by
      rw [hr.input_eq_words,hr.words_length,Nat.mul_assoc]
    have hhead := hinput.take_words (windows.origins.length*L)
    have htail := hinput.drop_words (windows.origins.length*L)
    simp only [List.flatMap_cons,←hlen,List.take_left] at hhead
    simp only [List.flatMap_cons,←hlen,List.drop_left] at htail
    have hout : EncodedRange A w q e (r.output windows w) :=
      windows.scatter_range r.ambient (r.words w) (hambient r (by simp))
        (by rw [←hr.input_eq_words]; exact hhead)
    exact hout.append (ih (fun z hz => hvalid z (by simp [hz]))
      (fun z hz => hambient z (by simp [hz])) htail)

/-- Each published replica supplies the field format required by packed
coupling, with its original magnitude bound and no ambient stream. -/
theorem publicationReplicas_packedField {s origin : ℕ} [NeZero s]
    (windows : PublicationWindows span L) (hw : 0 < w) (hfit : origin+span ≤ s)
    (hbudget : q+e+2 ≤ w) (replicas : List (PublicationReplica A))
    (hvalid : ∀ r ∈ replicas, r.Valid windows w 0)
    (hrange : EncodedRange A w q e (replicas.flatMap (PublicationReplica.output windows w)))
    (r : Fin replicas.length) :
    ∃ D : ZMod s → GaussianInt,
      ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)).take (span*w) =
        cstream A w (packedInterval origin span D) ∧
      (∀ i, ‖value q (D i)‖ ≤ (2 : ℝ)^e) ∧ (∀ i, Fits w (D i)) := by
  have hslice := (hrange.drop_words (r.val*span)).take_words span
  have hh := flatMap_uniform_slice (PublicationReplica.output windows w) replicas (span*w) 0 (span*w)
    (fun z hz => (hvalid z hz).output_length) r (by omega) []
  simp only [List.append_nil,Nat.add_zero,List.drop_zero] at hh
  have htake : (((replicas[r.val]'r.isLt).output windows w).take (span*w)) =
      (replicas[r.val]'r.isLt).output windows w := List.take_of_length_le (by
        rw [(hvalid _ (List.getElem_mem r.isLt)).output_length])
  rw [htake] at hh
  have heq : ((replicas.flatMap (PublicationReplica.output windows w)).drop (r.val*span*w)).take (span*w) =
      (replicas[r.val]'r.isLt).output windows w := by simpa only [Nat.mul_assoc] using hh
  apply encodedRange_packedField hw hfit hbudget _ ?_ (by simpa only [Nat.mul_assoc] using hslice)
  rw [heq]
  exact (hvalid _ (List.getElem_mem r.isLt)).output_length

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
