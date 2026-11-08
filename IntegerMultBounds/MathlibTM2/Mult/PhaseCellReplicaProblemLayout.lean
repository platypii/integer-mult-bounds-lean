module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem

/-! Interior passes reuse physical headers when geometry, format and replica
count agree. Their RHS, reference solutions and accuracy targets may differ. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

structure ReplicaHaloProblem.SameLayout {s : ℕ} (H J : ReplicaHaloProblem s) : Prop where
  p : J.p = H.p
  l : J.l = H.l
  t : J.t = H.t
  u : J.u = H.u
  origin : J.origin = H.origin
  span : J.span = H.span
  precision : J.precision = H.precision
  stage : J.stage = H.stage
  wordWidth : J.wordWidth = H.wordWidth
  count : J.Fs.length = H.Fs.length

theorem ReplicaHaloProblem.SameLayout.band {s : ℕ} {H J : ReplicaHaloProblem s}
    (h : H.SameLayout J) : J.band = H.band := by
  simp only [ReplicaHaloProblem.band,h.p,h.u]

theorem ReplicaHaloProblem.SameLayout.metadataWidth {s : ℕ} {H J : ReplicaHaloProblem s}
    (h : H.SameLayout J) : J.metadataWidth = H.metadataWidth := by
  simp only [ReplicaHaloProblem.metadataWidth,h.p,h.precision,h.wordWidth,h.t,h.u]

theorem ReplicaLoopHeaders.replace_source {s T A : ℕ} {H J : ReplicaHaloProblem s}
    (layout : H.SameLayout J) (gather : Fin 126 → Fin T)
    (buffers nextBuffers : ReplicaLoopBuffers A) (S F : Stacks T A)
    (h : ReplicaLoopHeaders H gather buffers S)
    (hframe : ∀ k : Fin 126, k ≠ 124 → F.R (gather k) = S.R (gather k))
    (hsource : F.R (gather 124) = J.Fs.flatMap
      (fun R => cstream A J.wordWidth (packedInterval J.origin J.span R))++nextBuffers.packedRhsTail) :
    ReplicaLoopHeaders J gather nextBuffers F := by
  constructor
  · intro r hr h102 h116
    have hall : replicaFactoryHeaderCopies.all (fun r => decide (r.1 ≠ 124)) = true := by decide +kernel
    have h124 : r.1 ≠ 124 := of_decide_eq_true (List.all_eq_true.mp hall r hr)
    rw [hframe r.1 h124,layout.p,layout.stage,layout.precision,layout.l,layout.t,layout.u,
      layout.band,layout.count,layout.wordWidth]
    exact h.masters r hr h102 h116
  · rw [hframe 111 (by decide),layout.origin]; exact h.origin
  · rw [hframe 113 (by decide),layout.origin,layout.span]; exact h.endpoint
  · rw [hframe 115 (by decide),layout.metadataWidth]; exact h.width
  · rw [hframe 123 (by decide),layout.span,layout.wordWidth]; exact h.volume
  · exact hsource
  · intro k hk
    rw [hframe k (by intro he; subst k; norm_num at hk)]
    exact h.blank k hk
  · intro k hk
    rw [hframe k (by intro he; subst k; norm_num at hk)]
    exact h.fresh k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
