module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! Selected dimensions discharge the initialized pass's metadata and local
padding hypotheses. No per-class workspace estimate is supplied by the caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

theorem selectedInitializedReplicaHaloWorkspace_le_local (hQ : SS.states ≤ Q)
    (R K ct ce : ℕ) {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (H : ReplicaHaloProblem (Sizes.s n i)) (hp : H.p = Sizes.p n) (ht : H.t = Sizes.t n i)
    (hl : H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (hu : H.u ≤ Sizes.p n) (htarget : H.target ≤ ct*Sizes.p n) (hrhs : H.rhsExp ≤ ce*Sizes.p n) :
    initializedReplicaHaloWorkspace (A := A) (U := U) H hQ R K ≤
      initializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K (2*(16*20+8*ct+8*ce+128)+426009) := by
  obtain ⟨_,_,_,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  apply initializedReplicaHaloWorkspace_le_local H hQ R K _
  · rw [ht]; exact selectedAxis_gap_le_source h i
  · rw [hl,ht]
  · simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,hl,ht] using hV

theorem selectedInitializedReplicaHaloLoop_within_local {T : ℕ} {P : Type}
    {body : P → Pr P T Q A U} (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (R K ct ce : ℕ)
    {n : ℕ} (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
    (H : ReplicaHaloProblem (Sizes.s n i)) (hp : H.p = Sizes.p n) (ht : H.t = Sizes.t n i)
    (hl : H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (hu : H.u ≤ Sizes.p n) (htarget : H.target ≤ ct*Sizes.p n) (hrhs : H.rhsExp ≤ ce*Sizes.p n)
    {depth steps : ℕ} {z z' : Store (HΓ (T := T) A) (HS T Q A U)}
    (he : ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      initializedReplicaHaloWorkspace (A := A) (U := U) H hQ R K) depth
      (initializedReplicaHaloLoop plan dst hR hQ) z steps z') :
    ExecWithin body (fun d state => mnSize state+d ≤ mnSize z+depth+
      initializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K (2*(16*20+8*ct+8*ce+128)+426009)) depth
      (initializedReplicaHaloLoop plan dst hR hQ) z steps z' := by
  have hc := selectedInitializedReplicaHaloWorkspace_le_local (A := A) (U := U) hQ R K ct ce h i H hp ht hl hu htarget hrhs
  apply he.mono
  intro d state hs
  exact hs.trans (Nat.add_le_add_left hc _)

end IntegerMultBounds.MathlibTM2.Cost
