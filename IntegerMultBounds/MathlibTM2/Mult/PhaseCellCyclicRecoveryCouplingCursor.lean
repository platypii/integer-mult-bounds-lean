module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingRow

/-! Chronological recovery language: remaining input queues, completed archives,
and a frame for the shared factor bank. The private loop clock is excluded. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "jointSource" => CyclicRecoveryPlacement.bank 132
local notation "clock" => CyclicRecoveryPlacement.bank 228
variable {s A : ℕ} [NeZero s]

abbrev CyclicRecoveryRow (s : ℕ) := (ZMod s → GaussianInt) × ((ZMod s → GaussianInt) × (ZMod s → GaussianInt))

def cyclicRecoveryField (H : ReplicaHaloProblem s) (C : ZMod s → GaussianInt) : List (Fin (A+4)) :=
  cstream A H.wordWidth (packedInterval H.origin H.span C)

def cyclicRecoveryOutputL (H : ReplicaHaloProblem s) (row : CyclicRecoveryRow s) : List (Fin (A+4)) :=
  cyclicRecoveryField H (guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
    H.origin (H.origin+H.span) true row.1 row.2.1)

def cyclicRecoveryOutputR (K : ReplicaHaloProblem s) (row : CyclicRecoveryRow s) : List (Fin (A+4)) :=
  cyclicRecoveryField K (guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band
    K.origin (K.origin+K.span) true row.1 row.2.2)

def cyclicRecoveryCouplingPorts : List (Fin 840) :=
  [jointSource,CyclicRecoveryPlacement.leftJob.coupling.bank 93,CyclicRecoveryPlacement.leftJob.coupling.bank 110,
    CyclicRecoveryPlacement.leftJob.plan.gather 125,CyclicRecoveryPlacement.rightJob.coupling.bank 93,
    CyclicRecoveryPlacement.rightJob.coupling.bank 110,CyclicRecoveryPlacement.rightJob.plan.gather 125,clock]

structure CyclicRecoveryCouplingCursor (H K : ReplicaHaloProblem s)
    (buffersL buffersR : ReplicaLoopBuffers A) (done todo : List (CyclicRecoveryRow s))
    (tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))) (S F : Stacks 840 A) : Prop where
  source : F.R jointSource = todo.flatMap (fun row => cyclicRecoveryField H row.1++cyclicRecoveryField K row.1)++tail
  rhsL : F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93) = todo.flatMap (fun row => cyclicRecoveryField H row.2.1)++rhsL
  rhsR : F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93) = todo.flatMap (fun row => cyclicRecoveryField K row.2.2)++rhsR
  outputL : F.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110) = done.reverse.flatMap (cyclicRecoveryOutputL H)++S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 110)
  outputR : F.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110) = done.reverse.flatMap (cyclicRecoveryOutputR K)++S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 110)
  archiveL : F.R (CyclicRecoveryPlacement.leftJob.plan.gather 125) = done.reverse.flatMap (fun row => cyclicRecoveryField H row.1)++S.R (CyclicRecoveryPlacement.leftJob.plan.gather 125)
  archiveR : F.R (CyclicRecoveryPlacement.rightJob.plan.gather 125) = done.reverse.flatMap (fun row => cyclicRecoveryField K row.1)++S.R (CyclicRecoveryPlacement.rightJob.plan.gather 125)
  headersL : ReplicaRecoveryRhsHeaders H CyclicRecoveryPlacement.leftJob.plan.gather buffersL F
  headersR : ReplicaRecoveryRhsHeaders K CyclicRecoveryPlacement.rightJob.plan.gather buffersR F
  cacheL : CachedRecoveryCouplingReady H (done.reverse.flatMap (cyclicRecoveryOutputL H)++rawL) pageL (embStk CyclicRecoveryPlacement.leftJob.coupling.bank F)
  cacheR : CachedRecoveryCouplingReady K (done.reverse.flatMap (cyclicRecoveryOutputR K)++rawR) pageR (embStk CyclicRecoveryPlacement.rightJob.coupling.bank F)
  input : F.inp = S.inp
  output : F.out = S.out
  left : F.L = S.L
  frame : ∀ k, k ∉ cyclicRecoveryCouplingPorts → F.R k = S.R k

theorem CyclicRecoveryCouplingCursor.update_clock {H K : ReplicaHaloProblem s}
    {buffersL buffersR : ReplicaLoopBuffers A} {done todo : List (CyclicRecoveryRow s)}
    {tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))} {S F : Stacks 840 A}
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F)
    (xs : List (Fin (A+4))) :
    CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S
      {F with R := Function.update F.R clock xs} := by
  have hL (i : Fin 840) (hi : CyclicRecoveryPlacement.leftJob.Owns i) : i ≠ clock :=
    CyclicRecoveryPlacement.native_left_disjoint 228 i hi
  have hR (i : Fin 840) (hi : CyclicRecoveryPlacement.rightJob.Owns i) : i ≠ clock :=
    CyclicRecoveryPlacement.native_right_disjoint 228 i hi
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_,h.input,h.output,h.left,?_⟩
  · simpa [CyclicRecoveryPlacement.bank_injective.ne (by decide : (132 : Fin 240) ≠ 228)] using h.source
  · simpa [hL _ (.bank 93)] using h.rhsL
  · simpa [hR _ (.bank 93)] using h.rhsR
  · simpa [hL _ (.bank 110)] using h.outputL
  · simpa [hR _ (.bank 110)] using h.outputR
  · simpa [hL _ (.gather 125)] using h.archiveL
  · simpa [hR _ (.gather 125)] using h.archiveR
  · apply h.headersL.of_frame H CyclicRecoveryPlacement.leftJob.plan.gather buffersL F
    intro i; exact Function.update_of_ne (hL _ (.gather i)) _ _
  · apply h.headersR.of_frame K CyclicRecoveryPlacement.rightJob.plan.gather buffersR F
    intro i; exact Function.update_of_ne (hR _ (.gather i)) _ _
  · rw [embStk_updateR_off _ _ _ (fun i => hL _ (.bank i))]
    exact h.cacheL
  · rw [embStk_updateR_off _ _ _ (fun i => hR _ (.bank i))]
    exact h.cacheR
  · intro k hk
    have hn : k ≠ clock := by intro he; apply hk; rw [he]; simp [cyclicRecoveryCouplingPorts]
    simpa [hn] using h.frame k hk

/-- Changing only the excluded private clock in the reference state does not
change the cursor's meaning. -/
theorem CyclicRecoveryCouplingCursor.base_clock {H K : ReplicaHaloProblem s}
    {buffersL buffersR : ReplicaLoopBuffers A} {done todo : List (CyclicRecoveryRow s)}
    {tail rhsL rhsR rawL rawR pageL pageR : List (Fin (A+4))} {S F : Stacks 840 A}
    (xs : List (Fin (A+4)))
    (h : CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR
      {S with R := Function.update S.R clock xs} F) :
    CyclicRecoveryCouplingCursor H K buffersL buffersR done todo tail rhsL rhsR rawL rawR pageL pageR S F := by
  have hL (i : Fin 840) (hi : CyclicRecoveryPlacement.leftJob.Owns i) : i ≠ clock :=
    CyclicRecoveryPlacement.native_left_disjoint 228 i hi
  have hR (i : Fin 840) (hi : CyclicRecoveryPlacement.rightJob.Owns i) : i ≠ clock :=
    CyclicRecoveryPlacement.native_right_disjoint 228 i hi
  refine ⟨h.source,h.rhsL,h.rhsR,?_,?_,?_,?_,h.headersL,h.headersR,h.cacheL,h.cacheR,
    h.input,h.output,h.left,?_⟩
  · simpa [hL _ (.bank 110)] using h.outputL
  · simpa [hR _ (.bank 110)] using h.outputR
  · simpa [hL _ (.gather 125)] using h.archiveL
  · simpa [hR _ (.gather 125)] using h.archiveR
  · intro k hk
    have hn : k ≠ clock := by intro he; apply hk; rw [he]; simp [cyclicRecoveryCouplingPorts]
    simpa [hn] using h.frame k hk

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
