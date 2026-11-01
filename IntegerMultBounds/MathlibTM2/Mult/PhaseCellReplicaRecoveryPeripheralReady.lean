module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaHaloProblem
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryInteriorPlacement

/-! The second pass's gather, cache and output premises are spectators during
preparation. Numerical-core readiness is derived separately from its exit bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s A : ℕ} [NeZero s]

structure ReplicaRecoveryPeripheralReady (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    (S : Stacks 392 A) : Prop where
  headers : ReplicaLoopHeaders H replicaRecoveryBatchInterior.gather buffers S
  cache : S.R (replicaRecoveryBatchInterior.solver 117) = buffers.cacheTail
  solverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (replicaRecoveryBatchInterior.solver k) = []
  input : S.inp = buffers.input
  output : S.out = buffers.output
  keys : S.R (replicaRecoveryBatchInterior.gather 87) = buffers.keyTail
  accumulator : S.R 247 = buffers.accumulatorTail
  packets : S.R (replicaRecoveryBatchInterior.gather 86) = []
  count : S.R (replicaRecoveryBatchInterior.gather 119) = []

theorem ReplicaRecoveryPeripheralReady.of_preparation_frame (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    {S F : Stacks 392 A} (h : ReplicaRecoveryPeripheralReady H buffers S)
    (hgather : embStk (Fin.castLE (by decide : 126 ≤ 392)) F = embStk (Fin.castLE (by decide : 126 ≤ 392)) S)
    (hoff : ∀ k : Fin 392, (∀ i, replicaRecoveryPreparationCallerReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) :
    ReplicaRecoveryPeripheralReady H buffers F := by
  have hg (i : Fin 126) : F.R (replicaRecoveryBatchInterior.gather i) = S.R (replicaRecoveryBatchInterior.gather i) :=
    congrFun (congrArg Stacks.R hgather) i
  have hi : F.inp = S.inp := congrArg (fun G : Stacks 126 A => G.inp) hgather
  have ho : F.out = S.out := congrArg (fun G : Stacks 126 A => G.out) hgather
  have hdst : F.R 247 = S.R 247 := (hoff 247 (by
    intro i he
    have hv := congrArg (fun k : Fin 392 => k.val) he
    have hh := replicaRecoveryPreparationCallerReg_gap i
    change (replicaRecoveryPreparationCallerReg i).val = 247 at hv
    omega)).2
  constructor
  · exact h.headers.of_frame (fun k _ _ => hg k)
  · exact (hoff _ (fun i => replicaRecoveryPreparationCallerReg_reserved i 117 (by decide))).2.trans h.cache
  · intro k hk
    have hreserved : 117 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
    exact (hoff _ (fun i => replicaRecoveryPreparationCallerReg_reserved i k hreserved)).2.trans (h.solverFresh k hk)
  · exact hi.trans h.input
  · exact ho.trans h.output
  · exact (hg 87).trans h.keys
  · exact hdst.trans h.accumulator
  · exact (hg 86).trans h.packets
  · exact (hg 119).trans h.count

theorem ReplicaRecoveryPeripheralReady.small_headers (H : ReplicaHaloProblem s) (buffers : ReplicaLoopBuffers A)
    (S : Stacks 392 A) (h : ReplicaRecoveryPeripheralReady H buffers S) :
    ReplicaLoopHeaders H replicaRecoverySmallInterior.gather buffers (embStk replicaRecoveryInteriorCallerReg S) := by
  have hg (i : Fin 126) : (embStk replicaRecoveryInteriorCallerReg S).R (replicaRecoverySmallInterior.gather i) =
      S.R (replicaRecoveryBatchInterior.gather i) := congrArg S.R (replicaRecoveryInteriorCallerReg_gather i)
  constructor
  · intro r hr h102 h116
    rw [hg]
    exact h.headers.masters r hr h102 h116
  · exact (congrArg List.length (hg 111)).trans h.headers.origin
  · exact (congrArg List.length (hg 113)).trans h.headers.endpoint
  · exact (congrArg List.length (hg 115)).trans h.headers.width
  · exact (congrArg List.length (hg 123)).trans h.headers.volume
  · exact (hg 124).trans h.headers.source
  · intro k hk
    exact (hg k).trans (h.headers.blank k hk)
  · intro k hk
    exact (hg k).trans (h.headers.fresh k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
