module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryInterior
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryAssembly

/-! Append actual final assembly to an executed shared interior pass. Its
readiness is derived from the pass's gather and spectator frames. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

noncomputable def placedReplicaRecoveryFinish (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  .seq (placedReplicaRecoveryInterior hR hQ) placedReplicaRecoveryAssembly

theorem placedReplicaRecoveryFinish_exec (H : ReplicaHaloProblem s) (target : ℕ) (X : ℕ → ZMod s → ℝ)
    (B : ReplicaRecoveryBatch H target X) (htarget) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 4 ≤ A)
    (buffers : ReplicaLoopBuffers A) (tailY : List (Fin (A+4)))
    (v vi : HS 392 Q A U) (S F : Stacks 392 A) (n depth W : ℕ)
    (hready : ReplicaRecoveryPeripheralReady H buffers S)
    (hboundary : S.R 257 = (List.ofFn B.boundary).flatMap
      (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++tailY)
    (hmask : S.R 386 = couplingSourceIntervalMaskSymbols true A s H.t H.band H.origin
      (H.origin+H.span) H.origin H.span)
    (hfresh : ∀ k ∈ ([390,299,248] : List (Fin 392)), S.R k = [])
    (hu : vi.user = v.user)
    (he : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth
      (placedReplicaRecoveryInterior hR hQ) (mk v S) n (mk vi F))
    (hfields : RealReplicaHaloOutput (B.problem htarget) 247 buffers.accumulatorTail F)
    (hgather : ∀ k : Fin 126, k ≠ 87 → k ≠ 119 → k ≠ 124 →
      F.R (replicaRecoveryBatchInterior.gather k) = S.R (replicaRecoveryBatchInterior.gather k))
    (hspectator : ∀ k : Fin 392, 248 ≤ k.val → k ≠ 389 → F.L k = S.L k ∧ F.R k = S.R k) :
    ∃ Ds : List (ZMod s → GaussianInt), ∃ v' G m outputs,
      Ds.length = H.Fs.length ∧ v'.user = v.user ∧
      m ≤ n+(H.Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4) ∧
      List.Forall₂ (ReplicaRecoveryAssemblyOutput B Ds) (List.finRange H.Fs.length) outputs ∧
      G.R 257 = tailY ∧ G.R 247 = buffers.accumulatorTail ∧ G.R 391 = outputs.reverse.flatten++S.R 391 ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (W+2*retainedPackedPublicationMergeCost H.span H.wordWidth)) depth
        (placedReplicaRecoveryFinish hR hQ) (mk v S) m (mk v' G) := by
  have hwidth : (S.R 94).length = H.wordWidth := by
    simpa [replicaFactoryHeaderValue] using hready.headers.masters (94,94)
      (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  have hcount : (S.R 121).length = H.Fs.length := by
    simpa [replicaFactoryHeaderValue] using hready.headers.masters (121,113)
      (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  obtain ⟨Ds,v',m,outputs,hlen,hu',hm,hcert,he'⟩ := placedReplicaRecoveryAssembly_exec (body := body)
    H target X B htarget hA buffers.accumulatorTail tailY vi F hfields
    ((hspectator 257 (by decide) (by decide)).2.trans hboundary)
    ((hspectator 386 (by decide) (by decide)).2.trans hmask)
    ((congrArg List.length (show F.R 94 = S.R 94 from hgather 94 (by decide) (by decide) (by decide))).trans hwidth)
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl
      · exact (hspectator 390 (by decide) (by decide)).2.trans (hfresh 390 (by decide))
      · exact (hspectator 299 (by decide) (by decide)).2.trans (hfresh 299 (by decide))
      · exact (hspectator 248 (by decide) (by decide)).2.trans (hfresh 248 (by decide))
      · exact (hgather 104 (by decide) (by decide) (by decide)).trans (hready.headers.fresh 104 (by simp))
      · exact (hgather 105 (by decide) (by decide) (by decide)).trans (hready.headers.fresh 105 (by simp))
      · exact (hgather 89 (by decide) (by decide) (by decide)).trans (hready.headers.fresh 89 (by simp)))
    ((congrArg List.length (show F.R 121 = S.R 121 from hgather 121 (by decide) (by decide) (by decide))).trans hcount) depth
  let G := {F with R := (Function.update (Function.update (Function.update F.R 257 tailY)
    247 buffers.accumulatorTail) 391 (outputs.reverse.flatten++F.R 391))}
  refine ⟨Ds,v',G,n+m,outputs,hlen,hu'.trans hu,by omega,hcert,?_,?_,?_,?_⟩
  · simp [G]
  · simp [G]
  · simp [G,(hspectator 391 (by decide) (by decide)).2]
  · have hsize := he.final
    exact .seq (he.mono (by intro d z hz; omega)) (he'.mono (by intro d z hz; omega))

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
