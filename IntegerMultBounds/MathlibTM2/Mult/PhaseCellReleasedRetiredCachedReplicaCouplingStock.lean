module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedCachedReplicaCouplingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedRetiredCachedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.StackExecutionUnique

/-! Mask retirement adds no workspace to the released cached traversal.
Execution uniqueness retains its established exact recovery-ready endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

theorem releasedRetiredCachedReplicaCoupling_exec_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T)
    (houtput : ∀ k, plan.gather k ≠ output) (hrhs : ∀ k, plan.gather k ≠ rhs)
    (hbankOutput : ∀ k, placement.bank k ≠ output) (hbankRhs : ∀ k, placement.bank k ≠ rhs)
    (hsep : output ≠ rhs) (hQ : SS.states ≤ Q) (K : ℕ)
    (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ K) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (outputTail rhsTail raw resultTail : List (Fin (A+4))) (buffers : ReplicaLoopBuffers A)
    (v : HS T Q A U) (S : Stacks T A)
    (h : ReplicaCouplingCursor H output rhs outputTail rhsTail 0 S)
    (hheaders : ReplicaLoopHeaders H plan.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) = releasedCellBank [] raw resultTail S.inp S.out)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (placement.bank k) = [])
    (h136 : S.R (placement.bank 136) = []) (h159 : S.R (placement.bank 159) = [])
    (h161 : S.R (placement.bank 161) = []) :
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧ m ≤ releasedRetiredCachedReplicaCouplingCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K)
        depth (releasedRetiredCachedReplicaCoupling placement output rhs hQ) (mk v S) m (mk v' F)) ∧
      F.R (plan.gather 122) = [] ∧ F.R output = outputTail ∧ F.R rhs = rhsTail ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw
        (embStk weightCacheCoreReg (embStk plan.solver F)) ∧
      CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank F) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, placement.bank i ≠ k) → k ∉ [output,rhs,plan.gather 125] → F.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      F.R (plan.gather 125) = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) ∧
      F.R (placement.bank 138) = cstream A H.wordWidth
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++S.R (placement.bank 138) ∧
      (F.R (placement.bank 139)).length =
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length ∧
      (F.R (placement.bank 140)).length = 2*H.band+1 ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], F.R (placement.bank k) = []) ∧
      (∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧ (∀ i, Fits H.wordWidth (D i))) ∧
      (embStk weightCacheCoreReg (embStk plan.solver F)).R =
      counterR H.precision H.wordWidth
        (replicaCouplingUnaryBank A (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
          H.origin (H.origin+H.span) raw resultTail S.inp S.out).R ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → F.R (placement.bank k) = S.R (placement.bank k)) := by
  obtain ⟨vf,G,m,Ds,hu,hm,hex,hrest⟩ := releasedRetiredCachedReplicaCoupling_exec (body := body)
    H placement output rhs houtput hrhs hbankOutput hbankRhs hsep hQ hA hspan horigin
    outputTail rhsTail raw resultTail buffers v S h hheaders hbank hblank hfresh h136 h159 h161
  obtain ⟨v₁,J,n,_,_,_,htrace,_⟩ := releasedCachedReplicaCoupling_exec_within (body := body)
    H placement output rhs houtput hrhs hbankOutput hbankRhs hsep hQ K hpush hA hspan horigin
    outputTail rhsTail raw resultTail buffers v S h hheaders hbank hblank hfresh h136 h159 h161
  obtain ⟨v₂,_,hretire⟩ := retireCouplingMasks_exec_within (body := body) placement.bank placement.bank_injective v₁ J
  have hsize := (htrace 0).final
  have ht : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K)
      0 (releasedRetiredCachedReplicaCoupling placement output rhs hQ) (mk v S)
      (n+((2*(J.R (placement.bank 159)).length+2)+(2*(J.R (placement.bank 161)).length+2)))
      (mk v₂ (retiredCouplingMasksState placement.bank J)) := by
    refine .seq ((htrace 0).mono ?_) ((hretire 0).mono ?_)
    all_goals intro d z hz; omega
  obtain ⟨htime,hfinal⟩ := ht.toExec.unique hex
  refine ⟨vf,G,m,Ds,hu,hm,?_,hrest⟩
  intro depth
  have hshift := mn_exec_within_shift ht depth
  simpa only [Nat.zero_add,Nat.add_right_comm] using hshift.cast htime hfinal

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
