module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaCouplingRows

/-! Finish an actual initialized interior trace with real row projection,
matching RHS construction, shared setup and all-replica residual coupling. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def initializedReplicaInteriorCoupling {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (initializedReplicaCouplingRows plan output rhs hR hQ) (releasedReplicaCoupling placement output rhs hQ)

theorem initializedReplicaInteriorCoupling_finish (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T)
    (houtput : ∀ k, plan.gather k ≠ output) (hrhs : ∀ k, plan.gather k ≠ rhs)
    (hbankOutput : ∀ k, placement.bank k ≠ output) (hbankRhs : ∀ k, placement.bank k ≠ rhs)
    (hsep : output ≠ rhs) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (buffers : ReplicaLoopBuffers A) (v v₀ : HS T Q A U) (S F : Stacks T A) (n depth W : ℕ)
    (hu₀ : v₀.user = v.user)
    (he₀ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth
      (initializedReplicaHaloLoop plan output hR hQ) (mk v S) n (mk v₀ F))
    (h : ReplicaHaloLoopState H plan output buffers (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]), F.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], F.R (placement.bank k) = []) :
    ∃ v' G m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧ m ≤ n+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+releasedReplicaCouplingCost H ∧
      Exec body (initializedReplicaInteriorCoupling placement output rhs hR hQ) (mk v S) m (mk v' G) ∧
      G.R (plan.gather 122) = [] ∧ G.R output = buffers.accumulatorTail ∧ G.R rhs = (F.R rhs) ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) buffers.rhsTail
        (embStk weightCacheCoreReg (embStk plan.solver G)) ∧
      CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank G) ∧
      G.L = F.L ∧ G.inp = F.inp ∧ G.out = F.out ∧
      (∀ k, (∀ i, placement.bank i ≠ k) → k ∉ [output,rhs,plan.gather 125] → G.R k = F.R k) ∧
      Ds.length = H.Fs.length ∧
      G.R (plan.gather 125) = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) ∧
      G.R (placement.bank 138) = cstream A H.wordWidth
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++F.R (placement.bank 138) ∧
      (G.R (placement.bank 139)).length =
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length ∧
      (G.R (placement.bank 140)).length = 2*H.band+1 ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], G.R (placement.bank k) = []) ∧
      (∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧ (∀ i, Fits H.wordWidth (D i))) := by
  have hdom := H.dominates hp hwidth
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hcursor,hgather,hL₁,hi₁,ho₁,hframe₁⟩ :=
    initializedReplicaCouplingRows_finish (body := body) H plan output rhs houtput hrhs hsep hR hQ (by omega : 4 ≤ A)
      buffers v v₀ S F n depth W hu₀ he₀ h hdom
  have hbankFrame : embStk placement.bank J = embStk placement.bank F := by
    refine Stacks.ext hi₁ ho₁ (congrArg (fun L => L ∘ placement.bank) hL₁) ?_
    funext k
    exact hframe₁ _ (hbankOutput k) (hbankRhs k)
  have hbankR (k : Fin 168) : J.R (placement.bank k) = F.R (placement.bank k) := congrFun (congrArg Stacks.R hbankFrame) k
  have hnative : embStk weightCacheCoreReg (embStk plan.solver J) = embStk weightCacheCoreReg (embStk plan.solver F) := by
    rw [← placement.native_view J,← placement.native_view F,hbankFrame]
  have hreleased : embStk weightCacheCoreReg (embStk plan.solver J) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail J.inp J.out := by
    rw [hnative,h.bank,hi₁,ho₁]
  have hheadersJ : ReplicaLoopHeaders H plan.gather buffers J := by
    apply h.headers.of_frame
    intro k _ _
    exact congrFun (congrArg Stacks.R hgather) k
  obtain ⟨v₂,G,n₂,Ds,hu₂,hn₂,he₂,hcount,hout,hrhsF,hready,hmeta,hL₂,hi₂,ho₂,hframe₂,hlen,harchive,hgood,hpage,hpageCount,hrows,hfreshF,hDsBounds⟩ :=
    releasedReplicaCoupling_exec (body := body) H placement output rhs houtput hrhs hbankOutput hbankRhs hsep hQ hA
      hspan horigin buffers.accumulatorTail (F.R rhs) buffers.rhsTail buffers.solverOutputTail
      buffers v₁ J hcursor hheadersJ hreleased
      (by intro k hk; rw [hbankR k]; exact hblank k hk)
      (by intro k hk; rw [hbankR k]; exact hfresh k hk)
  refine ⟨v₂,G,n₁+n₂,Ds,hu₂.trans hu₁,by omega,.seq he₁.toExec he₂,hcount,hout,hrhsF,hready,hmeta,
    hL₂.trans hL₁,hi₂.trans hi₁,ho₂.trans ho₁,?_,hlen,harchive,hgood,?_,hpageCount,hrows,hfreshF,hDsBounds⟩
  · intro k hk hp
    apply (hframe₂ k hk hp).trans
    have hn : k ≠ output ∧ k ≠ rhs := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hp
      exact ⟨hp.1,hp.2.1⟩
    exact hframe₁ k hn.1 hn.2
  · rw [hbankR 138] at hpage
    exact hpage

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
