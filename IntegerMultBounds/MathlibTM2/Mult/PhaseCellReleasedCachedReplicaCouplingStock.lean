module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCachedReplicaCouplingStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedCachedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReleasedReplicaCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaCouplingResidualBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReloadReplicaCouplingHeaders

/-! Reuse released numerical storage and retained gather controls. Gather 125
holds the residual archive; shared headers are copied from actual masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def releasedCachedReplicaCouplingWorkspace (H : ReplicaHaloProblem s) (K : ℕ) : ℕ :=
  2*replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+
    preparedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K H.metadataWidth

theorem releasedCachedReplicaCoupling_exec_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
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
    ∃ v' F m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧ m ≤ releasedCachedReplicaCouplingCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K)
        depth (releasedCachedReplicaCoupling placement output rhs hQ) (mk v S) m (mk v' F)) ∧
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
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → k ≠ 159 → k ≠ 161 →
        F.R (placement.bank k) = S.R (placement.bank k)) ∧
      F.R (placement.bank 159) = (couplingRibbonFlags (s := s) false H.t H.band H.origin
        (H.origin+H.span) H.origin H.span).map (fun flag => pairSym A flag flag) ∧
      F.R (placement.bank 161) = recoveryGuardIntervalSymbols true A s H.t (2*H.band)
        H.origin (H.origin+H.span) H.origin H.span := by
  obtain ⟨v₁,hu₁,he₁,hready,hgather,hL₁,hframe₁,hnativeJ⟩ := reloadReplicaCouplingHeaders_exec_within (body := body)
    plan (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) raw resultTail v S hbank
    (hheaders.coupling_masters H plan buffers S) (hheaders.blank 7 (by decide)) 0
  let J : Stacks T A := {S with R := unaryCopiesR (fun k => (S.R k).length) S.R (placedReplicaHeaderCopies plan replicaCouplingHeaderCopies)}
  have hforeign (k : Fin T) (hk : ∀ i, placement.bank i ≠ k) : J.R k = S.R k :=
    hframe₁ k (fun r _ hh => hk _ ((placement.bank_native r.2).trans hh))
  have hhigh (k : Fin 168) (hk : 117 ≤ k.val) : J.R (placement.bank k) = S.R (placement.bank k) := by
    apply hframe₁
    intro r _ hh
    have hv : r.2.val = k.val := congrArg Fin.val (placement.bank_injective ((placement.bank_native r.2).trans hh))
    have hr := r.2.isLt
    omega
  have hheadersJ : ReplicaLoopHeaders H plan.gather buffers J := by
    apply hheaders.of_frame
    intro k _ _
    exact congrFun (congrArg Stacks.R hgather) k
  have h107J : J.R (placement.bank 107) = [] := by
    have h107 : placement.bank 107 = plan.solver (weightCacheCoreReg (107 : Fin 117)) := placement.bank_native 107
    rw [hframe₁ _ (by
      intro r hr
      rw [h107]
      apply (plan.solver_injective.comp weightCacheCoreReg_injective).ne
      simp only [replicaCouplingHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
      rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide)]
    have hh := congrArg (fun B : Stacks 117 A => B.R 107) hbank
    simpa [embStk,releasedCellBank,ReplicaCouplingPlacement.bank,weightCacheCoreReg] using hh
  have hblankJ (k : Fin 168) (hk : k ∈ [(0 : Fin 168),1,2,3,145,146,147,148,149,151,154,155,156,157,163,164,165]) : J.R (placement.bank k) = [] := by
    by_cases hlt : k.val < 117
    · let i : Fin 117 := ⟨k.val,hlt⟩
      have hsmall : i.val < 63 := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
        rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [i] at * <;> omega
      have hh := hready.low i hsmall
      simpa [embStk,ReplicaCouplingPlacement.bank,hlt,i,weightCacheCoreReg] using hh
    · rw [hhigh k (by omega)]
      apply hblank
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
      all_goals first | omega | simp
  have hw5 : 5 ≤ H.wordWidth := by unfold ReplicaHaloProblem.wordWidth executionWidth; omega
  have hqw : H.precision+4 ≤ H.wordWidth := by unfold ReplicaHaloProblem.precision ReplicaHaloProblem.wordWidth executionWidth executionPrecision; omega
  obtain ⟨v₂,F,n₂,Ds,hu₂,hn₂,he₂,hcountF,hout,hrhsF,hreadyF,hmeta,hL₂,hi₂,ho₂,hframe₂,hlen,harchive,hgood,hpage,hcount,hrows,hfreshF,hnativeF,hsharedF,hmask159,hmask161⟩ :=
    preparedCachedReplicaCoupling_exec_within (body := body) H placement (plan.gather 123) output rhs (plan.gather 125)
      (plan.gather 104) (plan.gather 105) (plan.gather 122)
      (replicaCouplingControls_nodup placement output rhs houtput hrhs hbankOutput hbankRhs hsep)
      (by intro i k hk
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
          rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl
          all_goals first | exact placement.bank_gather_disjoint _ _ | exact hbankOutput _ | exact hbankRhs _)
      hQ K hpush hA hw5 hqw hspan horigin H.metadataWidth H.coupling_geometry.2 H.coupling_geometry.1
      (fun j _ => H.coupling_coefficients (H.origin+j)) outputTail rhsTail raw v₁ J
      (ReplicaCouplingCursor.of_frame H output rhs outputTail rhsTail 0 S J h (hforeign output hbankOutput) (hforeign rhs hbankRhs))
      (hheadersJ.fresh 122 (by simp))
      (by simpa [replicaFactoryHeaderValue] using hheadersJ.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide))
      hready hheadersJ.volume (hheadersJ.fresh 104 (by simp)) (hheadersJ.fresh 105 (by simp))
      hheadersJ.width (hheadersJ.blank 7 (by decide)) h107J hblankJ
      (by intro k hk
          have hh : 117 ≤ k.val := by
            simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
            rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
          rw [hhigh k hh]
          exact hfresh k hk)
      (by rw [hhigh 136 (by decide)]; exact h136)
      (by rw [hhigh 159 (by decide)]; exact h159)
      (by rw [hhigh 161 (by decide)]; exact h161)
  refine ⟨v₂,F,replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+n₂,
    Ds,hu₂.trans hu₁,by unfold releasedCachedReplicaCouplingCost; omega,?_,hcountF,hout,hrhsF,
    hreadyF,hmeta,hL₂.trans hL₁,hi₂,ho₂,?_,hlen,?_,hgood,?_,hcount,hrows,hfreshF,replicaCouplingResiduals_bounds H Ds hlen hgood,?_,?_,hmask159,hmask161⟩
  · have hsize := he₁.final
    change mnSize (mk v₁ J)+0 ≤ _ at hsize
    have hex : ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+releasedCachedReplicaCouplingWorkspace (Q := Q) (A := A) (U := U) H K)
        0 (releasedCachedReplicaCoupling placement output rhs hQ) (mk v S)
        (replicaCouplingHeaderCost (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)+n₂) (mk v₂ F) := by
      refine .seq (he₁.mono ?_) ((he₂ 0).mono ?_)
      all_goals intro d z hz; dsimp only [releasedCachedReplicaCouplingWorkspace] at *; omega
    intro depth
    simpa only [Nat.zero_add,Nat.add_right_comm] using mn_exec_within_shift hex depth
  · intro k hk hp
    exact (hframe₂ k hk hp).trans (hforeign k hk)
  · simpa only [hheadersJ.fresh 125 (by simp),List.append_nil] using harchive
  · rw [hhigh 138 (by decide)] at hpage
    exact hpage

  · rw [hnativeJ] at hnativeF
    exact congrArg Stacks.R hnativeF

  · intro k hk hnot hk159 hk161
    exact (hsharedF k hk hnot hk159 hk161).trans (hhigh k hk)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
