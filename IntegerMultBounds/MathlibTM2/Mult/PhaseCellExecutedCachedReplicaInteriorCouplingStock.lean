module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCachedReplicaInteriorCouplingStock

/-! Execute the first interior pass and residual coupling from ordinary headers.
The generated key loop and its accuracy contract are composed structurally. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def initializedCachedReplicaInteriorWorkspace (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q)
    (R K M : ℕ) : ℕ :=
  (2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
    (3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
      ((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map
        (H.keyWorkspace (A := A) (U := U) hQ R K)).sum))+
      cachedReplicaInteriorFinishingWorkspace (Q := Q) (A := A) (U := U) H M

theorem initializedCachedReplicaInteriorCoupling_exec_within (H : ReplicaHaloProblem s) {plan : ReplicaInteriorPlacement T}
    (placement : ReplicaCouplingPlacement plan) (output rhs : Fin T)
    (houtput : ∀ k, plan.gather k ≠ output) (hrhs : ∀ k, plan.gather k ≠ rhs)
    (hbankOutput : ∀ k, placement.bank k ≠ output) (hbankRhs : ∀ k, placement.bank k ≠ rhs)
    (hsolverOutput : ∀ k, plan.solver k ≠ output) (hsolverRhs : ∀ k, plan.solver k ≠ rhs)
    (hsep : output ≠ rhs) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (M : ℕ)
    (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (hA : 96 ≤ A)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H plan.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out)
    (hcache : S.R (plan.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = [])
    (hinput : S.inp = buffers.input) (houtputStream : S.out = buffers.output)
    (hsaved : embStk plan.gather S = buffers.savedGather)
    (hkeys : S.R (plan.gather 87) = buffers.keyTail) (hdst : S.R output = buffers.accumulatorTail)
    (h86 : S.R (plan.gather 86) = []) (h119 : S.R (plan.gather 119) = []) (depth : ℕ)
    (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]), S.R (placement.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167], S.R (placement.bank k) = [])
    (h136 : S.R (placement.bank 136) = []) (h159 : S.R (placement.bank 159) = [])
    (h161 : S.R (placement.bank 161) = []) :
    ∃ v' G m, ∃ Ds : List (ZMod s → GaussianInt), v'.user = v.user ∧ m ≤ (allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)+
        (placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth+
          (((haloLengthKeys s H.t H.band H.origin (H.origin+H.span)).map (fun L => H.keyCost L+3)).sum+2)))+
        realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+releasedRetiredCachedReplicaCouplingCost H ∧
      ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          initializedCachedReplicaInteriorWorkspace (A := A) (U := U) H hQ R K M) depth
        (initializedCachedReplicaInteriorCoupling placement output rhs hR hQ) (mk v S) m (mk v' G) ∧
      G.R (plan.gather 122) = [] ∧ G.R output = buffers.accumulatorTail ∧ G.R rhs = S.R rhs ∧
      RetainedCouplingReady (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) buffers.rhsTail
        (embStk weightCacheCoreReg (embStk plan.solver G)) ∧
      CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span) H.origin H.span (embStk placement.bank G) ∧
      G.inp = S.inp ∧ G.out = S.out ∧
      (embStk plan.gather G).L = (embStk plan.gather S).L ∧
      (∀ k : Fin 126, k ≠ 125 → G.R (plan.gather k) = S.R (plan.gather k)) ∧
      G.R (plan.solver 117) = buffers.cacheTail ∧
      (∀ k ∈ [(118 : Fin 121),119,120], G.R (plan.solver k) = []) ∧
      (embStk weightCacheCoreReg (embStk plan.solver G)).L =
        (embStk weightCacheCoreReg (embStk plan.solver S)).L ∧
      (∀ k, (∀ i, plan.gather i ≠ k) → (∀ i, plan.solver i ≠ k) → output ≠ k → G.L k = S.L k) ∧
      (∀ k, (∀ i, placement.bank i ≠ k) → (∀ i, plan.gather i ≠ k) →
        (∀ i, plan.solver i ≠ k) → output ≠ k → rhs ≠ k → G.R k = S.R k) ∧
      Ds.length = H.Fs.length ∧
      G.R (plan.gather 125) = Ds.flatMap (fun D => cstream A H.wordWidth (packedInterval H.origin H.span D)) ∧
      (∀ j : Fin Ds.length, ReplicaCouplingResidualSpec H (H.Fs.length-1-j.val) (Ds[j.val]'j.isLt)) ∧
      G.R (placement.bank 138) = cstream A H.wordWidth
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span)++S.R (placement.bank 138) ∧
      (G.R (placement.bank 139)).length =
        (couplingCoefficientPageInterval (2^15*H.p) H.precision s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span).length ∧
      (G.R (placement.bank 140)).length = 2*H.band+1 ∧
      (∀ k ∈ [(127 : Fin 168),143,166,158,135,167], G.R (placement.bank k) = []) ∧
      (∀ D ∈ Ds, (∀ i, ‖value H.precision (D i)‖ ≤ (2 : ℝ)^replicaResidualExponent H) ∧ (∀ i, Fits H.wordWidth (D i))) ∧
      ReplicaCouplingResidualsAccurate H Ds ∧
      (embStk weightCacheCoreReg (embStk plan.solver G)).R =
        counterR H.precision H.wordWidth
          (replicaCouplingUnaryBank A (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
            H.origin (H.origin+H.span) buffers.rhsTail buffers.solverOutputTail S.inp S.out).R ∧
      releaseReplicaCouplingNativeCost (extendStacks (by decide : 117 ≤ 248)
        (embStk weightCacheCoreReg (embStk plan.solver G))) ≤
        replicaCouplingNativeCleanupBound (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
          H.origin (H.origin+H.span) ∧
      (∀ k : Fin 168, 117 ≤ k.val → k ∉ replicaCouplingSetupPorts → G.R (placement.bank k) = S.R (placement.bank k)) ∧
      (CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
        H.origin (H.origin+H.span) (embStk placement.bank S) →
        (S.R (placement.bank 118)).length = H.stage+1 → (S.R (placement.bank 120)).length = H.l →
        PackedHaloRetainedHeaders (2^15*H.p) (H.stage+1) H.precision H.l s H.t H.u H.band
          H.origin (H.origin+H.span) H.metadataWidth H.wordWidth (embStk placement.bank G)) ∧
      ReplicaRecoveryRhsHeaders H plan.gather buffers G := by
  obtain ⟨v₀,F,n,hu₀,hn,hstate,he₀⟩ := initializedReplicaHaloLoop_exec_within (body := body)
    H plan output houtput hsolverOutput hR hQ hA hpad R K hpushR hpushK buffers v S
    headers hbank hcache hsolverFresh hinput houtputStream hsaved hkeys hdst h86 h119 depth
  have hfrhs := initializedReplicaHaloLoop_preserves_right plan output rhs hR hQ hrhs hsolverRhs hsep he₀.toExec
  obtain ⟨v',G,m,Ds,hu,hm,he,hcount,hout,hrhsF,hready,hmeta,hleftF,hinF,houtF,hframe,hrest⟩ :=
    initializedCachedReplicaInteriorCoupling_finish_within (body := body) H placement output rhs houtput hrhs
      hbankOutput hbankRhs hsep hR hQ M hpushM hA hspan horigin buffers v v₀ S F n depth _
      hu₀ he₀ hstate hp hwidth hblank hfresh h136 h159 h161
  have hcacheFrame (j : Fin 121) (hj : 117 ≤ j.val) : G.R (plan.solver j) = F.R (plan.solver j) := by
    apply hframe
    · intro i
      unfold ReplicaCouplingPlacement.bank
      split
      · rename_i hi
        intro he
        have hv := congrArg (fun k : Fin 121 => k.val) (plan.solver_injective he)
        change i.val = j.val at hv
        omega
      · exact placement.extra_solver_disjoint _ j
    · simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨hsolverOutput j,hsolverRhs j,(plan.disjoint 125 j).symm⟩
  refine ⟨v',G,m,Ds,hu,hm.trans ?_,by simpa only [initializedCachedReplicaInteriorWorkspace] using he,hcount,hout,hrhsF.trans hfrhs,hready,hmeta,
    hinF.trans (hstate.input.trans hinput.symm),houtF.trans (hstate.output.trans houtputStream.symm),
    ?_,?_,(hcacheFrame 117 (by decide)).trans hstate.cache,?_,?_,?_,?_,hrest⟩
  · exact Nat.add_le_add_right (Nat.add_le_add_right (Nat.add_le_add_right hn _) _) _
  · funext k
    have hs := congrArg (fun Z : Stacks 126 A => Z.L k) hsaved
    exact (congrFun hleftF (plan.gather k)).trans ((congrFun hstate.gatherLeft k).trans hs.symm)
  · intro k hk
    have hf : G.R (plan.gather k) = F.R (plan.gather k) := by
      apply hframe _ (fun i => placement.bank_gather_disjoint i k)
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨houtput k,hrhs k,plan.gather_injective.ne hk⟩
    apply hf.trans
    by_cases h87 : k = 87
    · subst k
      have hh : F.R (plan.gather 87) = buffers.keyTail := by simpa using hstate.packets
      exact hh.trans hkeys.symm
    by_cases h119k : k = 119
    · subst k
      have hh : F.R (plan.gather 119) = [] := by simpa using hstate.count
      exact hh.trans h119.symm
    exact (hstate.gatherFrame k h87 h119k).trans (congrArg (fun Z : Stacks 126 A => Z.R k) hsaved).symm
  · intro k hk
    have hkBound : 117 ≤ k.val := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> decide
    exact (hcacheFrame k hkBound).trans (hstate.solverFresh k hk)
  · funext i
    have hF := congrArg (fun Z : Stacks 117 A => Z.L i) hstate.bank
    have hS := congrArg (fun Z : Stacks 117 A => Z.L i) hbank
    change F.L (plan.solver (weightCacheCoreReg i)) = [] at hF
    change S.L (plan.solver (weightCacheCoreReg i)) = [] at hS
    exact (congrFun hleftF (plan.solver (weightCacheCoreReg i))).trans (hF.trans hS.symm)
  · intro k hg hs ho
    exact (congrFun hleftF k).trans
      (initializedReplicaHaloLoop_preserves_left plan output k hR hQ hg hs ho he₀.toExec)
  · intro k hbankOff hg hs ho hr
    have hfirst := initializedReplicaHaloLoop_preserves_right plan output k hR hQ hg hs ho he₀.toExec
    have hnot : k ∉ [output,rhs,plan.gather 125] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or]
      exact ⟨ho.symm,hr.symm,(hg 125).symm⟩
    exact (hframe k hbankOff hnot).trans hfirst

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
