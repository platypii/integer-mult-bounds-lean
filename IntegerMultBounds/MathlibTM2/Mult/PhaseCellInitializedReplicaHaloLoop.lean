module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaHaloLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedHaloLengthKeys
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaAccumulator

/-! Start the packed interior pass from ordinary headers and an untouched output
suffix. Both the actual key schedule and bounded accumulator are constructed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s T Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P T Q A U}

noncomputable def initializedReplicaHaloLoop (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (initializeReplicaAccumulator plan dst)
    (.seq (placedHaloLengthKeys plan) (runReplicaHaloLoop plan dst hR hQ))

theorem initializedReplicaHaloLoop_exec_within (H : ReplicaHaloProblem s)
    (plan : ReplicaInteriorPlacement T) (dst : Fin T)
    (hgd : ∀ k, plan.gather k ≠ dst) (hsd : ∀ k, plan.solver k ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (R K : ℕ)
    (hpushR : mnProgPush (rpProg (P := Empty) (Q := Q) (A := A) (U := U)
      Fixed.ringReg Fixed.hostReg Fixed.layout.ι_inj (by decide) hR) ≤ R)
    (hpushK : mnProgPush (cmulBlock cr (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr)) ≤ K)
    (buffers : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
    (headers : ReplicaLoopHeaders H plan.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk plan.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out)
    (hcache : S.R (plan.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (plan.solver k) = [])
    (hinput : S.inp = buffers.input) (houtput : S.out = buffers.output)
    (hsaved : embStk plan.gather S = buffers.savedGather)
    (hkeys : S.R (plan.gather 87) = buffers.keyTail) (hdst : S.R dst = buffers.accumulatorTail)
    (h86 : S.R (plan.gather 86) = []) (h119 : S.R (plan.gather 119) = []) (depth : ℕ) :
    let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
    let initCost := allocateZeroLineCost H.Fs.length (H.span*H.wordWidth)
    let setupCost := placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth
    ∃ v' F n, v'.user = v.user ∧ n ≤ initCost+(setupCost+((keys.map (fun L => H.keyCost L+3)).sum+2)) ∧
      ReplicaHaloLoopState H plan dst buffers keys [] F ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
        (2*initCost+(3*setupCost+(keys.map (H.keyWorkspace (A := A) (U := U) hQ R K)).sum))) depth
        (initializedReplicaHaloLoop plan dst hR hQ) (mk v S) n (mk v' F) := by
  dsimp only
  let keys := haloLengthKeys s H.t H.band H.origin (H.origin+H.span)
  let rows := replicaZeroRows A H.Fs.length H.span H.wordWidth
  have hN : (S.R (plan.gather 121)).length = H.Fs.length := by
    simpa [replicaFactoryHeaderValue] using headers.masters (121,113) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide)
  obtain ⟨v₁,n₁,hu₁,hn₁,he₁⟩ := initializeReplicaAccumulator_exec_within (body := body) plan dst hgd
    H.Fs.length H.span H.wordWidth v S hN headers.volume
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl <;> exact headers.fresh _ (by simp)) depth
  let M : Stacks T A := {S with R := Function.update S.R dst (rows.flatten++S.R dst)}
  have hgM (k : Fin 126) : M.R (plan.gather k) = S.R (plan.gather k) := by simp [M,hgd]
  have headersM : ReplicaLoopHeaders H plan.gather buffers M := headers.of_frame (fun k _ _ => hgM k)
  obtain ⟨v₂,n₂,hu₂,hn₂,he₂⟩ := placedHaloLengthKeys_exec_within (body := body) plan
    (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
    (by have hp := H.p_pos; norm_num; omega) (NeZero.pos s) H.s_lt_t H.u_pos H.band_fit
    (by have hh := H.span_fit; omega) H.span_fit (by omega) v₁ M
    (by simpa [replicaFactoryHeaderValue] using headersM.masters (97,97) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide))
    (by simpa [replicaFactoryHeaderValue] using headersM.masters (98,98) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide))
    (by simpa [replicaFactoryHeaderValue] using headersM.masters (100,100) (by simp [replicaFactoryHeaderCopies]) (by decide) (by decide))
    headersM.origin headersM.endpoint headersM.width
    (by
      intro k hk
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
      rcases hk with rfl | rfl | rfl | rfl
      · exact headersM.fresh _ (by simp)
      · exact headersM.fresh _ (by simp)
      · rw [hgM]; exact h86
      · rw [hgM]; exact h119) headersM.blank depth
  let G : Stacks T A := {M with R := (Function.update (Function.update M.R (plan.gather 87)
    (haloPositiveLengthPackets A H.metadataWidth s H.t H.band H.origin (H.origin+H.span)++M.R (plan.gather 87)))
    (plan.gather 119) (List.replicate keys.length tick))}
  change n₂ ≤ placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth at hn₂
  change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v₁ M)+depth+
    3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth) depth
    (placedHaloLengthKeys plan) (mk v₁ M) n₂ (mk v₂ G) at he₂
  have hgG (k : Fin 126) (h87 : k ≠ 87) (h119' : k ≠ 119) : G.R (plan.gather k) = S.R (plan.gather k) := by
    simp [G,plan.gather_injective.eq_iff,h87,h119',hgM]
  have hsG : embStk plan.solver G = embStk plan.solver S := by
    refine Stacks.ext rfl rfl rfl ?_
    funext k
    simp [G,M,embStk,(plan.disjoint 87 k).symm,(plan.disjoint 119 k).symm,hsd]
  have hdG : G.R dst = rows.flatten++buffers.accumulatorTail := by simp [G,M,(hgd 87).symm,(hgd 119).symm,hdst]
  have hInv : ReplicaHaloLoopState H plan dst buffers keys keys G := by
    refine ⟨fun _ h => h,headers.of_frame hgG,?_,?_,?_,hinput,houtput,?_,?_,?_,?_,?_,?_⟩
    · rw [hsG]; exact hbank
    · exact (congrFun (congrArg Stacks.R hsG) 117).trans hcache
    · intro k hk
      exact (congrFun (congrArg Stacks.R hsG) k).trans (hsolverFresh k hk)
    · have hh := congrArg (fun B : Stacks 126 A => B.L) hsaved
      exact hh
    · intro k h87 h119'
      exact (hgG k h87 h119').trans (congrFun (congrArg Stacks.R hsaved) k)
    · simp [G,haloPositiveLengthPackets,keys,hgM,hkeys,plan.gather_injective.eq_iff]
    · simp [G]
    · exact ⟨rows,replicaZeroRows_length _ _ _ _,replicaZeroRows_row_length _ _ _ _,
        replicaZeroRows_range _ _ _ _ _ _,hdG⟩
    · intro L hL hnot; exact False.elim (hnot hL)
  obtain ⟨v₃,F,n₃,hu₃,hn₃,hInvF,he₃⟩ := runReplicaHaloLoop_exec_within (body := body) H plan dst hgd hsd hR hQ hA
    buffers keys (H.candidate_bounds hpad) R K hpushR hpushK keys v₂ G hInv depth
  dsimp only [keys] at hn₃ he₃
  refine ⟨v₃,F,n₁+(n₂+n₃),hu₃.trans (hu₂.trans hu₁),by omega,hInvF,?_⟩
  have hsize₁ := he₁.final
  have hsize₂ := he₂.final
  change mnSize (mk v₁ M)+depth ≤ mnSize (mk v S)+depth+2*allocateZeroLineCost H.Fs.length (H.span*H.wordWidth) at hsize₁
  change mnSize (mk v₂ G)+depth ≤ mnSize (mk v₁ M)+depth+
    3*placedHaloLengthKeysCost s H.t H.band H.origin (H.origin+H.span) H.metadataWidth at hsize₂
  refine .seq (he₁.mono ?_) (.seq (he₂.mono ?_) (he₃.mono ?_))
  all_goals intro d z hz; omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
