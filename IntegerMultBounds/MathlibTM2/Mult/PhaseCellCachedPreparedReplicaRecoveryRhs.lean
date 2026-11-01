module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryReady
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCachedReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! Advance the original RHS queue and compute the second-pass RHS without
running a scalar interior solve. The exact output is ready to be archived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 255 Q A U}

noncomputable def cachedPreparedReplicaRecoveryRhs (hQ : SS.states ≤ Q) : Pr P 255 Q A U :=
  .seq prepareReplicaRecoveryInputs
    (embProg (Fin.castLE (by decide : 248 ≤ 255)) Empty.elim (cachedPackedBoundaryRecoveryRhs hQ))

theorem cachedPreparedReplicaRecoveryRhs_exec_within (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hsep : H.span+H.band ≤ s) (r W : ℕ) (solution : List GaussianInt)
    (hlen : solution.length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hfits : ∀ z ∈ solution, Fits H.wordWidth z)
    (rhsQueueTail solutionTail : List (Fin (A+4)))
    (M : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (v : HS 255 Q A U) (S : Stacks 255 A)
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg S))
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) S))
    (hmasks : ReplicaRecoveryMasksReady H (embStk (Fin.castLE (by decide : 248 ≤ 255)) S))
    (h116 : S.R 116 = []) (h167 : S.R 167 = [])
    (hsource : S.R 93 = cstream A H.wordWidth
      (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsQueueTail)
    (hsolution : S.R 238 = cstream A H.wordWidth solution++solutionTail) :
    let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution
    ∃ v' F n, v'.user = v.user ∧ n ≤ replicaRecoveryInputsCost H+cachedReplicaRecoveryRhsCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+(3*replicaRecoveryInputsCost H+cachedPackedBoundaryRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) M H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth))
        depth (cachedPreparedReplicaRecoveryRhs hQ) (mk v S) n (mk v' F)) ∧
      F.R 93 = rhsQueueTail ∧ F.R 238 = solutionTail ∧
      F.R 132 = cstream A H.wordWidth (packedInterval H.origin H.span Y)++S.R 132 ∧
      F.R 110 = cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))++
        (cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++S.R 110) ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) F) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧
      (∀ k : Fin 255, k ∉ [93,110,116,132,167,238] → F.R k = S.R k) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out := by
  dsimp only
  let xs := cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))
  let J := preparedReplicaRecoveryInputState S xs rhsQueueTail
  let e : Fin 248 → Fin 255 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 255 => k.val) he)
  have hlenXs : xs.length = H.span*H.wordWidth := by
    simp only [xs,length_cstream,packedInterval_length _ H.span_fit]
  obtain ⟨v₀,hu₀,he₀,hentry⟩ := prepareReplicaRecoveryReady_exec (body := body) H W
    (H.Fs.reverse.getD r (fun _ => 0)) rhsQueueTail v S hphysical hcore hsource h116 h167
  let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution
  have hmasksJ : ReplicaRecoveryMasksReady H (embStk e J) := by
    apply hmasks.of_frame
    · exact preparedReplicaRecoveryInputState_frame S xs rhsQueueTail 159 (by decide)
    · exact preparedReplicaRecoveryInputState_frame S xs rhsQueueTail 161 (by decide)
  let T := replicaRecoveryRhsState H r Y solutionTail (S.R 132) (S.R 110) (embStk e J)
  obtain ⟨vi,n,hu,hn,he⟩ := cachedReplicaRecoveryRhs_exec_within (body := fun z : Empty => nomatch z) H hQ hA hsep r W
    solution hlen hfits solutionTail (List.replicate (H.span*H.wordWidth) tick) (S.R 132)
    (List.replicate (H.span*H.wordWidth) tick) (S.R 110) (by simp) (by simp)
    M hpush (embDn e v₀) (embStk e J) hmasksJ hentry
    (by change J.R 238 = _; rw [preparedReplicaRecoveryInputState_frame S xs rhsQueueTail 238 (by decide)]; exact hsolution)
    (by change J.R 132 = _; simp [J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hlenXs])
    (by change J.R 110 = _; simp [J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,hlenXs]; rfl)
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) (he 0).toExec v₀ rfl J rfl
  let F := embOvr e T.get J
  have hget (i : Fin 248) : F.R (e i) = T.R i := by
    have hh := embOvr_get hinj T.get J (.rt i)
    change F.R (e i) = (T.R i).map id at hh
    simpa only [List.map_id] using hh
  have hframe (k : Fin 255) (hk : k ∉ [93,110,116,132,167,238]) : F.R k = S.R k := by
    have hh := embOvr_off (e := e) (j := k) T.get J
    by_cases hlow : k.val < 248
    · have heq : e ⟨k.val,hlow⟩ = k := Fin.ext rfl
      rw [←heq,hget]
      simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
      have hTk : T.R ⟨k.val,hlow⟩ = J.R k := by
        simp only [Fin.ext_iff] at hk
        norm_num at hk
        simp [T,replicaRecoveryRhsState,embStk,e,Fin.ext_iff,hk.2.1,hk.2.2.1,
          hk.2.2.2.1,hk.2.2.2.2.1,hk.2.2.2.2.2]
      exact hTk.trans (preparedReplicaRecoveryInputState_frame S xs rhsQueueTail k (by simp_all))
    · rw [(hh (fun i hi => by have hv := congrArg Fin.val hi; have hi' := i.isLt; dsimp [e] at hv; omega)).2]
      exact preparedReplicaRecoveryInputState_frame S xs rhsQueueTail k (by simp_all)
  refine ⟨v',F,replicaRecoveryInputsCost H+n,hu'.trans (hu.trans hu₀),Nat.add_le_add_left hn _,
    ?_,?_,?_,?_,?_,?_,?_,?_,hframe,?_,rfl,rfl⟩
  · intro depth
    have hnative : mnNativePushBound 3
        (prepareReplicaRecoveryInputs (P := P) (Q := Q) (A := A) (U := U)) := by
      simp [prepareReplicaRecoveryInputs,stageReplicaRecoveryRhs,seedReplicaRecovery,takePrefix,
        transfer,transferAct,ucopy,umulSym,scanR,drainR,popDo,keepIn,pushN,
        copyR,copyStep,moveR,moveStep,whileR,peekR,mnNativePushBound,mnActPush]
    have ht₀ := mn_native_exec_within he₀ 3 hnative depth
      (mnSize (mk v S)+depth+3*replicaRecoveryInputsCost H) (by rfl)
    have ht := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
      hinj (fun z => nomatch z) (he depth) v₀ rfl J rfl he'
    exact mn_seq_within_add (a := 3*replicaRecoveryInputsCost H) (b := cachedPackedBoundaryRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) M H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth) ht₀ ht
  · rw [show F.R 93 = T.R 93 from hget 93]
    simp [T,replicaRecoveryRhsState,J,preparedReplicaRecoveryInputState,seededReplicaRecoveryState,stagedReplicaRecoveryRhsState,embStk,e]
  · exact (hget 238).trans (by simp [T,replicaRecoveryRhsState])
  · exact (hget 132).trans (by simp [T,replicaRecoveryRhsState,Y])
  · exact (hget 110).trans (by simp [T,replicaRecoveryRhsState,Y])
  · rw [embStk_ovr hinj]
    exact replicaRecoveryRhsState_core H r W Y solutionTail _ _ _ hentry.toReplicaRecoveryCoreReady
  · exact (hget 116).trans (by simp [T,replicaRecoveryRhsState])
  · exact (hget 167).trans (by simp [T,replicaRecoveryRhsState])
  · exact embOvr_left_of_eq J T rfl

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
