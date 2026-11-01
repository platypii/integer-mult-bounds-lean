module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectReplicaRecoveryRhs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedReplicaRecoveryRhsStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectedReplicaRecoveryRhs

/-! Produce and collect one recovery pair in the retained machine. The only
new archive is outside the old worker; the shared bank can serve the next row. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 257 Q A U}

noncomputable def collectedReplicaRecoveryRhsWorkspace (H : ReplicaHaloProblem s) (M : ℕ) : ℕ :=
  (3*replicaRecoveryInputsCost H+packedBoundaryRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) M H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth)+2*(18*(H.span*H.wordWidth)+18)

theorem collectedReplicaRecoveryRhs_exec_within (H : ReplicaHaloProblem s) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hsep : H.span+H.band ≤ s) (r W : ℕ) (solution : List GaussianInt)
    (hlen : solution.length = (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (hfits : ∀ z ∈ solution, Fits H.wordWidth z)
    (rhsQueueTail solutionTail : List (Fin (A+4)))
    (M : ℕ) (hpush : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (v : HS 257 Q A U) (S : Stacks 257 A)
    (hphysical : ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg
      (embStk (Fin.castLE (by decide : 255 ≤ 257)) S)))
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257)) S))
    (h116 : S.R 116 = []) (h167 : S.R 167 = [])
    (hsource : S.R 93 = cstream A H.wordWidth
      (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))++rhsQueueTail)
    (hsolution : S.R 238 = cstream A H.wordWidth solution++solutionTail) :
    let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution
    ∃ v' F n, v'.user = v.user ∧ n ≤ collectedReplicaRecoveryRhsCost H ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          collectedReplicaRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) H M)
        depth (collectedReplicaRecoveryRhs hQ) (mk v S) n (mk v' F)) ∧
      F.R 93 = rhsQueueTail ∧ F.R 238 = solutionTail ∧ F.R 110 = S.R 110 ∧ F.R 132 = S.R 132 ∧
      F.R 125 = cstream A H.wordWidth (packedInterval H.origin H.span Y)++S.R 125 ∧
      F.R 256 = cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))++S.R 256 ∧
      ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257)) F) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) F)) ∧
      F.R 116 = [] ∧ F.R 167 = [] ∧
      (∀ k : Fin 257, k ∉ [93,110,116,125,132,167,238,256] → F.R k = S.R k) ∧
      F.L = S.L ∧ F.inp = S.inp ∧ F.out = S.out := by
  dsimp only
  let e : Fin 255 → Fin 257 := Fin.castLE (by decide)
  have hinj : Function.Injective e := by
    intro i j he
    exact Fin.ext (congrArg (fun k : Fin 257 => k.val) he)
  obtain ⟨vi,J,n,hu,hn,he,h93,h238,h132,h110,hcoreJ,h116J,h167J,hframeJ,hL,hinp,hout⟩ :=
    preparedReplicaRecoveryRhs_exec_within (body := fun z : Empty => nomatch z) H hQ hA hsep r W solution hlen hfits
      rhsQueueTail solutionTail M hpush (embDn e v) (embStk e S) hphysical hcore h116 h167 hsource hsolution
  obtain ⟨v₁,hv₁,hu₁,he₁⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim) hinj
    (fun z => nomatch z) (he 0).toExec v rfl S rfl
  let G := embOvr e J.get S
  have hget (i : Fin 255) : G.R (e i) = J.R i := by
    have hh := embOvr_get hinj J.get S (.rt i)
    change G.R (e i) = (J.R i).map id at hh
    simpa only [List.map_id] using hh
  have hframeG (k : Fin 257) (hk : k ∉ [93,110,116,132,167,238]) : G.R k = S.R k := by
    by_cases hlow : k.val < 255
    · have heq : e ⟨k.val,hlow⟩ = k := Fin.ext rfl
      rw [←heq,hget]
      apply hframeJ
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk ⊢
      norm_num at hk ⊢
      exact hk
    · exact (embOvr_off J.get S (by
        intro i hi
        have hh := congrArg (fun k : Fin 257 => k.val) hi
        have hi' := i.isLt
        change i.val = k.val at hh
        omega)).2
  let Y := boundarySolutionField (haloBoundary s H.t H.band H.origin (H.origin+H.span)) solution
  let C := cstream A H.wordWidth (packedInterval H.origin H.span (H.Fs.reverse.getD r (fun _ => 0)))
  let R := cstream A H.wordWidth (packedInterval H.origin H.span (replicaRecoveryRhs H r Y))
  let ys := cstream A H.wordWidth (packedInterval H.origin H.span Y)
  have hcoreG : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257)) G) := by
    change ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e G))
    rw [embStk_ovr hinj]
    exact hcoreJ
  have hvolume : (G.R 251).length = H.span*H.wordWidth := by
    rw [hframeG 251 (by decide)]
    exact hphysical.volume
  have hcollect (depth : ℕ) := collectReplicaRecoveryRhs_exec_within (body := body) (H.span*H.wordWidth)
    R C ys (S.R 110) (S.R 132)
    (by simp [R,length_cstream,packedInterval_length _ H.span_fit])
    (by simp [C,length_cstream,packedInterval_length _ H.span_fit])
    (by simp [ys,length_cstream,packedInterval_length _ H.span_fit]) v₁ G hvolume
    ((hget 110).trans h110) ((hget 132).trans h132)
    (hcoreG.native 104 (by decide) (by decide) (by decide))
    (hcoreG.native 105 (by decide) (by decide) (by decide)) depth
  obtain ⟨v₂,hu₂,he₂⟩ := hcollect 0
  let F := collectedReplicaRecoveryRhsState G R ys (S.R 110) (S.R 132)
  have hframeF (k : Fin 257) (hk : k ∉ [110,132,256,125]) : F.R k = G.R k :=
    collectedRecoveryPrefixes_frame G 110 132 256 125 R ys _ _ k hk
  have hcoreF := collectedReplicaRecoveryRhsState_core H W G R ys (S.R 110) (S.R 132) hcoreG
  have hphysicalF : ReplicaBoundaryRhsReady H
      (embStk replicaBoundaryPhaseReg (embStk e F)) := by
    have hc : ReplicaRecoveryCoreReady H W
        (embStk (Fin.castLE (by decide : 248 ≤ 255)) (embStk e F)) := hcoreF
    apply ReplicaBoundaryRhsReady.of_recovery_core H W hphysical hc
    intro k hk
    exact (hframeF (e k) (by
      simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,e,Fin.castLE]
      have hi := k.isLt
      norm_num
      omega)).trans (hframeG (e k) (by
        simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff,e,Fin.castLE]
        norm_num
        omega))
  refine ⟨v₂,F,n+(18*(H.span*H.wordWidth)+18),hu₂.trans (hu₁.trans hu),by unfold collectedReplicaRecoveryRhsCost; omega,
    ?_,?_,?_,?_,?_,?_,?_,hcoreF,hphysicalF,?_,?_,?_,?_,?_,?_⟩
  · intro depth
    have ht₁ := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
      hinj (fun z => nomatch z) (he depth) v rfl S rfl he₁
    obtain ⟨v₃,_,ht₂⟩ := hcollect depth
    have hfinal := (ht₂.toExec.unique he₂.toExec).2
    exact mn_seq_within_add (a := (3*replicaRecoveryInputsCost H+packedBoundaryRecoveryRhsWorkspace (Q := Q) (A := A) (U := U) (2^15*H.p) M H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span) H.origin H.span H.metadataWidth)) (b := 2*(18*(H.span*H.wordWidth)+18))
      ht₁ (ht₂.cast rfl hfinal)
  · exact (hframeF 93 (by decide)).trans ((hget 93).trans h93)
  · exact (hframeF 238 (by decide)).trans ((hget 238).trans h238)
  · simp [F,collectedReplicaRecoveryRhsState,collectedRecoveryPrefixes]
  · simp [F,collectedReplicaRecoveryRhsState,collectedRecoveryPrefixes]
  · change ys++G.R 125 = ys++S.R 125
    rw [hframeG 125 (by decide)]
  · change R++G.R 256 = R++S.R 256
    rw [hframeG 256 (by decide)]
  · exact (hframeF 116 (by decide)).trans ((hget 116).trans h116J)
  · exact (hframeF 167 (by decide)).trans ((hget 167).trans h167J)
  · intro k hk
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hk
    exact (hframeF k (by simp_all)).trans (hframeG k (by simp_all))
  · exact embOvr_left_of_eq S J hL
  · exact hinp
  · exact hout

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
