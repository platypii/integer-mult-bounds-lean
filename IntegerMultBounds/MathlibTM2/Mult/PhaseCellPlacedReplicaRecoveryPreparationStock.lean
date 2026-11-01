module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryPreparationLoopStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedReplicaRecoveryPreparation

/-! Execute recovery preparation in the common caller. Ordinary gather
headers are spectators, while the produced archives occupy their final roles. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.SchurDominance IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

theorem placedReplicaRecoveryPreparation_exec_within (H : ReplicaHaloProblem s) (target : ℕ)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hsep : H.span+H.band ≤ s)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (columns : List (ZMod s → GaussianInt))
    (push : BoundarySolvePushBounds (A := A) (U := U) hQ) (c : ℕ)
    (hpush : mnNativePushBound c (replicaBoundaryRhs (P := Empty) (Q := Q) (A := A) (U := U)))
    (M : ℕ) (hpushM : mnProgPush (rmulOne (P := Empty) (Q := Q) (A := A) (U := U)
      mul mul_injective (by decide) hQ cr) ≤ M) (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD r (fun _ => 0) i)).re))
    (residualTail rhsTail boundaryTail recoveryTail : List (Fin (A+4)))
    (v : HS 392 Q A U) (S : Stacks 392 A)
    (hcount : (S.R 390).length = H.Fs.length)
    (hready : ReplicaRecoveryPreparationReady H target X columns residualTail rhsTail boundaryTail recoveryTail
      (embStk replicaRecoveryPreparationCallerWorkerReg S)) :
    ∃ v' F n, ∃ B : ReplicaRecoveryBatch H target X,
      v'.user = v.user ∧ n ≤ H.Fs.length*(replicaRecoveryPreparationRowCost H+3)+2 ∧
      (∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+replicaRecoveryPreparationRowWorkspace H hQ push c M)
        depth (placedReplicaRecoveryPreparation hQ) (mk v S) n (mk v' F)) ∧ F.R 390 = [] ∧
      F.R 257 = (List.ofFn B.boundary).flatMap
        (fun Y => cstream A H.wordWidth (packedInterval H.origin H.span Y))++boundaryTail ∧
      F.R 389 = B.inputs.reverse.flatMap
        (fun R => cstream A H.wordWidth (packedInterval H.origin H.span R))++recoveryTail ∧
      embStk (Fin.castLE (by decide : 126 ≤ 392)) F = embStk (Fin.castLE (by decide : 126 ≤ 392)) S ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      let W := embStk replicaRecoveryPreparationCallerWorkerReg F
      ReplicaBoundaryFactorData H target columns (embStk (Fin.castLE (by decide : 242 ≤ 257)) W) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk (Fin.castLE (by decide : 248 ≤ 257)) W) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk (Fin.castLE (by decide : 255 ≤ 257)) W)) ∧
      W.R 238 = residualTail ∧ W.R 93 = rhsTail ∧ W.R 116 = [] ∧ W.R 167 = [] ∧
      W.L = (embStk replicaRecoveryPreparationCallerWorkerReg S).L ∧
      W.R 110 = S.R (replicaRecoveryPreparationCallerWorkerReg 110) ∧
      mnSize (mk (embDn replicaRecoveryPreparationCallerWorkerReg v') W) =
        mnSize (mk (embDn replicaRecoveryPreparationCallerWorkerReg v)
          (embStk replicaRecoveryPreparationCallerWorkerReg S)) ∧
      (∀ k : Fin 392, (∀ i, replicaRecoveryPreparationCallerReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) := by
  let e := replicaRecoveryPreparationCallerReg
  obtain ⟨vi,G,n,B,hu,hn,he,hcounter,h238,h93,h125,h256,hfactor,hcore,hphysical,
    h116,h167,hL,hinp,hout,h110,h132,hframe,hstock⟩ := replicaRecoveryPreparationLoop_exec_within
    (body := fun z : Empty => nomatch z) H target hQ hA hp hwidth hsep htarget columns push c hpush M hpushM X hX
      residualTail rhsTail boundaryTail recoveryTail (embDn e v) (embStk e S)
      (by change (S.R 390).length = _; exact hcount) hready.cursor hready.factor hready.left hready.physical
      hready.core hready.count hready.mask
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    replicaRecoveryPreparationCallerReg_injective (fun z => nomatch z) (he 0).toExec v rfl S rfl
  let F := embOvr e G.get S
  have hproj : embStk e F = G := embStk_ovr replicaRecoveryPreparationCallerReg_injective G S
  have hget (i : Fin 258) : F.R (e i) = G.R i := by
    have hh := embOvr_get replicaRecoveryPreparationCallerReg_injective G.get S (.rt i)
    change F.R (e i) = (G.R i).map id at hh
    simpa only [List.map_id] using hh
  have hworker : embStk replicaRecoveryPreparationCallerWorkerReg F = embStk replicaRecoveryPreparationWorkerReg G := by
    change embStk replicaRecoveryPreparationWorkerReg (embStk e F) = _
    rw [hproj]
  have hoff (k : Fin 392) (hk : ∀ i, e i ≠ k) : F.L k = S.L k ∧ F.R k = S.R k := embOvr_off G.get S hk
  have hgather : embStk (Fin.castLE (by decide : 126 ≤ 392)) F =
      embStk (Fin.castLE (by decide : 126 ≤ 392)) S := by
    refine Stacks.ext hinp hout ?_ ?_ <;> funext j
    · exact (hoff _ (fun i => replicaRecoveryPreparationCallerReg_gather_disjoint i j)).1
    · exact (hoff _ (fun i => replicaRecoveryPreparationCallerReg_gather_disjoint i j)).2
  refine ⟨v',F,n,B,hu'.trans hu,hn,?_,?_,?_,?_,hgather,hinp,hout,?_⟩
  · intro depth
    exact exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
      replicaRecoveryPreparationCallerReg_injective (fun z => nomatch z) (he depth) v rfl S rfl he'
  · exact (show F.R 390 = G.R 257 from hget 257).trans hcounter
  · exact (show F.R 257 = G.R 125 from hget 125).trans h125
  · exact (show F.R 389 = G.R 256 from hget 256).trans h256
  · rw [hworker]
    exact ⟨hfactor,hcore,hphysical,h238,h93,h116,h167,hL,h110,hstock,hoff⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
