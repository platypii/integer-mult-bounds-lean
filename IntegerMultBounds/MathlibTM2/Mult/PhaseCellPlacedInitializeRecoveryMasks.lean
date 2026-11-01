module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializeRecoveryMasksStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveryMaskFrame
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryMasks
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! Initialize both shared masks beside the retained recovery bank in the actual caller. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Layer IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

def recoveryMaskCallerReg (i : Fin 168) : Fin 392 :=
  replicaRecoveryPreparationCallerWorkerReg (Fin.castLE (by decide) i)

theorem recoveryMaskCallerReg_injective : Function.Injective recoveryMaskCallerReg := by
  intro i j h
  have hh := replicaRecoveryPreparationCallerReg_injective h
  exact Fin.ext (congrArg (fun k : Fin 258 => k.val) hh)

def initializedRecoveryMaskState (H : ReplicaHaloProblem s) (S : Stacks 392 A) : Stacks 392 A :=
  {S with R := (Function.update (Function.update S.R (recoveryMaskCallerReg 159)
    ((couplingRibbonFlags (s := s) true H.t H.band H.origin (H.origin+H.span)
      H.origin H.span).map (fun flag => pairSym A flag flag))) (recoveryMaskCallerReg 161)
    (recoveryGuardIntervalSymbols true A s H.t (2*H.band) H.origin
      (H.origin+H.span) H.origin H.span))}

def placedInitializeRecoveryMasks : Pr P 392 Q A U :=
  embProg recoveryMaskCallerReg Empty.elim initializeRecoveryMasks

noncomputable def initializeRecoveryMasksWorkspace (H : ReplicaHaloProblem s) : ℕ :=
  mnProgPush (initializeRecoveryMasks (P := Empty) (Q := Q) (A := A) (U := U))*
    initializeRecoveryMasksCost H.metadataWidth H.span H.band

theorem initializedRecoveryMaskState_frame (H : ReplicaHaloProblem s) (S : Stacks 392 A)
    (k : Fin 392) (h159 : k ≠ recoveryMaskCallerReg 159) (h161 : k ≠ recoveryMaskCallerReg 161) :
    (initializedRecoveryMaskState H S).R k = S.R k := by
  simp [initializedRecoveryMaskState,h159,h161]

theorem initializedRecoveryMaskState_ready (H : ReplicaHaloProblem s) (S : Stacks 392 A) :
    ReplicaRecoveryMasksReady H (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg (initializedRecoveryMaskState H S))) := by
  constructor
  · change (initializedRecoveryMaskState H S).R (recoveryMaskCallerReg 159) = _
    simp [initializedRecoveryMaskState,show recoveryMaskCallerReg 159 ≠ recoveryMaskCallerReg 161 from
      fun he => (by have hh := recoveryMaskCallerReg_injective he; cases hh)]
  · change (initializedRecoveryMaskState H S).R (recoveryMaskCallerReg 161) = _
    simp [initializedRecoveryMaskState]

theorem initializedRecoveryMaskState_worker_frame (H : ReplicaHaloProblem s) (S : Stacks 392 A)
    (k : Fin 257) (h159 : k ≠ 159) (h161 : k ≠ 161) :
    (initializedRecoveryMaskState H S).R (replicaRecoveryPreparationCallerWorkerReg k) =
      S.R (replicaRecoveryPreparationCallerWorkerReg k) := by
  apply initializedRecoveryMaskState_frame
  · intro he
    change replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 257 ≤ 258) k) =
      replicaRecoveryPreparationCallerReg 159 at he
    have hh := replicaRecoveryPreparationCallerReg_injective he
    exact h159 (Fin.ext (congrArg (fun i : Fin 258 => i.val) hh))
  · intro he
    change replicaRecoveryPreparationCallerReg (Fin.castLE (by decide : 257 ≤ 258) k) =
      replicaRecoveryPreparationCallerReg 161 at he
    have hh := replicaRecoveryPreparationCallerReg_injective he
    exact h161 (Fin.ext (congrArg (fun i : Fin 258 => i.val) hh))

theorem initializedRecoveryMaskState_off (H : ReplicaHaloProblem s) (S : Stacks 392 A)
    (k : Fin 392) (hk : ∀ i, replicaRecoveryPreparationCallerReg i ≠ k) :
    (initializedRecoveryMaskState H S).L k = S.L k ∧
      (initializedRecoveryMaskState H S).R k = S.R k := by
  refine ⟨rfl,initializedRecoveryMaskState_frame H S k ?_ ?_⟩
  · exact (hk 159).symm
  · exact (hk 161).symm

theorem initializedRecoveryMaskState_gather (H : ReplicaHaloProblem s) (S : Stacks 392 A) :
    embStk (Fin.castLE (by decide : 126 ≤ 392)) (initializedRecoveryMaskState H S) =
      embStk (Fin.castLE (by decide : 126 ≤ 392)) S := by
  refine Stacks.ext rfl rfl rfl ?_
  funext k
  exact (initializedRecoveryMaskState_off H S _
    (fun i => replicaRecoveryPreparationCallerReg_gather_disjoint i k)).2

theorem placedInitializeRecoveryMasks_exec_within (H : ReplicaHaloProblem s) (W : ℕ)
    (v : HS 392 Q A U) (S : Stacks 392 A)
    (hcore : ReplicaRecoveryCoreReady H W (embStk (Fin.castLE (by decide : 248 ≤ 257))
      (embStk replicaRecoveryPreparationCallerWorkerReg S)))
    (h159 : S.R (recoveryMaskCallerReg 159) = []) (h161 : S.R (recoveryMaskCallerReg 161) = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ initializeRecoveryMasksCost H.metadataWidth H.span H.band ∧
      ∀ depth, ExecWithin body
        (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+
          initializeRecoveryMasksWorkspace (Q := Q) (A := A) (U := U) H)
        depth placedInitializeRecoveryMasks (mk v S) n (mk v' (initializedRecoveryMaskState H S)) := by
  let e := recoveryMaskCallerReg
  have hgeometry : CouplingIntervalMetadata H.metadataWidth s H.t H.band H.origin (H.origin+H.span)
      H.origin H.span (embStk e S) := hcore.geometry
  have hclean : ∀ k : Fin 168, k.val < 63 → (embStk e S).R k = [] := by
    intro k hk
    exact hcore.native ⟨k.val,by omega⟩ (by intro he; have hh := congrArg Fin.val he; change k.val = 93 at hh; omega)
      (by intro he; have hh := congrArg Fin.val he; change k.val = 110 at hh; omega)
      (by intro he; have hh := congrArg Fin.val he; change k.val = 116 at hh; omega)
  obtain ⟨vi,n,hu,hn,he⟩ := initializeRecoveryMasks_exec_within (body := fun z : Empty => nomatch z)
    H.s_lt_t (by have hh := H.span_fit; omega) H.span_fit H.band_fit H.span_fit
    H.coupling_geometry.2 H.coupling_geometry.1 (embDn e v) (embStk e S) hgeometry hclean
    (hcore.clean 136 (by decide)) (hcore.clean 158 (by decide)) h159 h161
  obtain ⟨v',hv,hu',he'⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    recoveryMaskCallerReg_injective (fun z => nomatch z) (he 0).toExec v rfl S rfl
  have ht : embOvr e
      ({embStk e S with R := (Function.update (Function.update (embStk e S).R 159
        ((couplingRibbonFlags (s := s) true H.t H.band H.origin (H.origin+H.span)
          H.origin H.span).map (fun flag => pairSym A flag flag))) 161
        (recoveryGuardIntervalSymbols true A s H.t (2*H.band) H.origin
          (H.origin+H.span) H.origin H.span))} : Stacks 168 A).get S = initializedRecoveryMaskState H S := by
    rw [embOvr_updateR_updateR recoveryMaskCallerReg_injective]
    rfl
  refine ⟨v',n,hu'.trans hu,hn,?_⟩
  intro depth
  have hb := exec_emb_within_stock_of_exec (ι := Empty.elim) (body' := body)
    recoveryMaskCallerReg_injective (fun z => nomatch z) (he depth) v rfl S rfl he'
  exact hb.cast rfl (congrArg (mk v') ht)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
