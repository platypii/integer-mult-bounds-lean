module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedReplicaBoundaryFactory
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryBatchCoupling
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaRecoveryLeft

/-! Reuse the complete ordinary-header factory in the enlarged cached caller.
Installation, factor generation and old-geometry retirement are all executed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 392 Q A U}

theorem replicaRecoveryBoundaryFactoryReg_reindex (i : Fin 242) :
    replicaRecoveryBoundaryFactoryReg i = Fin.castLE (by decide : 389 ≤ 392) (replicaRecoveryCallerFactoryReg i) := by
  simpa only [replicaRecoveryBoundaryFactoryReg,replicaRecoveryPreparationCallerWorkerReg,
    replicaRecoveryPreparationWorkerReg,replicaRecoveryCallerFactoryReg,replicaRecoveryCallerNativeReg,
    replicaRecoveryCallerWorkerReg,packedBoundaryRecoveryBase,Fin.castLE] using
      replicaRecoveryPreparationCallerReg_worker (Fin.castLE (by decide : 242 ≤ 255) i)

theorem replicaRecoveryBoundaryFactory_reindex_view (S : Stacks 392 A) :
    embStk replicaRecoveryBoundaryFactoryReg S =
      embStk replicaRecoveryCallerFactoryReg (embStk (Fin.castLE (by decide : 389 ≤ 392)) S) := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (replicaRecoveryBoundaryFactoryReg_reindex i)
  · exact congrArg S.R (replicaRecoveryBoundaryFactoryReg_reindex i)

theorem replicaRecoveryBatchCoupling_reindex_view (S : Stacks 392 A) :
    embStk replicaRecoveryBatchCoupling.bank S =
      embStk replicaRecoveryCallerCoupling.bank (embStk (Fin.castLE (by decide : 389 ≤ 392)) S) := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (ReplicaCouplingPlacement.reindex_bank replicaRecoveryCallerCoupling
      (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _) i)
  · exact congrArg S.R (ReplicaCouplingPlacement.reindex_bank replicaRecoveryCallerCoupling
      (Fin.castLE (by decide : 389 ≤ 392)) (Fin.castLE_injective _) i)

omit [NeZero s] in
theorem ReplicaLoopHeaders.of_gather_view {T T' : ℕ} {H : ReplicaHaloProblem s}
    {gather : Fin 126 → Fin T} {gather' : Fin 126 → Fin T'} {buffers : ReplicaLoopBuffers A}
    {S : Stacks T A} {F : Stacks T' A} (h : ReplicaLoopHeaders H gather buffers S)
    (hview : embStk gather' F = embStk gather S) : ReplicaLoopHeaders H gather' buffers F := by
  have hR (k : Fin 126) : F.R (gather' k) = S.R (gather k) := congrFun (congrArg Stacks.R hview) k
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro r hr h102 h116; rw [hR]; exact h.masters r hr h102 h116
  · rw [hR]; exact h.origin
  · rw [hR]; exact h.endpoint
  · rw [hR]; exact h.width
  · rw [hR]; exact h.volume
  · rw [hR]; exact h.source
  · intro k hk; rw [hR]; exact h.blank k hk
  · intro k hk; rw [hR]; exact h.fresh k hk

theorem replicaRecoveryBoundaryFactory_runtime_view (S : Stacks 392 A) :
    embStk (Fin.castLE (by decide : 168 ≤ 242)) (embStk replicaRecoveryBoundaryFactoryReg S) =
      embStk replicaRecoveryBatchCoupling.bank S := by
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact congrArg S.L (show replicaRecoveryBoundaryFactoryReg (Fin.castLE (by decide : 168 ≤ 242) i) =
        replicaRecoveryBatchCoupling.bank i by rw [replicaRecoveryBatchCoupling_bank]; rfl)
  · exact congrArg S.R (show replicaRecoveryBoundaryFactoryReg (Fin.castLE (by decide : 168 ≤ 242) i) =
        replicaRecoveryBatchCoupling.bank i by rw [replicaRecoveryBatchCoupling_bank]; rfl)

theorem ReplicaBoundaryFactorData.initial_native_bank (H : ReplicaHaloProblem s) (target : ℕ)
    (columns : List (ZMod s → GaussianInt)) {S : Stacks 392 A}
    (h : ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg S))
    (hwork : ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg S)) :
    embStk weightCacheCoreReg (embStk replicaRecoveryBatchInterior.solver S) = releasedCellBank [] [] [] S.inp S.out := by
  rw [←replicaRecoveryBatchCoupling.native_view S,←replicaRecoveryBoundaryFactory_runtime_view]
  change embStk (Fin.castLE (by decide : 117 ≤ 242)) (embStk replicaRecoveryBoundaryFactoryReg S) = _
  refine Stacks.ext rfl rfl ?_ ?_ <;> funext i
  · exact h.bank.workspace.left_low ⟨i.val,by have := i.isLt; omega⟩
  · have hz : (releasedCellBank (A := A) [] [] [] S.inp S.out).R i = [] := by simp [releasedCellBank]
    exact (hwork.native i).trans hz.symm

theorem ReplicaFactoryWorkspace.coupling_fresh {S : Stacks 392 A}
    (h : ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg S)) :
    ∀ k ∈ ([(127 : Fin 168),135,139,140,143,158,166,167]), S.R (replicaRecoveryBatchCoupling.bank k) = [] := by
  intro k hk
  have hR : (embStk replicaRecoveryBoundaryFactoryReg S).R (Fin.castLE (by decide : 168 ≤ 242) k) =
      S.R (replicaRecoveryBatchCoupling.bank k) :=
    congrFun (congrArg Stacks.R (replicaRecoveryBoundaryFactory_runtime_view S)) k
  rw [←hR]
  apply h.scratch
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hk
  rcases hk with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> simp [replicaFactoryScratchPorts]

noncomputable def placedGeneratedReplicaBoundaryFactory (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 392 Q A U :=
  embProg (Fin.castLE (by decide : 389 ≤ 392)) Empty.elim (generatedReplicaBoundaryFactory (P := Empty) hR hQ)

theorem placedGeneratedReplicaBoundaryFactory_exec (H : ReplicaHaloProblem s) (target : ℕ)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (buffers : ReplicaLoopBuffers A) (v : HS 392 Q A U) (S : Stacks 392 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryBatchInterior.gather buffers S)
    (h119 : S.R 119 = []) (hblank : ∀ i, S.R (replicaRecoveryBoundaryFactoryReg i) = [])
    (hleft : ∀ i, S.L (replicaRecoveryBoundaryFactoryReg i) = []) :
    ∃ v' F n, ∃ columns : List (ZMod s → GaussianInt), v'.user = v.user ∧
      n ≤ generatedReplicaBoundaryFactoryCost H target ∧
      Exec body (placedGeneratedReplicaBoundaryFactory hR hQ) (mk v S) n (mk v' F) ∧
      ReplicaBoundaryFactorData H target columns (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band H.origin (H.origin+H.span)
        (embStk replicaRecoveryBatchCoupling.bank F) ∧
      (F.R (replicaRecoveryBatchCoupling.bank 118)).length = H.stage+1 ∧
      (F.R (replicaRecoveryBatchCoupling.bank 120)).length = H.l ∧
      (∀ k ∈ replicaFactoryGeometryPorts, F.R (replicaRecoveryBatchCoupling.bank k) = []) ∧
      embStk replicaRecoveryBatchInterior.gather F = embStk replicaRecoveryBatchInterior.gather S ∧
      F.inp = S.inp ∧ F.out = S.out ∧
      (∀ k, (∀ i, replicaRecoveryBoundaryFactoryReg i ≠ k) → F.L k = S.L k ∧ F.R k = S.R k) ∧
      ReplicaFactoryWorkspace (embStk replicaRecoveryBoundaryFactoryReg F) ∧
      (F.R (replicaRecoveryBoundaryFactoryReg 159) = [] ∧ F.R (replicaRecoveryBoundaryFactoryReg 161) = []) := by
  let e := Fin.castLE (by decide : 389 ≤ 392)
  have hgather (B : Stacks 392 A) : embStk replicaRecoveryBatchInterior.gather B =
      embStk replicaRecoveryCallerInterior.gather (embStk e B) := rfl
  have hreg (i : Fin 242) : replicaRecoveryBoundaryFactoryReg i = e (replicaRecoveryCallerFactoryReg i) :=
    replicaRecoveryBoundaryFactoryReg_reindex i
  obtain ⟨vi,G,n,columns,hu,hn,hex,hdata,hmasters,hstage,hlevel,hgeometry,hg,hin,hout,hoff,hwork,hmasks⟩ :=
    generatedReplicaBoundaryFactory_exec (body := fun f : Empty => nomatch f) H target hR hQ hA hp hwidth hpad htarget
      buffers (embDn e v) (embStk e S) (headers.of_gather_view (hgather S).symm) h119
      (by intro i; change S.R (e (replicaRecoveryCallerFactoryReg i)) = []; rw [←hreg]; exact hblank i)
      (by intro i; change S.L (e (replicaRecoveryCallerFactoryReg i)) = []; rw [←hreg]; exact hleft i)
  obtain ⟨v',hv,hu',hePlaced⟩ := exec_emb_ovr (body' := body) (ι := Empty.elim)
    (Fin.castLE_injective (by decide : 389 ≤ 392)) (fun f : Empty => nomatch f) hex v rfl S rfl
  let F := embOvr e G.get S
  have hview : embStk e F = G := embStk_ovr (Fin.castLE_injective _) G S
  have hfactory : embStk replicaRecoveryBoundaryFactoryReg F = embStk replicaRecoveryCallerFactoryReg G := by
    rw [replicaRecoveryBoundaryFactory_reindex_view,hview]
  have hbank : embStk replicaRecoveryBatchCoupling.bank F = embStk replicaRecoveryCallerCoupling.bank G := by
    rw [replicaRecoveryBatchCoupling_reindex_view,hview]
  have hbankR (i : Fin 168) : F.R (replicaRecoveryBatchCoupling.bank i) = G.R (replicaRecoveryCallerCoupling.bank i) :=
    congrFun (congrArg Stacks.R hbank) i
  refine ⟨v',F,n,columns,hu'.trans hu,hn,hePlaced,?_,?_,?_,?_,?_,?_,hin,hout,?_,?_,?_⟩
  · rw [hfactory]; exact hdata
  · rw [hbank]; exact hmasters
  · rw [hbankR 118]; exact hstage
  · rw [hbankR 120]; exact hlevel
  · intro k hk; rw [hbankR k]; exact hgeometry k hk
  · rw [hgather,hgather,hview]; exact hg
  · intro k hk
    by_cases hlow : k.val < 389
    · let j : Fin 389 := ⟨k.val,hlow⟩
      have hj : e j = k := Fin.ext rfl
      have ho : ∀ i, replicaRecoveryCallerFactoryReg i ≠ j := by
        intro i he
        apply hk i
        rw [replicaRecoveryBoundaryFactoryReg_reindex,he]
        exact hj
      have hL := congrFun (congrArg Stacks.L hview) j
      have hR := congrFun (congrArg Stacks.R hview) j
      rw [←hj]
      exact ⟨hL.trans (hoff j ho).1,hR.trans (hoff j ho).2⟩
    · exact embOvr_off G.get S (by intro j he; have hh := congrArg Fin.val he; change j.val = k.val at hh; have := j.isLt; omega)
  · rw [hfactory]; exact hwork
  · exact ⟨(congrArg (fun C : Stacks 242 A => C.R 159) hfactory).trans hmasks.1,
      (congrArg (fun C : Stacks 242 A => C.R 161) hfactory).trans hmasks.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
