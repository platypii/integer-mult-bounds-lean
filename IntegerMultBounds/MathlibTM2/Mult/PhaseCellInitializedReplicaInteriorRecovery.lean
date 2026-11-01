module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoupledReplicaRecoveryCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaCouplingRows
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaInteriorRecoveryFrame

/-! Finish actual initialized interior execution with real rows, shared coupling
and complete recovery. Retained factor data is transported from the initial bank. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

noncomputable def initializedReplicaInteriorRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 389 Q A U :=
  .seq (initializedReplicaCouplingRows replicaRecoveryCallerInterior 247 248 hR hQ)
    (coupledReplicaRecoveryCaller hR hQ)

theorem initializedReplicaInteriorRecovery_finish (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target : ℕ) (columns : List (ZMod s → GaussianInt))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re))
    (buffers : ReplicaLoopBuffers A) (v v₀ : HS 389 Q A U) (S F : Stacks 389 A)
    (n depth W : ℕ) (hu₀ : v₀.user = v.user)
    (he₀ : ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+W) depth
      (initializedReplicaHaloLoop replicaRecoveryCallerInterior 247 hR hQ) (mk v S) n (mk v₀ F))
    (h : ReplicaHaloLoopState H replicaRecoveryCallerInterior 247 buffers
      (haloLengthKeys s H.t H.band H.origin (H.origin+H.span)) [] F)
    (hfactor : ReplicaBoundaryFactorData H target columns
      (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg S)))
    (hmasters : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) (embStk replicaRecoveryCallerCoupling.bank S))
    (hstage : (S.R (replicaRecoveryCallerCoupling.bank 118)).length = H.stage+1)
    (hlevel : (S.R (replicaRecoveryCallerCoupling.bank 120)).length = H.l)
    (hblank : ∀ k ∈ ([(145 : Fin 168),146,147,148,149,151,154,155,156,157,163,164,165]),
      S.R (replicaRecoveryCallerCoupling.bank k) = [])
    (hfresh : ∀ k ∈ [(127 : Fin 168),135,139,140,143,158,166,167],
      S.R (replicaRecoveryCallerCoupling.bank k) = [])
    (hpage : S.R (replicaRecoveryCallerCoupling.bank 138) = [])
    (hclean : ∀ k ∈ ([129,131,133,134,136,153] : List (Fin 242)),
      (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg S)).R k = [])
    (hmaskLeft : S.L (replicaRecoveryCallerWorkerReg 167) = [])
    (hprivateLeft : ∀ k : Fin 255, 242 ≤ k.val → S.L (replicaRecoveryCallerWorkerReg k) = [])
    (hprivate : ∀ k : Fin 255, 242 ≤ k.val → S.R (replicaRecoveryCallerWorkerReg k) = [])
    (hqueue : S.R 388 = []) (hcontroller : S.R 387 = []) :
    ∃ v' G m, v'.user = v.user ∧ m ≤ n+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+
      reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+coupledReplicaRecoveryCallerCost H target ∧
      Exec body (initializedReplicaInteriorRecovery hR hQ) (mk v S) m (mk v' G) ∧
      G.R 387 = [] ∧ (G.R 121).length = H.Fs.length ∧ G.R 125 = [] ∧ G.R 388 = [] ∧
      RecoveredReplicaArchive H target X ((embStk replicaRecoveryCallerReg S).R 125)
        (embStk replicaRecoveryCallerWorkerReg G) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk replicaRecoveryCallerNativeReg G) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoveryCallerWorkerReg G)) ∧
      ReplicaBoundaryFactorData H target columns
        (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg G)) := by
  have houtput (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ (247 : Fin 389) := by
    intro he; have hv := congrArg (fun k : Fin 389 => k.val) he
    change k.val = 247 at hv
    have hk := k.isLt
    omega
  have hrhs (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ (248 : Fin 389) := by
    intro he; have hv := congrArg (fun k : Fin 389 => k.val) he
    change k.val = 248 at hv
    have hk := k.isLt
    omega
  obtain ⟨v₁,J,n₁,hu₁,hn₁,he₁,hcursor,hgather,hL,hinp,hout,hframe⟩ :=
    initializedReplicaCouplingRows_finish (body := body) H replicaRecoveryCallerInterior 247 248
      houtput hrhs (by decide) hR hQ (by omega : 4 ≤ A) buffers v v₀ S F n depth W hu₀ he₀ h (H.dominates hp hwidth)
  have hworker : embStk replicaRecoveryCallerWorkerReg J = embStk replicaRecoveryCallerWorkerReg F := by
    refine Stacks.ext hinp hout (congrArg (fun L => L ∘ replicaRecoveryCallerWorkerReg) hL) ?_
    funext k
    exact hframe _ (replicaRecoveryCallerReg_outputs_disjoint _).1 (replicaRecoveryCallerReg_outputs_disjoint _).2
  have hnativeF := h.bank
  rw [replicaRecoveryCallerCoupling_native_view] at hnativeF
  have hnativeLeft (i : Fin 117) : F.L (replicaRecoveryCallerWorkerReg (Fin.castLE (by decide) i)) = [] :=
    congrArg (fun B : Stacks 117 A => B.L i) hnativeF
  have hworkerLF : (embStk replicaRecoveryCallerWorkerReg F).L =
      (embStk replicaRecoveryCallerWorkerReg S).L := by
    funext k
    by_cases hk : k.val < 117
    · exact (hnativeLeft ⟨k.val,hk⟩).trans
        (hfactor.bank.workspace.left_low ⟨k.val,by omega⟩).symm
    · exact (initializedReplicaHaloLoop_recovery_frame hR hQ he₀.toExec k (by omega)).1
  have hworkerLJ : (embStk replicaRecoveryCallerWorkerReg J).L =
      (embStk replicaRecoveryCallerWorkerReg S).L := by
    rw [hworker]
    exact hworkerLF
  have hhigh (k : Fin 255) (hk : 117 ≤ k.val) :
      J.R (replicaRecoveryCallerWorkerReg k) = S.R (replicaRecoveryCallerWorkerReg k) := by
    exact (congrArg (fun B : Stacks 255 A => B.R k) hworker).trans
      (initializedReplicaHaloLoop_recovery_frame hR hQ he₀.toExec k hk).2
  have hshared (k : Fin 168) (hk : 117 ≤ k.val) :
      J.R (replicaRecoveryCallerCoupling.bank k) = S.R (replicaRecoveryCallerCoupling.bank k) := by
    simp only [replicaRecoveryCallerCoupling_bank]
    exact hhigh (Fin.castLE (by decide) k) hk
  have hfactorJ : ReplicaBoundaryFactorData H target columns
      (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg J)) := by
    apply hfactor.of_recovery_frame H target columns
    · exact congrArg (fun L => L ∘ (Fin.castLE (by decide : 242 ≤ 255))) hworkerLJ
    · intro i
      have hh := congrArg (fun B : Stacks 117 A => B.R (Fin.castLE (by decide) i)) hnativeF
      have hf := congrArg (fun B : Stacks 255 A => B.R (Fin.castLE (by decide) i)) hworker
      have h93 : i.val ≠ 93 := by have hi := i.isLt; omega
      have h110 : i.val ≠ 110 := by have hi := i.isLt; omega
      apply hf.trans
      simp only [releasedCellBank,Fin.val_castLE,if_neg h93,if_neg h110] at hh
      exact hh
    · exact hhigh 119 (by decide)
    · intro k hk h238
      exact hhigh (Fin.castLE (by decide) k) (by change 117 ≤ k.val; omega)
  have hmastersJ : CouplingMasterHeaders (2^15*H.p) H.precision H.wordWidth s H.t H.u H.band
      H.origin (H.origin+H.span) (embStk replicaRecoveryCallerCoupling.bank J) := by
    apply hmasters.of_frame
    intro k hk
    apply hshared
    simp only [couplingMasterPorts,List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
    norm_num at hk
    omega
  have hheadersJ : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers J := by
    apply h.headers.of_frame
    intro k _ _
    exact congrArg (fun B : Stacks 126 A => B.R k) hgather
  have hnativeJ : embStk weightCacheCoreReg (embStk replicaRecoveryCallerInterior.solver J) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail J.inp J.out := by
    rw [replicaRecoveryCallerCoupling_native_view]
    have hw : embStk replicaRecoveryCallerNativeReg J = embStk replicaRecoveryCallerNativeReg F :=
      congrArg (embStk (Fin.castLE (by decide : 248 ≤ 255))) hworker
    rw [hw,hnativeF,hinp,hout]
  obtain ⟨v',G,n₂,hu₂,hn₂,he₂,h387,h121,h125,h388,harchive,hcore,hphysical,hfactorG⟩ :=
    coupledReplicaRecoveryCaller_exec (body := body) H hR hQ hA hp hwidth hspan horigin hpad target columns
      htarget X hX buffers.accumulatorTail (F.R 248) buffers.rhsTail buffers.solverOutputTail buffers v₁ J
      hcursor hheadersJ hnativeJ hfactorJ hmastersJ
      (by rw [hshared 118 (by decide)]; exact hstage)
      (by rw [hshared 120 (by decide)]; exact hlevel)
      (by
        intro k hk
        rw [hshared k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
          norm_num at hk
          omega)]
        exact hblank k hk)
      (by
        intro k hk
        rw [hshared k (by
          simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
          norm_num at hk
          omega)]
        exact hfresh k hk)
      ((hshared 138 (by decide)).trans hpage)
      (by
        intro k hk
        have hb : 117 ≤ k.val := by
          simp only [List.mem_cons,List.not_mem_nil,or_false,Fin.ext_iff] at hk
          norm_num at hk
          omega
        exact (hhigh (Fin.castLE (by decide) k) hb).trans (hclean k hk))
      ((congrFun hworkerLJ 167).trans hmaskLeft)
      (by intro k hk; exact (congrFun hworkerLJ k).trans (hprivateLeft k hk))
      (by intro k hk; exact (hhigh k (by omega)).trans (hprivate k hk))
      ((hframe 388 (by decide) (by decide)).trans
        ((initializedReplicaHaloLoop_recovery_frame_at hR hQ he₀.toExec 388 (by decide)).2.trans hqueue))
      ((hframe 387 (by decide) (by decide)).trans
        ((initializedReplicaHaloLoop_recovery_frame_at hR hQ he₀.toExec 387 (by decide)).2.trans hcontroller))
  refine ⟨v',G,n₁+n₂,hu₂.trans hu₁,by omega,Exec.seq he₁.toExec he₂,h387,?_,h125,h388,?_,hcore,hphysical,hfactorG⟩
  · rw [h121]
    exact (hheadersJ.recovery_rhs H _ buffers J).count
  · have ht := hshared 125 (by decide)
    simp only [replicaRecoveryCallerCoupling_right] at ht
    change (embStk replicaRecoveryCallerReg J).R 125 = (embStk replicaRecoveryCallerReg S).R 125 at ht
    rw [ht] at harchive
    exact harchive

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
