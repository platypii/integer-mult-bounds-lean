module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellLiftedCyclicReplicaBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicBoundaryUnfoldLeft
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSolvedCyclicRecovery
public import IntegerMultBounds.MathlibTM2.Host.EmbedStockTrace

/-! Sequence the original cached caller's actual trace with solved-state
recovery in the extended bank. No extra blank private left stacks are assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
local notation "extendCaller" => CyclicRecoveryPlacement.extend
variable {s Q A : ℕ} [NeZero s] {P U : Type}

noncomputable def cachedCyclicReplicaRecovery (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  .seq (liftedCachedCyclicReplicaBatch hR hQ) (solvedCyclicRecovery hQ)

theorem cachedCyclicReplicaRecovery_exec (body : P → Pr P 117 Q A U)
    (H K : ReplicaHaloProblem s) (t band a n q w W : ℕ) (hst : s < t) (ha : a < s) (hn : n ≤ s)
    (hHt : H.t = t) (hHb : H.band = band) (hHL : H.origin = a)
    (hHN : H.span = min n (s-a)) (hHW : H.wordWidth = w)
    (hKt : K.t = t) (hKb : K.band = band) (hKL : K.origin = 0)
    (hKN : K.span = n-min n (s-a)) (hKW : K.wordWidth = w)
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hHF : H.Fs = Fs) (hKF : K.Fs = Fs) (hlen : solutions.length = Fs.length)
    (hsolutions : ∀ solution ∈ solutions,
      solution.length = (cyclicPrincipalBoundary s t band a n).card ∧ ∀ z ∈ solution, Fits w z)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (S S₁ S₂ producer F : Stacks 834 A)
    (Cs Ds : List (ZMod s → GaussianInt)) (v vf : HS 834 Q A U) (steps : ℕ)
    (hex : Exec (cyclicReplicaCallerBody body) (cachedCyclicReplicaBatch hR hQ) (mk v S) steps (mk vf F))
    (workspace : ℕ)
    (hwithin : ExecWithin (cyclicReplicaCallerBody body)
      (fun d z => mnSize z+d ≤ mnSize (mk v S)+0+workspace) 0
      (cachedCyclicReplicaBatch hR hQ) (mk v S) steps (mk vf F))
    (hu : vf.user = v.user)
    (postL : CachedReplicaPassPost H CyclicReplicaPlacement.left buffersL S₁ producer Cs)
    (postR : CachedReplicaPassPost K CyclicReplicaPlacement.right buffersR S₂ producer Ds)
    (hbankL : embStk CyclicReplicaPlacement.left.coupling.bank F = embStk CyclicReplicaPlacement.left.coupling.bank producer)
    (hbankR : embStk CyclicReplicaPlacement.right.coupling.bank F = embStk CyclicReplicaPlacement.right.coupling.bank producer)
    (headersL : ReplicaRecoveryRhsHeaders H CyclicReplicaPlacement.left.plan.gather buffersL F)
    (headersR : ReplicaRecoveryRhsHeaders K CyclicReplicaPlacement.right.plan.gather buffersR F)
    (solveTail : List (Fin (A+4)))
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk CyclicReplicaPlacement.factorReg F))
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk CyclicReplicaPlacement.factorReg F))) q w W (cyclicPrincipalBoundary s t band a n).card)
    (hsource : F.R (CyclicReplicaPlacement.factorReg 224) = solutions.flatMap (cstream A w)++solveTail)
    (projection : BoundaryProjectionFrame Fs.length (embStk CyclicReplicaPlacement.factorReg F))
    (z : HS 840 Q A U) (hz : embDn extendCaller z = v) :
    let B := cyclicPrincipalBoundary s t band a n
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let M := cyclicRecoveryMaskState H K (extendStacks (by decide : 834 ≤ 840) F)
    let G := prepareCyclicRecoveryCouplingState H K
      (placedNativeCyclicBoundaryBatchState M solveTail (solutions.reverse.flatMap fields))
    ∃ zf X m, zf.user = z.user ∧ m ≤ steps+solvedCyclicRecoveryCost H K Fs.length B.card n w ∧
      ExecWithin (embTab extendCaller (cyclicReplicaCallerBody body))
        (fun d state => mnSize state+d ≤ mnSize (mk z (extendStacks (by decide : 834 ≤ 840) S))+0+
          (workspace+solvedCyclicRecoveryWorkspace (A := A) (U := U) H K Fs.length B.card n w hQ)) 0
        (cachedCyclicReplicaRecovery hR hQ) (mk z (extendStacks (by decide : 834 ≤ 840) S)) m (mk zf X) ∧
      Exec (embTab extendCaller (cyclicReplicaCallerBody body)) (cachedCyclicReplicaRecovery hR hQ)
        (mk z (extendStacks (by decide : 834 ≤ 840) S)) m (mk zf X) ∧ X.R (recoveryBank 228) = [] ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR rows [] (M.R (recoveryBank 132))
        (M.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93)) (M.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93))
        buffersL.rhsTail buffersR.rhsTail (S₁.R (CyclicReplicaPlacement.left.coupling.bank 138))
        (S₂.R (CyclicReplicaPlacement.right.coupling.bank 138)) G X := by
  dsimp only
  obtain ⟨zi,_,hui,hei⟩ := cachedCyclicReplicaBatch_exec_lift body hR hQ v vf S F steps hex z hz
  obtain ⟨stateL,stateR⟩ := liftedCyclicRecoveryCallerReady H K buffersL buffersR S₁ S₂ producer F Cs Ds
    postL postR hbankL hbankR headersL headersR
  have hview := CyclicRecoveryPlacement.bank_old_view (extendStacks (by decide : 834 ≤ 840) F)
  simp only [CyclicRecoveryPlacement.extend,embStk_extendStacks] at hview
  have hread (i : Fin 234) : (extendStacks (by decide : 834 ≤ 840) F).R
      (recoveryBank (Fin.castLE (by decide : 234 ≤ 240) i)) = F.R (CyclicReplicaPlacement.factorReg i) :=
    congrArg (fun T : Stacks 234 A => T.R i) hview
  obtain ⟨zf,X,m,hu',hm,he,hclockX,hcursor⟩ := solvedCyclicRecovery_exec
    (body := embTab extendCaller (cyclicReplicaCallerBody body)) H K t band a n q w W hst ha hn
    hHt hHb hHL hHN hHW hKt hKb hKL hKN hKW solutions Fs hHF hKF hlen hsolutions hQ hA hsepL hsepR
    buffersL buffersR (S₁.R (CyclicReplicaPlacement.left.coupling.bank 138))
    (S₂.R (CyclicReplicaPlacement.right.coupling.bank 138)) zi (extendStacks (by decide : 834 ≤ 840) F) solveTail
    stateL stateR
    (by simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using hwork)
    (by simpa only [CyclicRecoveryPlacement.extend,embStk_extendStacks] using hready)
    (extendedCyclicBoundaryUnfold_left F projection.left)
    ((hread 224).trans hsource)
    (by intro i hi
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
        rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl
        · exact (hread 231).trans (projection.fresh 231 (by simp))
        · exact (hread 232).trans (projection.fresh 232 (by simp))
        · exact (hread 233).trans (projection.fresh 233 (by simp))
        all_goals exact (extendStacks_fresh (by decide : 834 ≤ 840) F _ (by decide)).2)
    ((congrArg List.length (hread 229)).trans projection.replicas)
    ((hread 228).trans (projection.fresh 228 (by simp))) ((hread 227).trans (projection.fresh 227 (by simp)))
    (extendStacks_fresh (by decide : 834 ≤ 840) F _ (by decide)).2
    (extendStacks_fresh (by decide : 834 ≤ 840) F _ (by decide)).2
  have hprefix := exec_emb_within_stock_of_exec (Fin.castLE_injective _) (ι := id)
    (body := cyclicReplicaCallerBody body) (body' := embTab extendCaller (cyclicReplicaCallerBody body))
    (by intro f; rfl) hwithin z hz (extendStacks (by decide : 834 ≤ 840) S)
    (embStk_extendStacks (by decide : 834 ≤ 840) S) hei
  have hwhole := execWithin_seq_two_budget (embTab extendCaller (cyclicReplicaCallerBody body))
    _ _ _ _ _ _ _ 0 _ _ hprefix he
  have hzUser : v.user = z.user := by rw [← hz]; rfl
  exact ⟨zf,X,steps+m,hu'.trans (hui.trans (hu.trans hzUser)),Nat.add_le_add_left hm _,hwhole,Exec.seq hei he.toExec,hclockX,hcursor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
