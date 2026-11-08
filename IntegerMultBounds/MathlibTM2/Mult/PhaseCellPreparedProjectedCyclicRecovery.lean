module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellProjectedCyclicRecoveryInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryCouplingBatch

/-! Preparation and the complete paired coupling traversal start at the actual
projected-boundary endpoint. Aligned queues and Fits come from that endpoint. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

noncomputable def preparedProjectedCyclicRecovery (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  .seq prepareCyclicRecoveryCoupling (cyclicRecoveryCouplingBatch hQ)

def preparedProjectedCyclicRecoveryCost (H K : ReplicaHaloProblem s) (replicas : ℕ) : ℕ :=
  (replicaRecoveryPreparationCost H+replicaRecoveryPreparationCost K)+
    ((4*replicas+4)+(replicas*(cyclicRecoveryCouplingPieceCost H+cyclicRecoveryCouplingPieceCost K+3)+2))

noncomputable def preparedProjectedCyclicRecoveryWorkspace (H K : ReplicaHaloProblem s) (replicas : ℕ)
    (hQ : SS.states ≤ Q) : ℕ :=
  (replicaRecoveryPreparationWorkspace (Q := Q) (A := A) (U := U) H+
    replicaRecoveryPreparationWorkspace (Q := Q) (A := A) (U := U) K)+
    (2*(4*replicas+4)+(cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) H hQ+
      cyclicRecoveryCouplingPieceWorkspace (A := A) (U := U) K hQ))

theorem preparedProjectedCyclicRecovery_exec_within (H K : ReplicaHaloProblem s)
    (t band a n w : ℕ)
    (hHL : H.origin = a) (hHN : H.span = min n (s-a)) (hHW : H.wordWidth = w)
    (hKL : K.origin = 0) (hKN : K.span = n-min n (s-a)) (hKW : K.wordWidth = w)
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hHF : H.Fs = Fs) (hKF : K.Fs = Fs) (hlen : solutions.length = Fs.length)
    (hsolutions : ∀ solution ∈ solutions,
      solution.length = (cyclicPrincipalBoundary s t band a n).card ∧ ∀ z ∈ solution, Fits w z)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (pageL pageR : List (Fin (A+4)))
    (S : Stacks 840 A) (solveTail : List (Fin (A+4)))
    (v : HS 840 Q A U) (depth : ℕ)
    (hmaster : (S.R (recoveryBank 229)).length = Fs.length)
    (hclock : S.R (recoveryBank 228) = []) (htmp : S.R (recoveryBank 227) = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let F := placedNativeCyclicBoundaryBatchState S solveTail (solutions.reverse.flatMap fields)
    let G := prepareCyclicRecoveryCouplingState H K F
    RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL F →
    RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR F →
    ∃ vf X m, vf.user = v.user ∧ m ≤ preparedProjectedCyclicRecoveryCost H K Fs.length ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v F)+depth+
        preparedProjectedCyclicRecoveryWorkspace (A := A) (U := U) H K Fs.length hQ)
        depth (preparedProjectedCyclicRecovery hQ) (mk v F) m (mk vf X) ∧ X.R (recoveryBank 228) = [] ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR rows [] (S.R (recoveryBank 132))
        (S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93)) (S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93))
        buffersL.rhsTail buffersR.rhsTail pageL
        pageR G X := by
  dsimp only
  intro stateL stateR
  let B := cyclicPrincipalBoundary s t band a n
  let rows := cyclicBoundaryRecoveryRows B solutions Fs
  let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
    cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  let F := placedNativeCyclicBoundaryBatchState S solveTail (solutions.reverse.flatMap fields)
  let G := prepareCyclicRecoveryCouplingState H K F
  obtain ⟨vi,mi,hu₁,hm₁,he₁,hhL,hhR,hcL,hcR⟩ := prepareCyclicRecoveryCoupling_exec_within (body := body)
    H K buffersL buffersR pageL pageR F stateL stateR v depth
  obtain ⟨hsource,hrhsL,hrhsR,hrows,hfitL,hfitR⟩ := projectedCyclicRecoveryInputs H K t band a n w
    hHL hHN hHW hKL hKN hKW solutions Fs hHF hKF hlen hsolutions S solveTail
  have hrowsCount : rows.length = Fs.length := hrows
  have hnative (i : Fin 240) (h132 : i ≠ 132) (h224 : i ≠ 224) : G.R (recoveryBank i) = S.R (recoveryBank i) := by
    dsimp only [G]
    rw [prepareCyclicRecoveryCouplingState_native H K F i]
    simp only [F,placedNativeCyclicBoundaryBatchState,
      Function.update_of_ne (CyclicRecoveryPlacement.bank_injective.ne h224),
      Function.update_of_ne (CyclicRecoveryPlacement.bank_injective.ne h132)]
  obtain ⟨vf,X,mf,hu₂,hm₂,he₂,hclockX,hcursor⟩ := cyclicRecoveryCouplingBatch_exec_within (body := body)
    H K hQ hA hsepL hsepR buffersL buffersR rows hfitL hfitR
    (S.R (recoveryBank 132)) (S.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93))
    (S.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93)) buffersL.rhsTail buffersR.rhsTail
    pageL pageR
    vi G hhL hhR hcL hcR hsource hrhsL hrhsR
    (by rw [hnative 229 (by decide) (by decide),hmaster,hrowsCount])
    (by rw [hnative 228 (by decide) (by decide)]; exact hclock)
    (by rw [hnative 227 (by decide) (by decide)]; exact htmp)
  refine ⟨vf,X,mi+mf,hu₂.trans hu₁,?_,?_,hclockX,hcursor⟩
  · simpa only [hrowsCount,preparedProjectedCyclicRecoveryCost] using Nat.add_le_add hm₁ hm₂
  · have hbatch := he₂ depth
    rw [hrowsCount] at hbatch
    exact execWithin_seq_two_budget body _ _ _ _ _ _ _ depth _ _ he₁ hbatch

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
