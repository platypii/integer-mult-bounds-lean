module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryReadyTransport
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedProjectedCyclicRecovery

/-! Recover all RHS rows from a solved joint boundary batch. Native mask setup,
projection and retained coupling execute in source order with complete time bills. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "recoveryBank" => CyclicRecoveryPlacement.bank
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 840 Q A U}

noncomputable def solvedCyclicRecovery (hQ : SS.states ≤ Q) : Pr P 840 Q A U :=
  .seq cyclicRecoveryMasks (.seq placedNativeCyclicBoundaryBatch (preparedProjectedCyclicRecovery hQ))

def solvedCyclicRecoveryCost (H K : ReplicaHaloProblem s) (replicas N n w : ℕ) : ℕ :=
  (placedReplicaBoundaryMaskCost H+placedReplicaBoundaryMaskCost K)+
    (nativeCyclicBoundaryBatchCost replicas N n w+preparedProjectedCyclicRecoveryCost H K replicas)

theorem solvedCyclicRecovery_exec (H K : ReplicaHaloProblem s)
    (t band a n q w W : ℕ) (hst : s < t) (ha : a < s) (hn : n ≤ s)
    (hHt : H.t = t) (hHb : H.band = band) (hHL : H.origin = a)
    (hHN : H.span = min n (s-a)) (hHW : H.wordWidth = w)
    (hKt : K.t = t) (hKb : K.band = band) (hKL : K.origin = 0)
    (hKN : K.span = n-min n (s-a)) (hKW : K.wordWidth = w)
    (solutions : List (List GaussianInt)) (Fs : List (ZMod s → GaussianInt))
    (hHF : H.Fs = Fs) (hKF : K.Fs = Fs) (hlen : solutions.length = Fs.length)
    (hsolutions : ∀ solution ∈ solutions,
      solution.length = (cyclicPrincipalBoundary s t band a n).card ∧ ∀ z ∈ solution, Fits w z)
    (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hsepL : H.span+H.band ≤ s) (hsepR : K.span+K.band ≤ s)
    (buffersL buffersR : ReplicaLoopBuffers A) (pageL pageR : List (Fin (A+4)))
    (v : HS 840 Q A U) (S : Stacks 840 A) (solveTail : List (Fin (A+4)))
    (stateL : RetainedReplicaRecoveryReady H CyclicRecoveryPlacement.leftJob buffersL pageL S)
    (stateR : RetainedReplicaRecoveryReady K CyclicRecoveryPlacement.rightJob buffersR pageR S)
    (hwork : NativeBoundaryUnfoldWorkspace (cyclicPrincipalBoundary s t band a n).card
      (embStk CyclicReplicaPlacement.factorReg (embStk CyclicRecoveryPlacement.extend S)))
    (hready : BoundarySolveReady (boundaryFactorState (embStk (Fin.castLE (by decide : 224 ≤ 234))
      (embStk CyclicReplicaPlacement.factorReg (embStk CyclicRecoveryPlacement.extend S))))
      q w W (cyclicPrincipalBoundary s t band a n).card)
    (hleft : ∀ i : Fin 224, S.L (recoveryBank (sharedPageBoundaryUnfoldReg i)) = [])
    (hsource : S.R (recoveryBank 224) = solutions.flatMap (cstream A w)++solveTail)
    (hfresh : ∀ i ∈ [(231 : Fin 240),232,233,234,235,236,237], S.R (recoveryBank i) = [])
    (hmaster : (S.R (recoveryBank 229)).length = Fs.length)
    (hclock : S.R (recoveryBank 228) = []) (htmp : S.R (recoveryBank 227) = [])
    (h239 : S.R (recoveryBank 239) = []) (h238 : S.R (recoveryBank 238) = []) :
    let B := cyclicPrincipalBoundary s t band a n
    let rows := cyclicBoundaryRecoveryRows B solutions Fs
    let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
      cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
    let M := cyclicRecoveryMaskState H K S
    let G := prepareCyclicRecoveryCouplingState H K
      (placedNativeCyclicBoundaryBatchState M solveTail (solutions.reverse.flatMap fields))
    ∃ vf X m, vf.user = v.user ∧ m ≤ solvedCyclicRecoveryCost H K Fs.length B.card n w ∧
      Exec body (solvedCyclicRecovery hQ) (mk v S) m (mk vf X) ∧ X.R (recoveryBank 228) = [] ∧
      CyclicRecoveryCouplingCursor H K buffersL buffersR rows [] (M.R (recoveryBank 132))
        (M.R (CyclicRecoveryPlacement.leftJob.coupling.bank 93)) (M.R (CyclicRecoveryPlacement.rightJob.coupling.bank 93))
        buffersL.rhsTail buffersR.rhsTail pageL pageR G X := by
  dsimp only
  let B := cyclicPrincipalBoundary s t band a n
  let fields := fun solution => cstream A w (packedInterval a (min n (s-a)) (boundarySolutionField B solution))++
    cstream A w (packedInterval 0 (n-min n (s-a)) (boundarySolutionField B solution))
  let M := cyclicRecoveryMaskState H K S
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁,hwM,hrM,_⟩ := cyclicRecoveryMasks_ready_exec (body := body)
    H K buffersL buffersR pageL pageR v S stateL stateR h239 h238 hwork hready
  obtain ⟨stateLM,stateRM⟩ := cyclicRecoveryMaskState_recoveryReady H K buffersL buffersR pageL pageR S stateL stateR
  have hread (i : Fin 240) (hi : i.val < 238) : M.R (recoveryBank i) = S.R (recoveryBank i) := by
    apply cyclicRecoveryMaskState_bank_read
    · intro he; have hv := congrArg (fun k : Fin 240 => k.val) he; change i.val = 238 at hv; omega
    · intro he; have hv := congrArg (fun k : Fin 240 => k.val) he; change i.val = 239 at hv; omega
  have hmaskL := (cyclicRecoveryMaskState_values H K S).1
  have hmaskR := (cyclicRecoveryMaskState_values H K S).2
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂,_,_⟩ := placedNativeCyclicBoundaryBatch_exec (body := body)
    hst (by omega) band a n ha hn q w W solutions (fun row hr => (hsolutions row hr).1) v₁ M solveTail
    hwM hrM hleft (by rw [hread 224 (by decide)]; exact hsource)
    (by simpa only [hKt,hKb,hKL,hKN,Nat.zero_add] using hmaskR)
    (by simpa only [hHt,hHb,hHL,hHN] using hmaskL)
    (by intro i hi
        have hv : i.val < 238 := by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
          rcases hi with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
        rw [hread i hv]; exact hfresh i hi)
    (by rw [hread 229 (by decide),hmaster,hlen])
    (by rw [hread 227 (by decide)]; exact htmp) (by rw [hread 228 (by decide)]; exact hclock)
  obtain ⟨stateLP,stateRP⟩ := placedNativeCyclicBoundaryBatchState_recoveryReady H K buffersL buffersR pageL pageR
    M solveTail (solutions.reverse.flatMap fields) stateLM stateRM
  obtain ⟨vf,X,m₃,hu₃,hm₃,he₃,hclockX,hcursor⟩ := preparedProjectedCyclicRecovery_exec_within (body := body)
    H K t band a n w ha hn hHL hHN hHW hKL hKN hKW solutions Fs hHF hKF hlen hsolutions
    hQ hA hsepL hsepR buffersL buffersR pageL pageR M solveTail v₂ 0
    (by rw [hread 224 (by decide)]; exact hsource)
    (by rw [hread 229 (by decide)]; exact hmaster)
    (by rw [hread 228 (by decide)]; exact hclock) (by rw [hread 227 (by decide)]; exact htmp) stateLP stateRP
  have hmP : m₂ ≤ nativeCyclicBoundaryBatchCost Fs.length B.card n w := by simpa only [hlen] using hm₂
  exact ⟨vf,X,m₁+(m₂+m₃),hu₃.trans (hu₂.trans hu₁),Nat.add_le_add hm₁ (Nat.add_le_add hmP hm₃),
    Exec.seq he₁ (Exec.seq he₂.toExec he₃.toExec),hclockX,hcursor⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
