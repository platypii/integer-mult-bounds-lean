module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaInteriorRecovery
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaFast

/-! Execute the entire interior/coupling/recovery caller from physical input
headers. The initialized interior trace is constructed, rather than assumed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Cost
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.SchurDominance
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {s Q A : ℕ} [NeZero s] {P U : Type} {body : P → Pr P 389 Q A U}

def initializedReplicaInteriorRecoveryCost (H : ReplicaHaloProblem s) (target : ℕ) :=
  initializedReplicaHaloTime H+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)+
    reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)+coupledReplicaRecoveryCallerCost H target

theorem initializedReplicaInteriorRecovery_exec (H : ReplicaHaloProblem s)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A) (hp : 2 ≤ H.p) (hwidth : 8*H.p ≤ 2^H.u)
    (hspan : H.span+H.band ≤ s) (horigin : H.origin < s)
    (hpad : 2*((s/(H.t-s)+1)-2*H.band) ≤ 2^H.l+1)
    (target : ℕ) (columns : List (ZMod s → GaussianInt))
    (htarget : H.target = boundaryHaloTarget H.p H.u (boundaryRecoveryTarget H.p target) H.rhsExp
      (haloBoundary s H.t H.band H.origin (H.origin+H.span)).card)
    (X : ℕ → ZMod s → ℝ)
    (hX : ∀ r < H.Fs.length, Solves (realMatrix s H.t H.p H.u) (haloVertices s H.origin (H.origin+H.span)) (X r)
      (fun i => (value H.precision (H.Fs.reverse.getD (H.Fs.length-1-r) (fun _ => 0) i)).re))
    (buffers : ReplicaLoopBuffers A) (v : HS 389 Q A U) (S : Stacks 389 A)
    (headers : ReplicaLoopHeaders H replicaRecoveryCallerInterior.gather buffers S)
    (hbank : embStk weightCacheCoreReg (embStk replicaRecoveryCallerInterior.solver S) =
      releasedCellBank [] buffers.rhsTail buffers.solverOutputTail S.inp S.out)
    (hcache : S.R (replicaRecoveryCallerInterior.solver 117) = buffers.cacheTail)
    (hsolverFresh : ∀ k ∈ [(118 : Fin 121),119,120], S.R (replicaRecoveryCallerInterior.solver k) = [])
    (hinput : S.inp = buffers.input) (houtput : S.out = buffers.output)
    (hsaved : embStk replicaRecoveryCallerInterior.gather S = buffers.savedGather)
    (hkeys : S.R (replicaRecoveryCallerInterior.gather 87) = buffers.keyTail)
    (hdst : S.R 247 = buffers.accumulatorTail)
    (h86 : S.R (replicaRecoveryCallerInterior.gather 86) = [])
    (h119 : S.R (replicaRecoveryCallerInterior.gather 119) = [])
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
    ∃ v' G m, v'.user = v.user ∧ m ≤ initializedReplicaInteriorRecoveryCost H target ∧
      Exec body (initializedReplicaInteriorRecovery hR hQ) (mk v S) m (mk v' G) ∧
      G.R 387 = [] ∧ (G.R 121).length = H.Fs.length ∧ G.R 125 = [] ∧ G.R 388 = [] ∧
      RecoveredReplicaArchive H target X ((embStk replicaRecoveryCallerReg S).R 125)
        (embStk replicaRecoveryCallerWorkerReg G) ∧
      ReplicaRecoveryCoreReady H (12*H.band+1) (embStk replicaRecoveryCallerNativeReg G) ∧
      ReplicaBoundaryRhsReady H (embStk replicaBoundaryPhaseReg (embStk replicaRecoveryCallerWorkerReg G)) ∧
      ReplicaBoundaryFactorData H target columns
        (embStk packedBoundaryRecoveryBase (embStk replicaRecoveryCallerNativeReg G)) := by
  have hgd (k : Fin 126) : replicaRecoveryCallerInterior.gather k ≠ (247 : Fin 389) := by
    intro he
    have hv := congrArg (fun k : Fin 389 => k.val) he
    change k.val = 247 at hv
    have hk := k.isLt
    omega
  have hsd (k : Fin 121) : replicaRecoveryCallerInterior.solver k ≠ (247 : Fin 389) := by
    intro he
    have hv := congrArg (fun k : Fin 389 => k.val) he
    change 126+k.val = 247 at hv
    have hk := k.isLt
    omega
  obtain ⟨v₀,F,n,hu₀,hn,hloop,he⟩ :=
    initializedReplicaHaloLoop_exec_within (body := body) H replicaRecoveryCallerInterior 247 hgd hsd
      hR hQ hA hpad _ _ (Nat.le_refl _) (Nat.le_refl _) buffers v S headers hbank hcache
      hsolverFresh hinput houtput hsaved hkeys hdst h86 h119 0
  have hn' : n ≤ initializedReplicaHaloTime H := hn
  obtain ⟨v',G,m,hu,hm,hex,h387,h121,h125,h388,harchive,hcore,hphysical,hfactorG⟩ :=
    initializedReplicaInteriorRecovery_finish (body := body) H hR hQ hA hp hwidth hspan horigin hpad
      target columns htarget X hX buffers v v₀ S F n 0 _ hu₀ he hloop hfactor hmasters hstage hlevel
      hblank hfresh hpage hclean hmaskLeft hprivateLeft hprivate hqueue hcontroller
  refine ⟨v',G,m,hu,?_,hex,h387,h121,h125,h388,harchive,hcore,hphysical,hfactorG⟩
  unfold initializedReplicaInteriorRecoveryCost
  omega

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
