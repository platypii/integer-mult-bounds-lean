module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicReplicaRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicRecoveryReplicaInputs
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSecondInterior

/-! Ordinary original-RHS inputs execute through both second interior solves.
The computed joint boundary rows determine the actual recovery RHS problems. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
local notation "extendRecovery" => CyclicSecondInteriorPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def executedCyclicSecondInterior (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 842 Q A U :=
  .seq (embProg extendRecovery id (cachedCyclicReplicaRecovery hR hQ)) (cyclicSecondInterior hR hQ)

theorem executedCyclicSecondInterior_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let cellTarget := initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (buffersL buffersR : ReplicaLoopBuffers A) (v : HS 842 Q A U) (S : Stacks 834 A)
      (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H CyclicReplicaPlacement.left buffersL S →
    CachedReplicaPassInput K CyclicReplicaPlacement.right buffersR S →
    CyclicResidualBatchInput p l s t u target a n tail pageTail (embStk CyclicReplicaPlacement.factorReg S) →
    S.R (CyclicReplicaPlacement.factorReg 226) = [] → S.R (CyclicReplicaPlacement.factorReg 229) = [] →
    ∃ (solutions : List (List GaussianInt)) (J L : ReplicaHaloProblem s)
      (X : Stacks 840 A) (vf : HS 842 Q A U) (G : Stacks 842 A) (steps : ℕ)
      (savedL savedR : List (Fin (A+4))),
      let rows := cyclicBoundaryRecoveryRows B solutions Fs
      let E := extendStacks (by decide : 840 ≤ 842) X
      solutions.length = Fs.length ∧
      (∀ solution ∈ solutions, solution.length = B.card ∧ ∀ y ∈ solution, Fits w y) ∧
      CyclicBoundaryRowsAccurate p t u a n q target Fs solutions ∧
      H.SameLayout J ∧ K.SameLayout L ∧
      J.target = boundaryHaloRecoveryTarget p target B.card ∧ L.target = boundaryHaloRecoveryTarget p target B.card ∧
      J.rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u) ∧
      L.rhsExp = recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u) ∧
      J.Fs = rows.map (fun row => guardedCouplingRowField (2^15*H.p) H.precision H.t H.u H.band
        H.origin (H.origin+H.span) true row.1 row.2.1) ∧
      L.Fs = rows.map (fun row => guardedCouplingRowField (2^15*K.p) K.precision K.t K.u K.band
        K.origin (K.origin+K.span) true row.1 row.2.1) ∧
      vf.user = v.user ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n target q w B.card (24*band+1) Fs.length+
        solvedCyclicRecoveryCost H K Fs.length B.card n w+
        (releaseReplicaInteriorBankCost CyclicSecondInteriorPlacement.left.plan E+replicaRecoveryInteriorTime H J+
          (releaseReplicaInteriorBankCost CyclicSecondInteriorPlacement.right.plan E+replicaRecoveryInteriorTime K L)) ∧
      RealReplicaHaloOutput J CyclicSecondInteriorPlacement.left.output buffersL.accumulatorTail G ∧
      RealReplicaHaloOutput L CyclicSecondInteriorPlacement.right.output buffersR.accumulatorTail G ∧
      G.R (CyclicSecondInteriorPlacement.left.plan.gather 125) = rows.reverse.flatMap (fun row => cyclicRecoveryField H row.1)++savedL ∧
      G.R (CyclicSecondInteriorPlacement.right.plan.gather 125) = rows.reverse.flatMap (fun row => cyclicRecoveryField K row.1)++savedR ∧
      Exec (embTab extendRecovery (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))
        (executedCyclicSecondInterior hR hQ)
        (mk v (extendStacks (by decide : 840 ≤ 842) (extendStacks (by decide : 834 ≤ 840) S))) steps (mk vf G) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let cellTarget := initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  intro buffersL buffersR v S tail pageTail inputsL inputsR factory h226 h229
  obtain ⟨solutions,z,X,m,savedL,savedR,pageL,pageR,hlen,hformat,haccuracy,hmag,hu,hm,he,hclock,
    hsourceL,hsourceR,harchiveL,harchiveR,hcacheL,hcacheR,hheadersL,hheadersR,hreadyL,hreadyR⟩ :=
    executedCyclicReplicaRecovery_spec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom
      Fs hF buffersL buffersR (embDn extendRecovery v) S tail pageTail inputsL inputsR factory h226 h229
  have hfitL : a+min n (s-a) ≤ s := by omega
  have hfitR : 0+(n-min n (s-a)) ≤ s := by omega
  obtain ⟨J,layoutL,hJtarget,hJexp,hJFs,hJsource,_⟩ := cyclicRecoveryReplicaInputs (A := A)
    axis target a (min n (s-a)) hfitL B Fs hF solutions hlen hmag
  obtain ⟨L,layoutR,hLtarget,hLexp,hLFs,_,hLsource⟩ := cyclicRecoveryReplicaInputs (A := A)
    axis target 0 (n-min n (s-a)) hfitR B Fs hF solutions hlen hmag
  obtain ⟨zi,hzi,huser,helift⟩ := exec_extendStacks (by decide : 840 ≤ 842) (ι := id)
    (body' := embTab extendRecovery (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))
    (fun _ => rfl) he v rfl
  obtain ⟨vf,G,k,huf,hk,hfieldsL,hfieldsR,harchL,harchR,heSecond⟩ := cyclicSecondInterior_exec
    (body := embTab extendRecovery (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))
    H K J L layoutL layoutR hR hQ hA axis.hp axis.hpacket axis.hp axis.hpacket axis.hpad axis.hpad
    buffersL buffersR buffersL.rhsTail buffersR.rhsTail zi X hreadyL hreadyR
    (hsourceL.trans (congrArg (fun xs => xs++buffersL.rhsTail) hJsource.symm))
    (hsourceR.trans (congrArg (fun xs => xs++buffersR.rhsTail) hLsource.symm))
  exact ⟨solutions,J,L,X,vf,G,m+k,savedL,savedR,hlen,hformat,haccuracy,layoutL,layoutR,hJtarget,hLtarget,hJexp,hLexp,hJFs,hLFs,
    huf.trans (huser.trans hu),Nat.add_le_add hm hk,hfieldsL,hfieldsR,harchL.trans harchiveL,
    harchR.trans harchiveR,Exec.seq helift heSecond⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
