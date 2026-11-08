module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicPackedRecovery
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRecoveredCyclicPackedNormalization
public import IntegerMultBounds.MathlibTM2.Host.ExtendStacksRight

/-! Ordinary original-RHS inputs execute recovery and both common-width
normalizations. Reference solutions and publication readiness are derived. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
local notation "extendNormalization" => CyclicPackedNormalizationPlacement.extend
local notation "extendAssembly" => CyclicPackedAssemblyPlacement.extend
local notation "extendSecond" => CyclicSecondInteriorPlacement.extend
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def executedCyclicPackedNormalization (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 907 Q A U :=
  .seq (embProg extendNormalization id (executedCyclicPackedRecovery hR hQ)) cyclicPackedNormalization

theorem executedCyclicPackedNormalization_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
    ∀ (W : ℕ) (_ : 2*p+13 ≤ W) (wide : List (Fin (A+4))) (_ : wide.length = W)
      (buffersL buffersR : ReplicaLoopBuffers A) (v : HS 907 Q A U) (S : Stacks 834 A)
      (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H CyclicReplicaPlacement.left buffersL S →
    CachedReplicaPassInput K CyclicReplicaPlacement.right buffersR S →
    CyclicResidualBatchInput p l s t u solveTarget a n tail pageTail (embStk CyclicReplicaPlacement.factorReg S) →
    S.R (CyclicReplicaPlacement.factorReg 226) = [] → S.R (CyclicReplicaPlacement.factorReg 229) = [] →
    ∃ (J L : ReplicaHaloProblem s) (X : Stacks 840 A) (G : Stacks 850 A)
      (fields : Fin Fs.length → ZMod s → GaussianInt) (xs : List (ZMod s → ℝ))
      (vf : HS 907 Q A U) (steps : ℕ) (savedL savedR : List (Fin (A+4))),
      let E := extendStacks (by decide : 840 ≤ 842) X
      let Gs := ((List.ofFn fields).reverse).map
        (fun D i => finalRoundWord w q p (inverseNormalizationShift p) (D i))
      let F := cyclicPackedNormalizationInput G wide
      vf.user = v.user ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n solveTarget q w B.card (24*band+1) Fs.length+
        solvedCyclicRecoveryCost H K Fs.length B.card n w+
        (releaseReplicaInteriorBankCost CyclicSecondInteriorPlacement.left.plan E+H.interiorTimeBudget (boundaryHaloRecoveryTarget p solveTarget B.card)
            (recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u))+
          (releaseReplicaInteriorBankCost CyclicSecondInteriorPlacement.right.plan E+K.interiorTimeBudget (boundaryHaloRecoveryTarget p solveTarget B.card)
            (recoveryRhsExponent p 2 (stableInteriorExponent p 2) (couplingCountExponent p u))))+
        ((Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
          (Fs.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4))+
        (PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) Fs.length+
          PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) Fs.length) ∧
      G.R 247 = buffersL.accumulatorTail ∧ G.R 547 = buffersR.accumulatorTail ∧
      G.R 125 = savedL ∧ G.R 425 = savedR ∧
      ReplicaAssemblyControls H (CyclicPackedNormalizationPlacement.gather false) 839 G ∧
      ReplicaAssemblyControls K (CyclicPackedNormalizationPlacement.gather true) 838 G ∧
      List.Forall₂ (fun rhs x => SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) x (fun i => (value q (rhs i)).re)) Fs.reverse xs ∧
      Exec (embTab extendNormalization (embTab extendAssembly
          (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))))
        (executedCyclicPackedNormalization hR hQ)
        (mk v (cyclicPackedNormalizationInput
          (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
            (extendStacks (by decide : 834 ≤ 840) S))) wide)) steps
        (mk vf {F with R := (Function.update (Function.update F.R 848
          ((Gs.map (fun D => cstream A W (packedInterval a (min n (s-a)) D))).flatten)) 849
          ((Gs.map (fun D => cstream A W (packedInterval 0 (n-min n (s-a)) D))).flatten))}) ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s a (a+min n (s-a)))
        (packedIntervalRead p W a (cstream A W (packedInterval a (min n (s-a)) D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs Gs ∧
      List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s 0 (n-min n (s-a)))
        (packedIntervalRead p W 0 (cstream A W (packedInterval 0 (n-min n (s-a)) D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  intro Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
  intro W hW wide hwide buffersL buffersR v S tail pageTail inputsL inputsR factory h226 h229
  obtain ⟨J,L,X,z,G,fields,m,savedL,savedR,hu,hm,hwordsL,hwordsR,h247,h547,h125,h425,hfields,controlsL,controlsR,he⟩ :=
    executedCyclicPackedRecovery_spec (body := body) (target := target+1) hR hQ hA axis ha hn hleftRoom hrightRoom
      Fs hF buffersL buffersR (embDn extendNormalization v) S tail pageTail inputsL inputsR factory h226 h229
  let callerBody := embTab extendNormalization (embTab extendAssembly
    (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))
  obtain ⟨vi,hvi,huser,helift⟩ := exec_extendStacks_right (by decide : 850 ≤ 907) (ι := id)
    (body' := callerBody) (fun _ => rfl) he 906 (by decide) wide v rfl
  have controlsL' : ReplicaAssemblyControls H (CyclicPackedNormalizationPlacement.gather false) 839 G := by
    exact controlsL
  have controlsR' : ReplicaAssemblyControls K (CyclicPackedNormalizationPlacement.gather true) 838 G := by
    exact controlsR
  obtain ⟨xs,vf,k,hsol,huf,hk,henorm,haccL,haccR⟩ := recoveredCyclicPackedNormalization_exec
    (body := callerBody) (target := target) (by omega : 4 ≤ A) axis ha hn Fs hF fields
    (fun j => ⟨(hfields j).1,(hfields j).2.1,(hfields j).2.2.2⟩)
    W hW wide hwide vi G controlsL' controlsR' hwordsL hwordsR
  refine ⟨J,L,X,G,fields,xs,vf,m+k,savedL,savedR,huf.trans (huser.trans hu),
    Nat.add_le_add hm hk,h247,h547,h125,h425,controlsL',controlsR',hsol,?_,haccL,haccR⟩
  exact Exec.seq helift henorm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
