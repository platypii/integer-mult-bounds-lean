module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicCorePublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellNormalizedComponentSolutions
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrincipalNormalizedOutput

/-! Component-input banks execute the complete fitting-halo complex core trace.
The component order, exact principal target, pairing count and readiness derive
from ordinary data and the executed scalar endpoint. -/
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

theorem shiftedComplexComponents_bound {s : ℕ} (p q : ℕ) (hpq : p+1 ≤ q)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1) :
    ∀ R ∈ (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i),
      ∀ i, ‖value q (R i)‖ ≤ (2 : ℝ)^2 := by
  intro R hR i
  obtain ⟨F,hmem,rfl⟩ := List.mem_map.mp hR
  exact packedBatch_shift_bound p q 2 hpq (complexComponentFields Fs)
    (complexComponentFields_norm_le p Fs hF) F hmem i

noncomputable def executedCyclicComplexCore (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 909 Q A U :=
  .seq (executedCyclicCorePublication hR hQ) normalizedComponentSolutionsAssembly

theorem executedCyclicComplexCore_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s) :
    let band := PhaseCellBand.width p u
    let B := cyclicPrincipalBoundary s t band a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l cellTarget 2
    let w := executionWidth p l cellTarget 2
    let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1),
    let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
    let hRs := shiftedComplexComponents_bound p q hqp Fs hF
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Rs hRs
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Rs hRs
    ∀ (W : ℕ) (_ : 2*p+13 ≤ W) (wide : List (Fin (A+4))) (_ : wide.length = W)
      (radiusWord coreWord : List (Fin (A+4))) (_ : radiusWord.length = radius)
      (_ : coreWord.length = coreLength s coreWidth k)
      (buffersL buffersR : ReplicaLoopBuffers A) (v : HS 909 Q A U) (S : Stacks 834 A)
      (tail pageTail : List (Fin (A+4))),
    CachedReplicaPassInput H CyclicReplicaPlacement.left buffersL S →
    CachedReplicaPassInput K CyclicReplicaPlacement.right buffersR S →
    CyclicResidualBatchInput p l s t u solveTarget a n tail pageTail (embStk CyclicReplicaPlacement.factorReg S) →
    S.R (CyclicReplicaPlacement.factorReg 226) = [] → S.R (CyclicReplicaPlacement.factorReg 229) = [] →
    ∃ (J L : ReplicaHaloProblem s) (X : Stacks 840 A) (G : Stacks 850 A)
      (fields : Fin Rs.length → ZMod s → GaussianInt)
      (y : (ZMod s → GaussianInt) → ZMod s → ℝ) (vf : HS 909 Q A U)
      (steps : ℕ) (savedL savedR : List (Fin (A+4))),
      let scalars := ((List.ofFn fields).reverse).map
        (fun D i => finalRoundWord w q p (inverseNormalizationShift p) (D i))
      let Ds := scalars.reverse
      let Zs := pairedComponentFields (Ds.take Fs.length) (Ds.drop Fs.length)
      let F₀ := cyclicPackedNormalizationInput G wide
      let F := {F₀ with R := (Function.update (Function.update F₀.R 848
        ((scalars.map (fun D => cstream A W (packedInterval a (min n (s-a)) D))).flatten)) 849
        ((scalars.map (fun D => cstream A W (packedInterval 0 (n-min n (s-a)) D))).flatten))}
      let D := normalizedCorePublicationInput F radiusWord coreWord
      vf.user = v.user ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n solveTarget q w B.card (24*band+1) Rs.length+
        solvedCyclicRecoveryCost H K Rs.length B.card n w+
        cyclicSecondInteriorTimeBudget H K p solveTarget B.card+
        ((Rs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
          (Rs.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4))+
        (PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) Rs.length+
          PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) Rs.length)+
        (packedCoreArchiveControlsCost radius (coreLength s coreWidth k) W Rs.length+
          (Rs.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
            (coreLength s coreWidth k+2*radius) W+3)+2)+
          (2*(radius*W+coreLength s coreWidth k*W+(coreLength s coreWidth k+2*radius))+7))+
        ((6*Fs.length+4)+((coreLength s coreWidth k*(4*W+9)+4)+
          (Fs.length*(16*(coreLength s coreWidth k*W)+9)+14)+(2*(coreLength s coreWidth k*W)+2))+
          (2*Fs.length+2)) ∧
      G.R 247 = buffersL.accumulatorTail ∧ G.R 547 = buffersR.accumulatorTail ∧
      G.R 125 = savedL ∧ G.R 425 = savedR ∧ Zs.length = Fs.length ∧
      (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) (y F)
        (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re)) ∧
      Exec (embTab cyclicCorePublicationReg (embTab extendNormalization (embTab extendAssembly
          (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))))
        (executedCyclicComplexCore hR hQ)
        (mk v (normalizedCorePublicationInput (cyclicPackedNormalizationInput
          (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
            (extendStacks (by decide : 834 ≤ 840) S))) wide) radiusWord coreWord)) steps
        (mk vf {D with R := (Function.update (Function.update D.R 848 []) 850
          ((Zs.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten))}) ∧
      List.Forall₂ (fun z F => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k F))) z
        (2/(2 : ℝ)^p+(1/(2 : ℝ)^target)/(2 : ℝ)^inverseNormalizationShift p))
        (Fs.map (fun F i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*componentSolution y F i)) Zs ∧
      ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
        p+1 ≤ qRef →
        cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
        (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
          (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
        PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y
          ((Zs.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten) := by
  dsimp only
  let band := PhaseCellBand.width p u
  let B := cyclicPrincipalBoundary s t band a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let cellTarget := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l cellTarget 2
  let w := executionWidth p l cellTarget 2
  let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  intro Fs hF
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Rs hRs
  intro W hW wide hwide radiusWord coreWord hRword hLword buffersL buffersR v S tail pageTail
    inputsL inputsR factory h226 h229
  obtain ⟨J,L,X,G,fields,xs,vi,m,savedL,savedR,hu,hprofile,hm,h247,h547,h125,h425,controlsL,controlsR,hsol,he,hready,hacc⟩ :=
    executedCyclicCorePublication_spec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom
      coreWidth k radius hleft haCore hnCore hright Rs hRs W hW wide hwide radiusWord coreWord hRword hLword
      buffersL buffersR v S tail pageTail inputsL inputsR factory h226 h229
  let scalars := ((List.ofFn fields).reverse).map
    (fun D i => finalRoundWord w q p (inverseNormalizationShift p) (D i))
  let Ds := scalars.reverse
  let F₀ := cyclicPackedNormalizationInput G wide
  let F : Stacks 907 A := {F₀ with R := (Function.update (Function.update F₀.R 848
    ((scalars.map (fun D => cstream A W (packedInterval a (min n (s-a)) D))).flatten)) 849
    ((scalars.map (fun D => cstream A W (packedInterval 0 (n-min n (s-a)) D))).flatten))}
  let D := normalizedCorePublicationInput F radiusWord coreWord
  let V : Stacks 909 A := {D with R := (Function.update (Function.update D.R 848 []) 850
    ((Ds.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten))}
  let callerBody := embTab cyclicCorePublicationReg (embTab extendNormalization (embTab extendAssembly
    (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))))
  have hp : 0 < p := by have h := axis.hp; omega
  have hμ : (0 : ℝ) < 1/(8*(p : ℝ)) := by positivity
  have hdom := SchurDominance.dominates_mono (realMatrix s t p u) Finset.univ
    (cyclicPrincipalVertices s a n) _ (Finset.subset_univ _) axis.hdom
  have hex (F : ZMod s → GaussianInt) : ∃ x, SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalVertices s a n) x (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) :=
    SchurDominance.solves_exists _ _ _ hμ hdom _
  let y := fun F => Classical.choose (hex F)
  have hy : ∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u)
      (cyclicPrincipalVertices s a n) (y F) (fun i => (value q ((2 : GaussianInt)^(q-p-1)*F i)).re) :=
    fun F _ => Classical.choose_spec (hex F)
  have hfit : a+n ≤ s := by omega
  have hmin : min n (s-a) = n := min_eq_left (by omega)
  have hcore : ownedCore s coreWidth k ⊆ cyclicPrincipalVertices s a n := by
    intro i hi
    have hb := (mem_haloVertices (coreStart coreWidth k) (coreStart coreWidth k+coreLength s coreWidth k) i).mp hi
    exact Finset.mem_union_left _ ((mem_haloVertices _ _ i).mpr ⟨by omega,by omega⟩)
  have hDlen : Ds.length = Rs.length := by simp [Ds,scalars]
  have hscalar : (V.R 121).length = Ds.length := hready.1.trans hDlen.symm
  have hsrc : V.R 850 = (Ds.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten++[] := by
    simp only [V,Function.update_self,List.append_nil]
  obtain ⟨hlen,vf,nc,huf,hnc,hasm,haccuracy⟩ := assembleNormalizedComponentSolutions_exec (body := callerBody)
    (by omega : 4 ≤ A) (realMatrix s t p u) (cyclicPrincipalVertices s a n) (1/(8*(p : ℝ))) hμ hdom
    p q (q-p-1) (inverseNormalizationShift p) W coreWidth k target hcore (by omega) Fs y hy
    xs.reverse Ds hsol hacc [] vi V hscalar hready.2.1 hready.2.2.1 hsrc hready.2.2.2
  refine ⟨J,L,X,G,fields,y,vf,m+nc,savedL,savedR,huf.trans hu,hprofile,Nat.add_le_add hm hnc,
    h247,h547,h125,h425,hlen,hy,?_,?_,?_⟩
  · simpa only [executedCyclicComplexCore,V,Function.update_idem,List.append_nil] using Exec.seq he hasm
  · simpa only [List.append_nil] using haccuracy
  · intro localityTarget qRef Y hpRef hhalo hY
    exact principalNormalizedOutput (q := q) (a := a) (n := n) axis hqp W target coreWidth k localityTarget qRef hpRef
      hhalo Fs hF y Y hy hY _ hlen (by simpa only [List.append_nil] using haccuracy)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
