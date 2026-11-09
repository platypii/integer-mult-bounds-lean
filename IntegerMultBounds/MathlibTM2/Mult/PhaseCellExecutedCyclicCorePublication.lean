module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicPackedNormalization
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPhysicalNormalizedCorePublication

/-! Ordinary fitting-halo inputs execute through normalized, forward-order core
publication. The existing crop machine adds no arithmetic error. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
local notation "extendNormalization" => CyclicPackedNormalizationPlacement.extend
local notation "extendAssembly" => CyclicPackedAssemblyPlacement.extend
local notation "extendSecond" => CyclicSecondInteriorPlacement.extend
abbrev cyclicCorePublicationReg : Fin 907 → Fin 909 := Fin.castLE (by decide)
variable {Q A : ℕ} {P U : Type} {body : P → Pr P 117 Q A U}

noncomputable def executedCyclicCorePublication (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P 909 Q A U :=
  .seq (embProg cyclicCorePublicationReg id (executedCyclicPackedNormalization hR hQ)) normalizedCorePublication

theorem executedCyclicCorePublication_spec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
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
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value q (F i)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem cellTarget 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem cellTarget 2 a n hn Fs hF
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
      (fields : Fin Fs.length → ZMod s → GaussianInt) (xs : List (ZMod s → ℝ))
      (vf : HS 909 Q A U) (steps : ℕ) (savedL savedR : List (Fin (A+4))),
      let Gs := ((List.ofFn fields).reverse).map
        (fun D i => finalRoundWord w q p (inverseNormalizationShift p) (D i))
      let F₀ := cyclicPackedNormalizationInput G wide
      let F := {F₀ with R := (Function.update (Function.update F₀.R 848
        ((Gs.map (fun D => cstream A W (packedInterval a (min n (s-a)) D))).flatten)) 849
        ((Gs.map (fun D => cstream A W (packedInterval 0 (n-min n (s-a)) D))).flatten))}
      let D := normalizedCorePublicationInput F radiusWord coreWord
      vf.user = v.user ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ cachedCyclicReplicaBoundaryBill H K p u l t a n solveTarget q w B.card (24*band+1) Fs.length+
        solvedCyclicRecoveryCost H K Fs.length B.card n w+
        cyclicSecondInteriorTimeBudget H K p solveTarget B.card+
        ((Fs.length*(retainedPackedPublicationMergeCost H.span H.wordWidth+5)+4)+
          (Fs.length*(retainedPackedPublicationMergeCost K.span K.wordWidth+5)+4))+
        (PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) Fs.length+
          PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) Fs.length)+
        (packedCoreArchiveControlsCost radius (coreLength s coreWidth k) W Fs.length+
          (Fs.length*(packedCoreArchiveStepCost radius (coreLength s coreWidth k)
            (coreLength s coreWidth k+2*radius) W+3)+2)+
          (2*(radius*W+coreLength s coreWidth k*W+(coreLength s coreWidth k+2*radius))+7)) ∧
      G.R 247 = buffersL.accumulatorTail ∧ G.R 547 = buffersR.accumulatorTail ∧
      G.R 125 = savedL ∧ G.R 425 = savedR ∧
      ReplicaAssemblyControls H (CyclicPackedNormalizationPlacement.gather false) 839 G ∧
      ReplicaAssemblyControls K (CyclicPackedNormalizationPlacement.gather true) 838 G ∧
      (G.inp = S.inp ∧ G.out = S.out) ∧
      List.Forall₂ (fun rhs x => SchurDominance.Solves (realMatrix s t p u)
        (cyclicPrincipalVertices s a n) x (fun i => (value q (rhs i)).re)) Fs xs.reverse ∧
      Exec (embTab cyclicCorePublicationReg (embTab extendNormalization (embTab extendAssembly
          (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body))))))
        (executedCyclicCorePublication hR hQ)
        (mk v (normalizedCorePublicationInput (cyclicPackedNormalizationInput
          (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
            (extendStacks (by decide : 834 ≤ 840) S))) wide) radiusWord coreWord)) steps
        (mk vf {D with R := (Function.update (Function.update D.R 848 []) 850
          ((Gs.reverse.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten))}) ∧
      (let output := {D with R := (Function.update (Function.update D.R 848 []) 850
          ((Gs.reverse.map (fun F => cstream A W (ownedCoreWords coreWidth k F))).flatten))}
       (output.R 121).length = Fs.length ∧ (output.R 908).length = coreLength s coreWidth k ∧
       (output.R 906).length = W ∧ ∀ i ∈ ([(851 : Fin 909),852,853,854,855,856,857]), output.R i = []) ∧
      List.Forall₂ (fun x F => PhaseCellInterface.ErrorOn (ownedCore s coreWidth k)
        (packedIntervalRead p W (coreStart coreWidth k) (cstream A W (ownedCoreWords coreWidth k F)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs.reverse Gs.reverse := by
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
  intro W hW wide hwide radiusWord coreWord hRword hLword buffersL buffersR v S tail pageTail
    inputsL inputsR factory h226 h229
  obtain ⟨J,L,X,G,fields,xs,z,m,savedL,savedR,hu,hprofile,hm,h247,h547,h125,h425,controlsL,controlsR,hstreams,hsol,he,haccL,haccR⟩ :=
    executedCyclicPackedNormalization_spec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom
      Fs hF W hW wide hwide buffersL buffersR (embDn cyclicCorePublicationReg v) S tail pageTail
      inputsL inputsR factory h226 h229
  let Gs := ((List.ofFn fields).reverse).map
    (fun F i => finalRoundWord w q p (inverseNormalizationShift p) (F i))
  let F₀ := cyclicPackedNormalizationInput G wide
  let F : Stacks 907 A := {F₀ with R := (Function.update (Function.update F₀.R 848
    ((Gs.map (fun F => cstream A W (packedInterval a (min n (s-a)) F))).flatten)) 849
    ((Gs.map (fun F => cstream A W (packedInterval 0 (n-min n (s-a)) F))).flatten))}
  let initial := cyclicPackedNormalizationInput
    (extendStacks (by decide : 842 ≤ 850) (extendStacks (by decide : 840 ≤ 842)
      (extendStacks (by decide : 834 ≤ 840) S))) wide
  let V := normalizedCorePublicationInput initial radiusWord coreWord
  let callerBody := embTab cyclicCorePublicationReg (embTab extendNormalization (embTab extendAssembly
    (embTab extendSecond (embTab CyclicRecoveryPlacement.extend (cyclicReplicaCallerBody body)))))
  obtain ⟨vi,hvi,huser,helift⟩ := exec_emb_ovr (body' := callerBody) (e := cyclicCorePublicationReg) (ι := id)
    (Fin.castLE_injective _) (fun _ => rfl) he v rfl V (normalizedCorePublicationInput_view initial radiusWord coreWord)
  have hstate : embOvr cyclicCorePublicationReg F.get V = normalizedCorePublicationInput F radiusWord coreWord :=
    normalizedCorePublicationInput_override initial F radiusWord coreWord
  have helift' := helift.cast rfl (congrArg (mk vi) hstate)
  have hfit : a+n ≤ s := by omega
  have hmin : min n (s-a) = n := min_eq_left (by omega)
  have hsrc : F.R 848 = (Gs.map (fun D => cstream A W
      (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D))).flatten := by
    simp only [F,Function.update_of_ne (by decide : (848 : Fin 907) ≠ 849),Function.update_self]
    rw [hmin,haCore,hnCore]
  have hw : (F.R 906).length = W := by
    simpa [F,F₀,cyclicPackedNormalizationInput] using hwide
  have hDlen : Gs.length = Fs.length := by simp [Gs]
  have hN : (F.R 121).length = Gs.length := by
    have hrep := controlsL.replicas
    have hg : CyclicPackedNormalizationPlacement.gather false 121 = (121 : Fin 850) := by decide +kernel
    rw [hg] at hrep
    have hread : F₀.R (121 : Fin 907) = G.R 121 := by
      simp only [F₀,cyclicPackedNormalizationInput,
        Function.update_of_ne (by decide : (121 : Fin 907) ≠ 906)]
      rfl
    have hread' : F.R 121 = G.R 121 := by
      simpa only [F,Function.update_of_ne (by decide : (121 : Fin 907) ≠ 849),
        Function.update_of_ne (by decide : (121 : Fin 907) ≠ 848)] using hread
    rw [hread',hDlen]
    exact hrep
  have hfresh (i : Fin 907) (hi : 850 ≤ i.val) (hi' : i.val < 906) : F.R i = [] := by
    have h848 : i ≠ 848 := by intro h; have hv := congrArg Fin.val h; omega
    have h849 : i ≠ 849 := by intro h; have hv := congrArg Fin.val h; omega
    have h906 : i ≠ 906 := by intro h; have hv := congrArg Fin.val h; omega
    simp only [F,F₀,cyclicPackedNormalizationInput,Function.update_of_ne h848,
      Function.update_of_ne h849,Function.update_of_ne h906]
    exact (extendStacks_fresh (by decide : 850 ≤ 907) G i hi).2
  have hgood : List.Forall₂ (fun z D => PhaseCellInterface.ErrorOn
      (haloVertices s (coreStart coreWidth k-radius) (coreStart coreWidth k+coreLength s coreWidth k+radius))
      (packedIntervalRead p W (coreStart coreWidth k-radius)
        (cstream A W (packedInterval (coreStart coreWidth k-radius) (coreLength s coreWidth k+2*radius) D)))
      z (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p))
      (xs.map (fun x i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))) Gs := by
    apply List.forall₂_map_left_iff.mpr
    have hend : a+min n (s-a) = coreStart coreWidth k+coreLength s coreWidth k+radius := by omega
    have hacc : List.Forall₂ (fun x D => PhaseCellInterface.ErrorOn (haloVertices s a (a+min n (s-a)))
        (packedIntervalRead p W a (cstream A W (packedInterval a (min n (s-a)) D)))
        (fun i => ((2 : ℂ)^inverseNormalizationShift p)⁻¹*(x i : ℂ))
        (1/(2 : ℝ)^p+(1/(2 : ℝ)^(target+1))/(2 : ℝ)^inverseNormalizationShift p)) xs Gs := haccL
    rw [hend,hmin] at hacc
    simpa only [haCore,hnCore] using hacc
  obtain ⟨vf,nc,huf,hnc,hecrop,hready,haccuracy⟩ := normalizedCorePublication_exec (body := callerBody)
    p W coreWidth k radius hleft hright _ Gs _ hgood vi F radiusWord coreWord hRword hLword hsrc hw hN hfresh
  refine ⟨J,L,X,G,fields,xs,vf,m+nc,savedL,savedR,huf.trans (huser.trans hu),hprofile,?_,
    h247,h547,h125,h425,controlsL,controlsR,hstreams,?_,Exec.seq helift' hecrop,?_,?_⟩
  · simpa only [hDlen] using Nat.add_le_add hm hnc
  · simpa only [List.reverse_reverse] using List.forall₂_reverse_iff.mpr hsol
  · simpa only [hDlen] using hready
  · exact List.forall₂_map_left_iff.mp (by simpa only [←List.map_reverse] using haccuracy)

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
