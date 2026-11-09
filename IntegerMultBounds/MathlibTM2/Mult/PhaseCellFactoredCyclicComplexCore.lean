module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCyclicComplexCore
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCyclicFactorFromCached

/-! Cached inputs execute factor preparation, ordinary control installation and
numerical publication as one program. No factor-input supplier remains. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open CyclicReplicaPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def factoredCyclicComplexCore (bank : Fin 909 → Fin T) (source : Fin 3 → Fin T)
    (span tmp : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (prepareCyclicFactorFromCached (bank ∘ Fin.castLE (by decide : 834 ≤ 909)) span tmp)
    (preparedCyclicComplexCore bank source tmp hR hQ)

theorem factoredCyclicComplexCore_exec (bank : Fin 909 → Fin T) (hbank : Function.Injective bank)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s) :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
    let q := executionPrecision p l stage 2
    let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1),
    let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
    let hRs := shiftedComplexComponents_bound p q hqp Fs hF
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
    let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
    ∀ (W : ℕ), 2*p+13 ≤ W →
    ∀ (buffersL buffersR : ReplicaLoopBuffers A) (v : HS T Q A U) (S : Stacks T A)
      (source : Fin 3 → Fin T) (span tmp : Fin T),
    let small := bank ∘ Fin.castLE (by decide : 834 ≤ 909)
    let small_injective := hbank.comp (Fin.castLE_injective (by decide : 834 ≤ 909))
    CachedReplicaPassInput H (CyclicReplicaPlacement.left.reindex small small_injective) buffersL S →
    CachedReplicaPassInput K (CyclicReplicaPlacement.right.reindex small small_injective) buffersR S →
    (S.R span).length = n → (∀ i, span ≠ bank i) → span ≠ tmp →
    (∀ i, S.L (small (CyclicReplicaPlacement.factorReg i)) = [] ∧
      S.R (small (CyclicReplicaPlacement.factorReg i)) = []) →
    (∀ i j, source i ≠ bank j) → (∀ i, source i ≠ tmp) → (∀ i, bank i ≠ tmp) →
    (∀ i, (S.R (source i)).length = ![W,radius,coreLength s coreWidth k] i) →
    (∀ i : Fin 909, 834 ≤ i.val → S.L (bank i) = [] ∧ S.R (bank i) = []) → S.R tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (v' : HS T Q A U) (F G : Stacks T A) (steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ (copyUnaryHeadersCost (fun k => (S.R k).length)
        (masterHeaderCopies ((small ∘ CyclicReplicaPlacement.factorReg) ∘ Fin.castLE (by decide : 224 ≤ 234))
          (cachedFactorSeedSource (small ∘ CyclicReplicaPlacement.left.plan.gather) span))+
        prepareCyclicBoundaryPageCost
          (embStk (Fin.castLE (by decide : 154 ≤ 234)) (embStk (small ∘ CyclicReplicaPlacement.factorReg) F)).R
          s t (PhaseCellBand.width p u) a n)+((4*(W+radius+coreLength s coreWidth k)+13)+
        Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
          (coreLength s coreWidth k) Rs.length Fs.length) ∧
      Exec body (factoredCyclicComplexCore bank source span tmp hR hQ) (mk v S) steps (mk v' G) ∧
      G.R (bank 850) = word ∧ G.R (bank 848) = [] ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      (∀ i, (∀ j, bank j ≠ i) → G.L i = S.L i ∧ G.R i = S.R i) := by
  dsimp only
  intro Fs hF
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l stage 2
  let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  let small := bank ∘ Fin.castLE (by decide : 834 ≤ 909)
  have hsmall : Function.Injective small := hbank.comp (Fin.castLE_injective _)
  intro W hW buffersL buffersR v S source span tmp inputsL inputsR hspan hspanOff hspanTmp
    hfactorFresh hsourceOff hsourceTmp hbankTmp hvalues hfresh htmp localityTarget qRef Y hqRef hwindow hY
  have hgatherOff (i : Fin 126) (j : Fin 234) :
      small (left.plan.gather i) ≠ small (factorReg j) := by
    intro he
    have hv := congrArg Fin.val (hsmall he)
    change i.val = 600+j.val at hv
    have := i.isLt
    omega
  have hseedOff (i : Fin 10) (j : Fin 234) :
      cachedFactorSeedSource (small ∘ left.plan.gather) span i ≠ small (factorReg j) := by
    fin_cases i <;> first | exact hgatherOff _ j | exact hspanOff _
  have hseedTmp (i : Fin 10) : cachedFactorSeedSource (small ∘ left.plan.gather) span i ≠ tmp := by
    fin_cases i <;> first | exact hbankTmp _ | exact hspanTmp
  have hmaster := axis.cyclicLeftReplicaProblem_factorSeedValues solveTarget a n ha Rs hRs
  obtain ⟨v₁,F,R,n₁,hu₁,hseed,hn₁,he₁,factory,inputsL',inputsR',hframe,h226,h229⟩ :=
    prepareCyclicFactorFromCached_exec (body := body) small hsmall H.s_lt_t ha hn H.band_fit
      H K buffersL buffersR span tmp hseedOff hseedTmp (fun i => hbankTmp _) v S
      inputsL inputsR hmaster hspan (fun i => (hfactorFresh i).2) (fun i => (hfactorFresh i).1) htmp
  have hvalues' (i : Fin 3) : (R.R (source i)).length = ![W,radius,coreLength s coreWidth k] i := by
    rw [(hframe (source i) (fun j => (hsourceOff i _).symm)).2]
    exact hvalues i
  have hfresh' (i : Fin 909) (hi : 834 ≤ i.val) : R.L (bank i) = [] ∧ R.R (bank i) = [] := by
    have hoff : ∀ j, small (factorReg j) ≠ bank i := by
      intro j he
      have hv := congrArg Fin.val (hbank he)
      change 600+j.val = i.val at hv
      have := j.isLt
      omega
    have hh := hframe (bank i) hoff
    exact ⟨hh.1.trans (hfresh i hi).1,hh.2.trans (hfresh i hi).2⟩
  have htmp' : R.R tmp = [] := (hframe tmp (fun i => hbankTmp _)).2.trans htmp
  obtain ⟨J,L,v₂,G,n₂,word,hu₂,hprofile,hn₂,he₂,hword,h848,hcert,houtside⟩ :=
    preparedCyclicComplexCore_exec (body := body) bank hbank hR hQ hA axis ha hn hleftRoom hrightRoom
      coreWidth k radius hleft haCore hnCore hright Fs hF W hW buffersL buffersR v₁ R source tmp
      inputsL' inputsR' factory h226 h229 hsourceOff hsourceTmp hbankTmp hvalues' hfresh' htmp'
      localityTarget qRef Y hqRef hwindow hY
  refine ⟨J,L,v₂,F,G,n₁+n₂,word,hu₂.trans hu₁,hseed,hprofile,Nat.add_le_add hn₁ hn₂,
    Exec.seq he₁ he₂,hword,h848,hcert,?_⟩
  intro i hi
  have hf := hframe i (fun j => hi _)
  exact ⟨(houtside i hi).1.trans hf.1,(houtside i hi).2.trans hf.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
