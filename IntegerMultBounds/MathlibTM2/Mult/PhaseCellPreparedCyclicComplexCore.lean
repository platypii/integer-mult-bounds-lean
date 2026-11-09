module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicComplexCoreCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCachedReplicaInput

/-! Ordinary width/crop controls execute before the numerical core. Physical
cached readiness is read through the bank view, not supplied a second time. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def preparedCyclicComplexCore (bank : Fin 909 → Fin T) (source : Fin 3 → Fin T) (tmp : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (installCyclicComplexCoreControls bank source tmp) (placedCyclicComplexCore bank hR hQ)

theorem preparedCyclicComplexCore_exec (bank : Fin 909 → Fin T) (hbank : Function.Injective bank)
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
      (source : Fin 3 → Fin T) (tmp : Fin T),
    let small := bank ∘ Fin.castLE (by decide : 834 ≤ 909)
    let small_injective := hbank.comp (Fin.castLE_injective (by decide : 834 ≤ 909))
    CachedReplicaPassInput H (CyclicReplicaPlacement.left.reindex small small_injective) buffersL S →
    CachedReplicaPassInput K (CyclicReplicaPlacement.right.reindex small small_injective) buffersR S →
    CyclicResidualBatchInput p l s t u solveTarget a n [] [] (embStk (small ∘ CyclicReplicaPlacement.factorReg) S) →
    S.R (small (CyclicReplicaPlacement.factorReg 226)) = [] →
    S.R (small (CyclicReplicaPlacement.factorReg 229)) = [] →
    (∀ i j, source i ≠ bank j) → (∀ i, source i ≠ tmp) → (∀ i, bank i ≠ tmp) →
    (∀ i, (S.R (source i)).length = ![W,radius,coreLength s coreWidth k] i) →
    (∀ i : Fin 909, 834 ≤ i.val → S.L (bank i) = [] ∧ S.R (bank i) = []) → S.R tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (v' : HS T Q A U) (G : Stacks T A) (steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧ CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      steps ≤ (4*(W+radius+coreLength s coreWidth k)+13)+
        Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
          (coreLength s coreWidth k) Rs.length Fs.length ∧
      Exec body (preparedCyclicComplexCore bank source tmp hR hQ) (mk v S) steps (mk v' G) ∧
      G.R (bank 850) = word ∧ G.R (bank 848) = [] ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      (∀ i, (∀ j, bank j ≠ i) → G.L i = S.L i ∧ G.R i = S.R i) := by
  dsimp only
  intro Fs hF W hW buffersL buffersR v S source tmp inputsL inputsR factory h226 h229
    hsourceOff hsourceTmp hbankTmp hvalues hfresh htmp localityTarget qRef Y hqRef hwindow hY
  let I := embStk (bank ∘ Fin.castLE (by decide : 834 ≤ 909)) S
  obtain ⟨v₁,F,hu₁,he₁,hview,hI,hO,hL,hoff⟩ := installCyclicComplexCoreControls_exec
    (body := body) bank hbank source tmp hsourceOff hsourceTmp hbankTmp W radius
    (coreLength s coreWidth k) v S hvalues hfresh htmp
  have hcost := cyclicComplexControlCopies_cost bank source W radius (coreLength s coreWidth k) S hvalues
  rw [hcost] at he₁
  obtain ⟨J,L,v₂,G,m,word,hu₂,hprofile,hm,he₂,hword,h848,hcert,hframe⟩ := placedCyclicComplexCore_exec
    (body := body) bank hbank hR hQ hA axis ha hn hleftRoom hrightRoom coreWidth k radius
    hleft haCore hnCore hright Fs hF W hW buffersL buffersR v₁ F I
    inputsL.of_reindex inputsR.of_reindex factory h226 h229 hview localityTarget qRef Y hqRef hwindow hY
  refine ⟨J,L,v₂,G,_,word,hu₂.trans hu₁,hprofile,Nat.add_le_add (le_refl _) hm,
    Exec.seq he₁ he₂,hword,h848,hcert,?_⟩
  intro i hi
  exact ⟨(hframe i hi).1.trans (congrFun hL i),(hframe i hi).2.trans (hoff i hi)⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
