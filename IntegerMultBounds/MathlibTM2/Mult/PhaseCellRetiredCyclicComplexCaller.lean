module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Mult.ExportClearRegisterBank
public import IntegerMultBounds.MathlibTM2.StackInvariantShift
public import IntegerMultBounds.MathlibTM2.Host.ConsumeRuns

/-! The numerical batch publishes to the caller and releases its complete
private bank, ready to receive the next routed batch. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def retiredProgram (ports : CyclicComplexCallerLayout T) (dst : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (ports.program hR hQ) (exportClearRegisterBank ports.bank 850 848 dst)

theorem retiredProgram_exec (ports : CyclicComplexCallerLayout T) (dst : Fin T)
    (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
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
    ∀ (W : ℕ), 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W →
    ∀ (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))),
    let small := ports.bank ∘ Fin.castLE (by decide : 834 ≤ 909)
    (∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []) →
    (∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedL i)).length = recoverySeedHeader H W Fs.length i) →
    (∀ i ∈ recoverySeedHeaderPorts, (S.R (ports.seedR i)).length = recoverySeedHeader K W Fs.length i) →
    S.R ports.archive = cstream A W (Fs.map (packedInterval a n)).flatten++tail →
    (S.R ports.count).length = Fs.length*n*W → (S.R ports.span).length = n →
    (∀ i, (S.R (ports.controls i)).length = ![W,radius,coreLength s coreWidth k] i) →
    S.R ports.saved = [] → S.R ports.tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ),
    p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (vm v' : HS T Q A U) (C F R G : Stacks T A) (runSteps steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      Exec body (ports.program hR hQ) (Host.mk v S) runSteps (Host.mk vm R) ∧
      steps = runSteps+exportClearRegisterBankCost ports.bank 850 dst R ∧
      (∀ depth, ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk vm R)+depth) depth
        (exportClearRegisterBank ports.bank 850 848 dst) (Host.mk vm R)
        (exportClearRegisterBankCost ports.bank 850 dst R) (Host.mk v' G)) ∧
      steps ≤ (ports.inputTimeCost H K W Fs.length S+
        (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
          Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
            (coreLength s coreWidth k) Rs.length Fs.length)))+
        (8*registerBankStock (embStk ports.bank R)+4*909+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*ports.inputTimeCost H K W Fs.length S+
          (cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*ports.factorTimeCost s t p u a n C F+
            (2*(4*(W+radius+coreLength s coreWidth k)+13)+
              cyclicComplexCoreWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
                p u l t a n solveTarget q (executionWidth p l stage 2) W B.card
                Rs.length Fs.length radius (coreLength s coreWidth k))))) 0
        (ports.retiredProgram dst hR hQ) (Host.mk v S) steps (Host.mk v' G) ∧
      Exec body (ports.retiredProgram dst hR hQ) (Host.mk v S) steps (Host.mk v' G) ∧
      G.R dst = word++S.R dst ∧
      (∀ i, G.L (ports.bank i) = [] ∧ G.R (ports.bank i) = []) ∧ G.R ports.archive = tail ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      (G.inp = S.inp ∧ G.out = S.out) ∧ G.L = S.L ∧
      G = {S with R := Function.update (Function.update S.R ports.archive tail) dst (word++S.R dst)} ∧
      word.length = Fs.length*coreLength s coreWidth k*W ∧ word.length ≤ Fs.length*n*W ∧
      word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length ∧
      mnSize (Host.mk v' G) ≤ mnSize (Host.mk v S) ∧
      (∀ i, i ≠ ports.archive → i ≠ dst → (∀ j, ports.bank j ≠ i) → G.L i = S.L i ∧ G.R i = S.R i) := by
  dsimp only
  intro Fs hF W hW hWin v S tail hblank hvaluesL hvaluesR hsrc hcount hspan hcontrols hsaved htmp
    localityTarget qRef Y hqRef hwindow hY
  obtain ⟨J,L,v₁,C,F,R,n₁,word,hu₁,hseed,hprofile,hn₁,hfittingWithin,he₁,hword,h848,harchive,hcert,hstreams,hleftArchive,hframe⟩ :=
    ports.program_exec (body := body) hR hQ hA axis ha hn hleftRoom hrightRoom coreWidth k radius
      hleft haCore hnCore hright Fs hF W hW hWin v S tail hblank hvaluesL hvaluesR hsrc hcount hspan
      hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  obtain ⟨v₂,hu₂,hw₂,hclean,hresult,hframe₂⟩ := exportClearRegisterBank_exec (body := body)
    ports.bank ports.injective 850 848 (by decide) dst hdst v₁ R h848 0 (mnSize (Host.mk v₁ R)) (by omega)
  let G := clearedRegisterBank ports.bank {R with R := Function.update R.R dst (R.R (ports.bank 850)++R.R dst)}
  change ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v₁ R)) 0
    (exportClearRegisterBank ports.bank 850 848 dst) (Host.mk v₁ R)
    (exportClearRegisterBankCost ports.bank 850 dst R) (Host.mk v₂ G) at hw₂
  have hwhole := ExecWithin.seq hfittingWithin
    (hw₂.mono (by
      intro d z hz
      have hpeak := hfittingWithin.final
      omega))
  have he₂ := hw₂.toExec
  change Exec body (exportClearRegisterBank ports.bank 850 848 dst) (Host.mk v₁ R)
    (exportClearRegisterBankCost ports.bank 850 dst R) (Host.mk v₂ G) at he₂
  have hstreamsG : G.inp = S.inp ∧ G.out = S.out := by
    simpa only [G,clearedRegisterBank] using hstreams
  have hleft : G.L = S.L := by
    funext i
    by_cases hi : ∃ j, ports.bank j = i
    · obtain ⟨j,rfl⟩ := hi
      exact (hclean j).1.trans (hblank j).1.symm
    · have hoff : ∀ j, ports.bank j ≠ i := by simpa only [not_exists] using hi
      have hL : G.L i = R.L i := by simp only [G,clearedRegisterBank]; simp only [List.mem_ofFn]; simp [hi]
      rw [hL]
      by_cases ha : i = ports.archive
      · subst i; exact hleftArchive
      · exact (hframe i ha hoff).1
  have hfinal : G = {S with R := Function.update (Function.update S.R ports.archive tail) dst (word++S.R dst)} := by
    refine Stacks.ext hstreamsG.1 hstreamsG.2 hleft ?_
    funext i
    change G.R i = Function.update (Function.update S.R ports.archive tail) dst (word++S.R dst) i
    by_cases hd : i = dst
    · subst i
      simpa only [Function.update_self] using hresult.trans
        (by rw [hword,(hframe dst harchiveDst hdst).2])
    · by_cases ha : i = ports.archive
      · subst i
        simpa only [Function.update_of_ne hd,Function.update_self] using
          (hframe₂ ports.archive harchiveDst.symm (fun j => (ports.archiveOff j).symm)).2.trans harchive
      · rw [Function.update_of_ne hd,Function.update_of_ne ha]
        by_cases hi : ∃ j, ports.bank j = i
        · obtain ⟨j,rfl⟩ := hi
          exact (hclean j).2.trans (hblank j).2.symm
        · have hoff : ∀ j, ports.bank j ≠ i := by simpa only [not_exists] using hi
          exact (hframe₂ i hd hoff).2.trans (hframe i ha hoff).2
  have hvolume : word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length := by
    rw [length_cstream,packedBatch_length a n Fs (by omega)]
    exact hcert.length_le (by omega)
  refine ⟨J,L,v₁,v₂,C,F,R,G,n₁,_,word,hu₂.trans hu₁,hseed,hprofile,he₁,rfl,?_,
    Nat.add_le_add hn₁ (exportClearRegisterBankCost_le ports.bank 850 dst hdst R),
    hwhole,Exec.seq he₁ he₂,?_,hclean,?_,hcert,hstreamsG,hleft,hfinal,hcert.length,hcert.length_le (by omega),hvolume,?_,?_⟩
  · intro depth
    simpa only [Nat.zero_add] using mn_exec_within_shift hw₂ depth
  · rw [hresult,hword,(hframe dst harchiveDst hdst).2]
  · exact (hframe₂ ports.archive harchiveDst.symm (fun j => (ports.archiveOff j).symm)).2.trans harchive
  · rw [hfinal]
    exact mn_consume_appendR_size_nonincreasing v v₂ S ports.archive dst harchiveDst.symm
      _ tail word hsrc hvolume
  · intro i hi hd hiBank
    have hf := hframe₂ i hd hiBank
    have hg := hframe i hi hiBank
    exact ⟨hf.1.trans hg.1,hf.2.trans hg.2⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
