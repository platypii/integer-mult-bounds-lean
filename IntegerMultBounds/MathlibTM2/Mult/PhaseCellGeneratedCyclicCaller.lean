module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSeedLayout
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireGeneratedHeaders

/-! One ordinary dimension bank generates the changing numerical masters,
executes a fitting batch, publishes output, and releases all generated masters. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

noncomputable def generatedProgram (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (dst : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq g.program (.seq (ports.retiredProgram dst hR hQ) (clearWords (List.ofFn g.masters)))

def fixedControls (ports : CyclicComplexCallerLayout T) : List (Fin T) :=
  [ports.count,ports.span,ports.saved,ports.tmp]++List.ofFn ports.controls

theorem generatedProgram_exec (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (hwireL : ports.seedL = g.left) (hwireR : ports.seedR = g.right)
    (hfixed : ∀ r ∈ ports.fixedControls, ∀ i, g.masters i ≠ r)
    (dst : Fin T) (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
    (hmastersDst : ∀ i, g.masters i ≠ dst)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    {B p l s t u target a n : ℕ} [NeZero s] {α d : ℝ}
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,a+n] i < 2^B)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s) :
    let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 boundary.card) 2
    let q := executionPrecision p l stage 2
    let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ i, ‖value p (F i)‖ ≤ 1),
    let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
    let hRs := shiftedComplexComponents_bound p q hqp Fs hF
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
    let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
    ∀ W, 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W →
    ∀ (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4))),
    g.Ready B p u l target s t a n W Fs.length S →
    (∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []) →
    S.R ports.archive = cstream A W (Fs.map (packedInterval a n)).flatten++tail →
    (S.R ports.count).length = Fs.length*n*W → (S.R ports.span).length = n →
    (∀ i, (S.R (ports.controls i)).length = ![W,radius,coreLength s coreWidth k] i) →
    S.R ports.saved = [] → S.R ports.tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (J L : ReplicaHaloProblem s) (v' : HS T Q A U) (E C F : Stacks T A) (steps : ℕ) (word : List (Fin (A+4))),
      v'.user = v.user ∧
      (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedL j)).length = recoverySeedHeader H W Fs.length j) ∧
      (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedR j)).length = recoverySeedHeader K W Fs.length j) ∧
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (ports.small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      (∀ j, (C.R (cachedFactorSeedSource (ports.small ∘ CyclicReplicaPlacement.left.plan.gather) ports.span j)).length =
        cyclicFactorMasterValues p l s t u solveTarget a n j) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget boundary.card ∧
      steps ≤ CyclicSeedLayout.timeCost B p u l target s t a n+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost H K W Fs.length E+
            (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
              Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
                (coreLength s coreWidth k) Rs.length Fs.length))) (Fs.length*n*W)+
        (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (CyclicSeedLayout.workspace B p u l target s t a n+
          ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
            (executionWidth p l stage 2) W boundary.card Rs.length Fs.length radius
            (coreLength s coreWidth k) E C F)) 0
        (ports.generatedProgram g dst hR hQ) (Host.mk v S) steps
        (Host.mk v' {S with R := Function.update (Function.update S.R ports.archive tail) dst (word++S.R dst)}) ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length := by
  dsimp only
  intro Fs hF
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 boundary.card) 2
  let q := executionPrecision p l stage 2
  let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  intro W hW hWin v S tail ready hblank hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  have hfit : a+n ≤ s := by omega
  have hmasterPort (i : Fin 10) : ports.seedL (recoveryMasterPort i) = g.masters i := by
    rw [hwireL]
    exact recoverySeedSources_master g.masters g.precision g.packet g.replicas i
  have hbankOff (i : Fin 10) (j : Fin 909) : g.masters i ≠ ports.bank j := by
    rw [←hmasterPort i]
    exact (ports.seedOff _ j).1
  have harchiveOff (i : Fin 10) : g.masters i ≠ ports.archive := by
    rw [←hmasterPort i]
    exact (ports.seedArchive _).1
  obtain ⟨v₁,E,n₁,hu₁,hn₁,he₁,hleftSeed,hrightSeed,hI,hO,hL,hframe⟩ :=
    g.program_exec (body := body) axis ha hfit hbandRoom hgeometryRoom hprecisionRoom hvaluesFit Rs hRs W Fs.length v S ready
  rw [←hwireL] at hleftSeed
  rw [←hwireR] at hrightSeed
  have hscalar (r : Fin T) (hr : r ∈ ports.fixedControls) : E.R r = S.R r := hframe r (hfixed r hr)
  obtain ⟨J,L,vm,v₂,C,F,R,G,runSteps,n₂,word,hu₂,hseed,hfactorValues,hprofile,heRun,hnRun,hcleanup,
    hn₂,he₂,hex₂,hword,hclean,harchive,hcert,hstreams,hleftG,hfinal,hlen,hvol,hpayload,hstock,houtside⟩ :=
    ports.retiredProgram_exec (body := body) dst hdst harchiveDst hR hQ hA axis ha hn hleftRoom hrightRoom
      coreWidth k radius hleft haCore hnCore hright Fs hF W hW hWin v₁ E tail
      (by intro i; exact ⟨(congrFun hL _).trans (hblank i).1,(hframe _ (fun j => hbankOff j i)).trans (hblank i).2⟩)
      hleftSeed hrightSeed
      ((hframe ports.archive harchiveOff).trans hsrc)
      (by rw [hscalar _ (by simp [fixedControls])]; exact hcount)
      (by rw [hscalar _ (by simp [fixedControls])]; exact hspan)
      (by intro i; rw [hscalar _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))]; exact hcontrols i)
      ((hscalar _ (by simp [fixedControls])).trans hsaved) ((hscalar _ (by simp [fixedControls])).trans htmp)
      localityTarget qRef Y hqRef hwindow hY
  let D : Stacks T A := {S with R := Function.update (Function.update S.R ports.archive tail) dst (word++S.R dst)}
  have hdstStable : E.R dst = S.R dst := hframe dst hmastersDst
  have hbaseBlank (i : Fin 10) : D.R (g.masters i) = [] := by
    simp only [D,Function.update_of_ne (hmastersDst i),Function.update_of_ne (harchiveOff i),ready.masters i]
  have hgenerated (i : Fin 10) : (G.R (g.masters i)).length = inverseMasterValues p u l target s t a (a+n) i := by
    have hm : recoveryMasterPort i ∈ recoverySeedHeaderPorts := recoverySeedHeaderPorts_perm.mem_iff.mpr
      (List.mem_append_left _ (List.mem_ofFn.mpr ⟨i,rfl⟩))
    have hv := hleftSeed _ hm
    rw [hmasterPort,recoverySeedHeader_master] at hv
    rw [(houtside _ (harchiveOff i) (hmastersDst i) (fun j => (hbankOff i j).symm)).2]
    exact hv.trans (congrFun (axis.fittingCyclicLeftMasterValues target a n ha hfit Rs hRs) i)
  have hfinalFrame (r : Fin T) (hr : ∀ i, g.masters i ≠ r) : G.R r = D.R r := by
    rw [hfinal,hdstStable]
    change Function.update (Function.update E.R ports.archive tail) dst (word++S.R dst) r = _
    by_cases hd : r = dst
    · subst r; simp [D]
    · by_cases ha' : r = ports.archive
      · subst r; simp [D,hd]
      · simp only [D,Function.update_of_ne hd,Function.update_of_ne ha']
        exact hframe r hr
  obtain ⟨v₃,hu₃,he₃⟩ := retireGeneratedHeaders_exec (body := body) g.masters g.mastersInjective
    (inverseMasterValues p u l target s t a (a+n)) v₂ D G hbaseBlank hgenerated
    (hstreams.1.trans hI) (hstreams.2.trans hO) (hleftG.trans hL) hfinalFrame 0
  have hnumClear := ExecWithin.seq he₂ (he₃.mono (by
    intro d z hz
    have hpeak := he₂.final
    omega))
  have hwhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ he₁ hnumClear
  refine ⟨J,L,v₃,E,C,F,n₁+(n₂+(2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21)),word,
    hu₃.trans (hu₂.trans hu₁),hleftSeed,hrightSeed,hseed,hfactorValues,hprofile,?_,hwhole,hcert,hpayload⟩
  have htime := Nat.add_le_add hn₁ (Nat.add_le_add_right hn₂
    (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21))
  simpa only [Nat.add_assoc] using htime

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
