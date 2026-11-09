module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetiredCyclicComplexCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireRecoverySeedEndpoints
public import IntegerMultBounds.MathlibTM2.Host.ConsumeScan

/-! One fitting callback consumes its binary origin and payload, executes the
concrete numerical caller, and retires both changing external seed words. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

def readerProtected (ports : CyclicComplexCallerLayout T) (dst r : Fin T) : Prop :=
  (∃ i, ports.bank i = r) ∨ (∃ i, ports.controls i = r) ∨
  (∃ i ∈ recoverySeedHeaderPorts, ports.seedR i = r) ∨
  r ∈ [ports.archive,ports.count,ports.span,ports.saved,ports.tmp,dst]

noncomputable def originProgram (ports : CyclicComplexCallerLayout T) (dst : Fin T)
    (width origins binary work readerSaved readerTmp : Fin T)
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  .seq (readRecoverySeedEndpoints (P := P) (Q := Q) (A := A) (U := U) width ports.span origins binary ports.seedL work readerSaved readerTmp)
    (.seq (ports.retiredProgram dst hR hQ) (retireRecoverySeedEndpoints (P := P) (Q := Q) (A := A) (U := U) ports.seedL))

theorem originProgram_exec (ports : CyclicComplexCallerLayout T) (dst : Fin T)
    (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
    (width origins binary work readerSaved readerTmp : Fin T)
    (hreader : [width,ports.span,origins,binary,ports.seedL 111,ports.seedL 113,work,readerSaved,readerTmp].Nodup)
    (hprotected : ∀ r, ports.readerProtected dst r →
      r ≠ origins ∧ r ≠ ports.seedL 111 ∧ r ≠ ports.seedL 113)
    (hseedOff : ∀ i ∈ recoverySeedHeaderPorts, i ≠ 111 → i ≠ 113 →
      ports.seedL i ≠ origins ∧ ports.seedL i ≠ ports.seedL 111 ∧ ports.seedL i ≠ ports.seedL 113)
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
    ∀ (W V : ℕ), a < 2^V → 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W →
    ∀ (v : HS T Q A U) (S : Stacks T A) (originTail tail : List (Fin (A+4))),
    (∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []) →
    (S.R width).length = V → S.R origins = binSyms V a++originTail →
    (∀ r ∈ [binary,ports.seedL 111,ports.seedL 113,work,readerSaved,readerTmp], S.R r = []) →
    (∀ i ∈ recoverySeedHeaderPorts, i ≠ 111 → i ≠ 113 →
      (S.R (ports.seedL i)).length = recoverySeedHeader H W Fs.length i) →
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
    let E := recoverySeedEndpointState ports.seedL a (a+n) {S with R := Function.update S.R origins originTail}
    ∃ (J L : ReplicaHaloProblem s) (C F R : Stacks T A) (vstart vm v' : HS T Q A U) (readSteps runSteps steps : ℕ)
      (word : List (Fin (A+4))),
      v'.user = v.user ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      Exec body (readRecoverySeedEndpoints width ports.span origins binary ports.seedL work readerSaved readerTmp)
        (Host.mk v S) readSteps (Host.mk vstart E) ∧
      Exec body (ports.program hR hQ) (Host.mk vstart E) runSteps (Host.mk vm R) ∧
      steps ≤ readSupplierEndpointsCost V a n+
        ((ports.inputTimeCost H K W Fs.length E+
          (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
            Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
              (coreLength s coreWidth k) Rs.length Fs.length)))+
          (8*registerBankStock (embStk ports.bank R)+4*909+5))+(2*(a+(a+n))+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (3*readSupplierEndpointsCost V a n+
        (fittingCyclicInputPush (Q := Q) (A := A) (U := U)*ports.inputTimeCost H K W Fs.length E+
          (cyclicFactorPreparationPush (Q := Q) (A := A) (U := U)*ports.factorTimeCost s t p u a n C F+
            (2*(4*(W+radius+coreLength s coreWidth k)+13)+
              cyclicComplexCoreWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
                p u l t a n solveTarget q (executionWidth p l stage 2) W B.card
                Rs.length Fs.length radius (coreLength s coreWidth k)))))) 0
        (ports.originProgram dst width origins binary work readerSaved readerTmp hR hQ)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          ports.archive tail) dst (word++S.R dst))}) ∧
      Exec body (ports.originProgram dst width origins binary work readerSaved readerTmp hR hQ)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          ports.archive tail) dst (word++S.R dst))}) ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length := by
  dsimp only
  intro Fs hF W V hfit hW hWin v S originTail tail hblank hwidth horigins hreaderBlank
    hvaluesL hvaluesR hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l stage 2
  have hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  have hfitInterval : a+n ≤ s := by omega
  have hHorigin : H.origin = a := rfl
  have hHspan : H.span = n := by change min n (s-a) = n; omega
  obtain ⟨vi,m,hui,hm,heRead,hheaders⟩ := readRecoverySeedEndpoints_exec (body := body)
    H H rfl rfl rfl rfl rfl rfl W Fs.length V width ports.span origins binary ports.seedL
    work readerSaved readerTmp hreader hseedOff hfit originTail v S hwidth
    (by simpa only [hHspan] using hspan) horigins hreaderBlank hvaluesL 0
  let E := recoverySeedEndpointState ports.seedL a (a+n) {S with R := Function.update S.R origins originTail}
  have hread : Exec body (readRecoverySeedEndpoints width ports.span origins binary ports.seedL work readerSaved readerTmp)
      (Host.mk v S) m (Host.mk vi E) := by
    simpa only [hHspan,hHorigin,E,recoverySeedEndpointState] using heRead.toExec
  have hstable (r : Fin T) (hr : ports.readerProtected dst r) : E.R r = S.R r := by
    obtain ⟨ho,ha,hb⟩ := hprotected r hr
    simp only [E,recoverySeedEndpointState,Function.update_of_ne hb,Function.update_of_ne ha,
      Function.update_of_ne ho]
  have hbank (i : Fin 909) : E.L (ports.bank i) = [] ∧ E.R (ports.bank i) = [] := by
    exact ⟨(hblank i).1,(hstable _ (.inl ⟨i,rfl⟩)).trans (hblank i).2⟩
  have hscalar (r : Fin T) (hr : r ∈ [ports.archive,ports.count,ports.span,ports.saved,ports.tmp,dst]) :
      E.R r = S.R r := hstable r (.inr (.inr (.inr hr)))
  obtain ⟨J,L,vm,vf,C,F,R,G,runSteps,numericalSteps,word,huf,hseed,hprofile,heRun,hsteps,hcleanup,
    htime,hretiredWithin,heNumerical,hword,hclean,harchive,hcert,hstreams,hleft,hfinal,hlen,hvol,hpayload,hstock,hframe⟩ :=
    ports.retiredProgram_exec (body := body) dst hdst harchiveDst hR hQ hA axis ha hn hleftRoom hrightRoom
      coreWidth k radius hleft haCore hnCore hright Fs hF W hW hWin vi E tail hbank
      (by simpa only [hHspan,hHorigin,E,recoverySeedEndpointState] using hheaders)
      (by intro i hi; rw [hstable _ (.inr (.inr (.inl ⟨i,hi,rfl⟩)))]; exact hvaluesR i hi)
      (by rw [hscalar _ (by simp)]; exact hsrc)
      (by rw [hscalar _ (by simp)]; exact hcount)
      (by rw [hscalar _ (by simp)]; exact hspan)
      (by intro i; rw [hstable _ (.inr (.inl ⟨i,rfl⟩))]; exact hcontrols i)
      (by rw [hscalar _ (by simp)]; exact hsaved)
      (by rw [hscalar _ (by simp)]; exact htmp) localityTarget qRef Y hqRef hwindow hY
  let D : Stacks T A := {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
      ports.archive tail) dst (word++S.R dst))}
  have hdstStable := hscalar dst (by simp)
  have hG : G = recoverySeedEndpointState ports.seedL a (a+n) D := by
    rw [hfinal,hdstStable]
    let M : Stacks T A := {S with R := Function.update S.R origins originTail}
    have hA := recoverySeedEndpointState_updateR ports.seedL a (a+n) M ports.archive tail
      (hprotected ports.archive (.inr (.inr (.inr (by simp))))).2.1
      (hprotected ports.archive (.inr (.inr (.inr (by simp))))).2.2
    have hAR := congrArg (fun Z : Stacks T A => Z.R) hA
    change Function.update E.R ports.archive tail = _ at hAR
    change {{E with R := Function.update E.R ports.archive tail} with R :=
      (Function.update (Function.update E.R ports.archive tail) dst (word++S.R dst))} = _
    rw [hA,hAR]
    exact recoverySeedEndpointState_updateR ports.seedL a (a+n)
      {M with R := Function.update M.R ports.archive tail} dst (word++S.R dst)
      (hprotected dst (.inr (.inr (.inr (by simp))))).2.1
      (hprotected dst (.inr (.inr (.inr (by simp))))).2.2
  have hr := hreader
  regs_ne hr
  have hDblank (i : Fin 392) (hi : i = 111 ∨ i = 113) : D.R (ports.seedL i) = [] := by
    have harchive := hprotected ports.archive (.inr (.inr (.inr (by simp))))
    have hdst := hprotected dst (.inr (.inr (.inr (by simp))))
    rcases hi with rfl | rfl <;>
      simp_all [D,Function.update_of_ne,ne_comm]
  obtain ⟨v',hu',heClear⟩ := retireRecoverySeedEndpoints_exec (body := body) ports.seedL
    (by assumption) a (a+n) vf D (hDblank 111 (.inl rfl)) (hDblank 113 (.inr rfl)) 0
  rw [←hG] at heClear
  have hretiredClear := ExecWithin.seq hretiredWithin
    (heClear.mono (by
      intro d z hz
      have hpeak := hretiredWithin.final
      omega))
  have hreaderWithin : ExecWithin body
      (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+3*readSupplierEndpointsCost V a n) 0
      (readRecoverySeedEndpoints width ports.span origins binary ports.seedL work readerSaved readerTmp)
      (Host.mk v S) m (Host.mk vi E) := by
    simpa only [hHspan,hHorigin,E,recoverySeedEndpointState] using heRead
  have hwhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hreaderWithin hretiredClear
  refine ⟨J,L,C,F,R,vi,vm,v',m,runSteps,m+(numericalSteps+(2*(a+(a+n))+5)),word,
    hu'.trans (huf.trans hui),hprofile,hread,heRun,?_,
    hwhole,Exec.seq hread (Exec.seq heNumerical heClear.toExec),hcert,hpayload⟩
  have hm' : m ≤ readSupplierEndpointsCost V a n := by simpa only [hHspan,hHorigin] using hm
  have hb := Nat.add_le_add hm' (Nat.add_le_add_right htime (2*(a+(a+n))+5))
  simpa only [Nat.add_assoc] using hb

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
