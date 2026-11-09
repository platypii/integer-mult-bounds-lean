module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedOriginReaderWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOriginCyclicComplexCaller

/-! Correctness, the actual time ledger and selected peak space concern the
same execution from ordinary complex streams and scalar headers. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open CyclicReplicaPlacement
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedOriginCyclicProgram_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (ct cW cV : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (ports : CyclicComplexCallerLayout T) (dst : Fin T)
    (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
    (width origins binary work readerSaved readerTmp : Fin T)
    (hreader : [width,ports.span,origins,binary,ports.seedL 111,ports.seedL 113,work,readerSaved,readerTmp].Nodup)
    (hprotected : ∀ r, ports.readerProtected dst r →
      r ≠ origins ∧ r ≠ ports.seedL 111 ∧ r ≠ ports.seedL 113)
    (hseedOff : ∀ i ∈ recoverySeedHeaderPorts, i ≠ 111 → i ≠ 113 →
      ports.seedL i ≠ origins ∧ ports.seedL i ≠ ports.seedL 111 ∧ ports.seedL i ≠ ports.seedL 113),
    let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    ∀ (u target a n : ℕ) (α d : ℝ)
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hu : u ≤ p) (htarget : target ≤ ct*p)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s),
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
    ∀ (W V : ℕ), a < 2^V → 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W → W ≤ cW*p → V ≤ cV*p →
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
      CyclicFactorSeedInput p l s t u solveTarget a n []
        (embStk (ports.small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      (∀ i, (C.R (cachedFactorSeedSource (ports.small ∘ CyclicReplicaPlacement.left.plan.gather) ports.span i)).length =
        cyclicFactorMasterValues p l s t u solveTarget a n i) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget B.card ∧
      (∀ i ∈ recoverySeedHeaderPorts,
        (E.R (ports.seedL i)).length = recoverySeedHeader H W Fs.length i) ∧
      (∀ i ∈ recoverySeedHeaderPorts,
        (E.R (ports.seedR i)).length = recoverySeedHeader K W Fs.length i) ∧

      Exec body (readRecoverySeedEndpoints width ports.span origins binary ports.seedL work readerSaved readerTmp)
        (Host.mk v S) readSteps (Host.mk vstart E) ∧
      Exec body (ports.program hR hQ) (Host.mk vstart E) runSteps (Host.mk vm R) ∧
      steps ≤ readSupplierEndpointsCost V a n+
        CyclicComplexCallerLayout.retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost H K W Fs.length E+
        (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
          Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
            (coreLength s coreWidth k) Rs.length Fs.length))) (Fs.length*n*W)+(2*(a+(a+n))+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*
          Fs.length*t*p+44*Sizes.T m)) 0
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
  filter_upwards [selectedFittingCyclicWorkspace_le (A := A) (U := U) (T := T) hR hQ ct cW,
    selectedOriginReaderWorkspace_le cV] with m hreserve hreaderBudget
  intro h i _ ports dst hdst harchiveDst width origins binary work readerSaved readerTmp hreader hprotected hseedOff
  dsimp only
  intro u target a n α d axis ha hn hleftRoom hrightRoom hu htarget coreWidth k radius hleft haCore hnCore hright Fs hF
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 B.card) 2
  let q := executionPrecision p l stage 2
  let hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  intro W V hfit hW hWin hWmax hVmax v S originTail tail hblank hwidth horigins hreaderBlank
    hvaluesL hvaluesR hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  let E := recoverySeedEndpointState ports.seedL a (a+n) {S with R := Function.update S.R origins originTail}
  obtain ⟨J,L,C,F,R,vstart,vm,v',readSteps,runSteps,steps,word,hu',hseed,hvalues,hprofile,hEL,hER,
    hread,hrun,htime,hwithin,hex,hcert,hpayload⟩ :=
    ports.originProgram_exec (body := body) dst hdst harchiveDst width origins binary work readerSaved readerTmp
      hreader hprotected hseedOff hR hQ hA axis ha hn hleftRoom hrightRoom coreWidth k radius
      hleft haCore hnCore hright Fs hF W V hfit hW hWin v S originTail tail hblank hwidth horigins hreaderBlank
      hvaluesL hvaluesR hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  have hbudget := hreserve h i ports E C F u target a n W Fs.length radius (coreLength s coreWidth k)
    α d axis ha hn hu htarget (by omega) (by dsimp only [s]; omega) hWmax (by omega)
    Rs hRs (by simp only [Rs,List.length_map,complexComponentFields_length]) hEL hER hvalues hseed J L hprofile
  have hreadBudget := hreaderBudget h i V a n hVmax (by omega) hn
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  have htotal : 3*readSupplierEndpointsCost V a n+
      ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
        (executionWidth p l stage 2) W B.card Rs.length Fs.length radius (coreLength s coreWidth k) E C F ≤
      fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+44*Sizes.T m := by
    have hsum := Nat.add_le_add hreadBudget hbudget
    change 3*readSupplierEndpointsCost V a n+
      ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
        (executionWidth p l stage 2) W B.card Rs.length Fs.length radius (coreLength s coreWidth k) E C F ≤
      Sizes.T m+(fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+43*Sizes.T m) at hsum
    omega
  refine ⟨J,L,C,F,R,vstart,vm,v',readSteps,runSteps,steps,word,hu',hseed,hvalues,hprofile,hEL,hER,
    hread,hrun,htime,?_,hex,hcert,hpayload⟩
  exact hwithin.mono (by
    intro depth z hz
    exact hz.trans (Nat.add_le_add_left htotal _))

end IntegerMultBounds.MathlibTM2.Cost
