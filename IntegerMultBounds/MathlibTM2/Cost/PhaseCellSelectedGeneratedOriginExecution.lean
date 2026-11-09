module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFittingCyclicWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedOriginReaderWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedOriginCyclicCaller
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicSeedCosts
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeneratedOriginTimeCost

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
open CyclicReplicaPlacement CyclicComplexCallerLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedGeneratedOriginCyclicProgram_exec
    (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (hwireL : ports.seedL = g.left) (hwireR : ports.seedR = g.right)
    (hfixed : ∀ r ∈ ports.fixedControls, ∀ i, g.masters i ≠ r)
    (dst : Fin T) (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
    (hmastersDst : ∀ i, g.masters i ≠ dst)
    (width origins binary work readerSaved readerTmp : Fin T)
    (hreader : [width,ports.span,origins,binary,g.source 6,g.source 7,work,readerSaved,readerTmp].Nodup)
    (hretained : ∀ r, g.retained r → origins ≠ r ∧ g.source 6 ≠ r ∧ g.source 7 ≠ r)
    (hprotected : ∀ r, ports.generatedReaderProtected dst r →
      r ≠ origins ∧ r ≠ g.source 6 ∧ r ≠ g.source 7)
    ,
    let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    ∀ (B u target a n : ℕ) (α d : ℝ)
    (axis : RecoveryAxisBounds s t p u l α d) (ha : a < s) (hn : n ≤ s)
    (hleftRoom : min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hrightRoom : n-min n (s-a)+PhaseCellBand.width p u ≤ s)
    (hu : u ≤ p) (htarget : target ≤ ct*p)
    (hBmax : B ≤ cZ*p) (hlmax : l ≤ cZ*p) (htargetMax : target ≤ cZ*p)
    (hbandMax : PhaseCellBand.width p u ≤ cZ*p)
    (hbandRoom : 64*(p+1)+u < 2^B)
    (hgeometryRoom : 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B)
    (hprecisionRoom : inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card (PhaseCellBand.width p u) < 2^B)
    (hvaluesFit : ∀ i : Fin 8, ![p,u,l,target,s,t,a,a+n] i < 2^B)
    (coreWidth k radius : ℕ) (hleft : radius ≤ coreStart coreWidth k)
    (haCore : a = coreStart coreWidth k-radius) (hnCore : n = coreLength s coreWidth k+2*radius)
    (hright : coreStart coreWidth k+coreLength s coreWidth k+radius ≤ s),
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
    ∀ W V, a < 2^V → 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W → W ≤ cW*p → V ≤ cV*p →
    ∀ (v : HS T Q A U) (S : Stacks T A) (originTail tail : List (Fin (A+4))),
    g.Ready B p u l target s t 0 0 W Fs.length S →
    (S.R width).length = V → S.R origins = binSyms V a++originTail →
    (∀ r ∈ [binary,g.source 6,g.source 7,work,readerSaved,readerTmp], S.R r = []) →
    (∀ i, S.L (ports.bank i) = [] ∧ S.R (ports.bank i) = []) →
    S.R ports.archive = cstream A W (Fs.map (packedInterval a n)).flatten++tail →
    (S.R ports.count).length = Fs.length*n*W → (S.R ports.span).length = n →
    (∀ i, (S.R (ports.controls i)).length = ![W,radius,coreLength s coreWidth k] i) →
    S.R ports.saved = [] → S.R ports.tmp = [] →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    cyclicPrincipalVertices s a n = (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget k).halo →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun i => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F i)).re)) →
    ∃ (v' : HS T Q A U) (steps : ℕ) (word : List (Fin (A+4))) (runTime reserve : ℕ),
      v'.user = v.user ∧
      steps ≤ generatedOriginTimeCost (A := A) (U := U) hR hQ B H K
        p u l t a n target q W radius (coreLength s coreWidth k) Rs.length Fs.length V ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*
          Fs.length*t*p+45*Sizes.T m)) 0
        (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ)
        (Host.mk v S) steps
        (Host.mk v' {S with R := (Function.update (Function.update (Function.update S.R origins originTail)
          ports.archive tail) dst (word++S.R dst))}) ∧
    ∃ (J L : ReplicaHaloProblem s) (E C F : Stacks T A),
      (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedL j)).length = recoverySeedHeader H W Fs.length j) ∧
      (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedR j)).length = recoverySeedHeader K W Fs.length j) ∧
      CyclicFactorSeedInput p l s t u solveTarget a n [] (embStk (ports.small ∘ CyclicReplicaPlacement.factorReg) F) ∧
      (∀ j, (C.R (cachedFactorSeedSource (ports.small ∘ CyclicReplicaPlacement.left.plan.gather) ports.span j)).length =
        cyclicFactorMasterValues p l s t u solveTarget a n j) ∧
      CyclicSecondInteriorProfile H K J L p solveTarget boundary.card ∧
      runTime = CyclicSeedLayout.timeCost B p u l target s t a n+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost H K W Fs.length E+
            (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
              Cost.cyclicComplexCoreTimeCost H K p u l t a n target q W radius
                (coreLength s coreWidth k) Rs.length Fs.length))) (Fs.length*n*W)+
        (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21) ∧
      reserve = CyclicSeedLayout.workspace B p u l target s t a n+
          ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
            (executionWidth p l stage 2) W boundary.card Rs.length Fs.length radius
            (coreLength s coreWidth k) E C F ∧
      PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word ∧
      word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length := by
  filter_upwards [selectedFittingCyclicWorkspace_le (A := A) (U := U) (T := T) hR hQ ct cW,
    selectedOriginReaderWorkspace_le cV, selectedCyclicSeedWorkspace_le cZ hcZ] with m hreserve hreaderBudget hseedBudget
  intro h i _ ports g hwireL hwireR hfixed dst hdst harchiveDst hmastersDst
    width origins binary work readerSaved readerTmp hreader hretained hprotected
  dsimp only
  intro B u target a n α d axis ha hn hleftRoom hrightRoom hu htarget
    hBmax hlmax htargetMax hbandMax hbandRoom hgeometryRoom hprecisionRoom hvaluesFit
    coreWidth k radius hleft haCore hnCore hright Fs hF
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 boundary.card) 2
  let q := executionPrecision p l stage 2
  have hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  intro W V hfit hW hWin hWmax hVmax v S originTail tail ready hwidth horigins hreaderBlank
    hblank hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  obtain ⟨v',steps,word,runTime,reserve,hu',htime,hwithin,J,L,E,C,F,hEL,hER,hseed,hvalues,hprofile,htotalTime,hworkspace,hcert,hlen⟩ :=
    ports.generatedOriginProgram_exec (body := body) g hwireL hwireR hfixed dst hdst harchiveDst hmastersDst
      width origins binary work readerSaved readerTmp hreader hretained hprotected hR hQ hA
      axis ha hn hleftRoom hrightRoom hbandRoom hgeometryRoom hprecisionRoom hvaluesFit
      coreWidth k radius hleft haCore hnCore hright Fs hF W V hfit hW hWin v S originTail tail ready
      hwidth horigins hreaderBlank hblank hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  have hbudget := hreserve h i ports E C F u target a n W Fs.length radius (coreLength s coreWidth k)
    α d axis ha hn hu htarget (by omega) (by dsimp only [s]; omega) hWmax (by omega)
    Rs hRs (by simp only [Rs,List.length_map,complexComponentFields_length]) hEL hER hvalues hseed J L hprofile
  have hread := hreaderBudget h i V a n hVmax (by omega) hn
  have hpZ : p ≤ cZ*p := by simpa using Nat.mul_le_mul_right p hcZ
  have hgeneration := hseedBudget h i B u l target a n hBmax (hu.trans hpZ) hlmax htargetMax (by omega) hbandMax
  have htotal : 3*readSupplierEndpointsCost V a n+reserve ≤
      fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m := by
    rw [hworkspace]
    change 3*readSupplierEndpointsCost V a n+
      (CyclicSeedLayout.workspace B p u l target s t a n+
        ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
          (executionWidth p l stage 2) W boundary.card Rs.length Fs.length radius (coreLength s coreWidth k) E C F) ≤
      fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m
    have hsum := Nat.add_le_add hread (Nat.add_le_add hgeneration hbudget)
    change 3*readSupplierEndpointsCost V a n+
      (CyclicSeedLayout.workspace B p u l target s t a n+
        ports.workspace (U := U) H K J L hR hQ p u l t a n solveTarget q
          (executionWidth p l stage 2) W boundary.card Rs.length Fs.length radius (coreLength s coreWidth k) E C F) ≤
      Sizes.T m+(Sizes.T m+(fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+43*Sizes.T m)) at hsum
    omega
  have hcountH : H.Fs.length = 2*Fs.length := by
    change Rs.length = 2*Fs.length
    simp only [Rs,List.length_map,complexComponentFields_length]
  have hcountK : K.Fs.length = 2*Fs.length := by
    change Rs.length = 2*Fs.length
    simp only [Rs,List.length_map,complexComponentFields_length]
  have hinput := fittingCyclicInputTime_affine ports H K W Fs.length E hcountH hcountK hEL hER
  have hfactor := fittingCyclicFactorTime_eq ports C F p l t u solveTarget a n hvalues hseed
  have htimeFixed : steps ≤ generatedOriginTimeCost (A := A) (U := U) hR hQ B H K
      p u l t a n target q W radius (coreLength s coreWidth k) Rs.length Fs.length V := by
    rw [htotalTime] at htime
    change steps ≤ readSupplierEndpointsCost V a n+
      (CyclicSeedLayout.timeCost B p u l target s t a n+
        retiredTimeCost (A := A) (U := U) hR hQ
          (ports.inputTimeCost H K W Fs.length E+
            (ports.factorTimeCost s t p u a n C F+((4*(W+radius+coreLength s coreWidth k)+13)+
              cyclicComplexCoreTimeCost H K p u l t a n target q W radius
                (coreLength s coreWidth k) Rs.length Fs.length))) (Fs.length*n*W)+
        (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21))+
      (2*(a+(a+n))+5) at htime
    rw [hinput,hfactor] at htime
    exact htime
  refine ⟨v',steps,word,runTime,reserve,hu',htimeFixed,?_,J,L,E,C,F,hEL,hER,hseed,hvalues,hprofile,htotalTime,hworkspace,hcert,hlen⟩
  exact hwithin.mono (by intro depth z hz; exact hz.trans (Nat.add_le_add_left htotal _))

end IntegerMultBounds.MathlibTM2.Cost
