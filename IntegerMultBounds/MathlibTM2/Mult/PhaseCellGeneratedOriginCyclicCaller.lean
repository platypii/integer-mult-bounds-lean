module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedCyclicCaller
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReadRunRetire

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

def generatedReaderProtected (ports : CyclicComplexCallerLayout T) (dst r : Fin T) : Prop :=
  (∃ i, ports.bank i = r) ∨ r ∈ ports.fixedControls ∨ r = ports.archive ∨ r = dst

noncomputable def generatedOriginProgram (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (dst width origins binary work saved tmp : Fin T) (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) : Pr P T Q A U :=
  g.readRunRetire width ports.span origins binary work saved tmp (ports.generatedProgram g dst hR hQ)

theorem generatedOriginProgram_exec (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
    (hwireL : ports.seedL = g.left) (hwireR : ports.seedR = g.right)
    (hfixed : ∀ r ∈ ports.fixedControls, ∀ i, g.masters i ≠ r)
    (dst : Fin T) (hdst : ∀ i, ports.bank i ≠ dst) (harchiveDst : dst ≠ ports.archive)
    (hmastersDst : ∀ i, g.masters i ≠ dst)
    (width origins binary work readerSaved readerTmp : Fin T)
    (hreader : [width,ports.span,origins,binary,g.source 6,g.source 7,work,readerSaved,readerTmp].Nodup)
    (hretained : ∀ r, g.retained r → origins ≠ r ∧ g.source 6 ≠ r ∧ g.source 7 ≠ r)
    (hprotected : ∀ r, ports.generatedReaderProtected dst r →
      r ≠ origins ∧ r ≠ g.source 6 ∧ r ≠ g.source 7)
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
    ∀ W V, a < 2^V → 2*p+13 ≤ W → executionWidth p l stage 2 ≤ W →
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
      steps ≤ readSupplierEndpointsCost V a n+runTime+(2*(a+(a+n))+5) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (3*readSupplierEndpointsCost V a n+reserve)) 0
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
  dsimp only
  intro Fs hF W V hfit hW hWin v S originTail tail ready hwidth horigins hreaderBlank
    hblank hsrc hcount hspan hcontrols hsaved htmp localityTarget qRef Y hqRef hwindow hY
  let boundary := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 boundary.card) 2
  let q := executionPrecision p l stage 2
  have hqp : p+1 ≤ q := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := (complexComponentFields Fs).map (fun F i => (2 : GaussianInt)^(q-p-1)*F i)
  let hRs := shiftedComplexComponents_bound p q hqp Fs hF
  let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Rs hRs
  let K := axis.cyclicRightReplicaProblem stage 2 a n hn Rs hRs
  let Cert : ℕ → ℕ → List (Fin (A+4)) → Prop := fun runTime reserve word =>
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
      word.length ≤ (cstream A W (Fs.map (packedInterval a n)).flatten).length
  have hscalar (r : Fin T) (hr : r ∈ ports.fixedControls ∨ r = ports.archive ∨ r = dst) :=
    hprotected r (Or.inr hr)
  apply CyclicSeedLayout.readRunRetire_exec (body := body) g width ports.span origins binary work readerSaved readerTmp
    ports.archive dst hreader hretained
    ⟨(hscalar _ (Or.inr (Or.inl rfl))).2.1,(hscalar _ (Or.inr (Or.inl rfl))).2.2⟩
    (hscalar _ (Or.inr (Or.inr rfl))) hfit originTail tail v S ready hwidth hspan horigins hreaderBlank
    (ports.generatedProgram g dst hR hQ) Cert
  intro vi D hD hready
  have hstable (r : Fin T) (hr : ports.generatedReaderProtected dst r) : D.R r = S.R r := by
    obtain ⟨ho,ha,hb⟩ := hprotected r hr
    rw [hD]
    simp only [Function.update_of_ne hb,Function.update_of_ne ha,Function.update_of_ne ho]
  have hfixedStable (r : Fin T) (hr : r ∈ ports.fixedControls) := hstable r (Or.inr (Or.inl hr))
  have hbank (i : Fin 909) : D.L (ports.bank i) = [] ∧ D.R (ports.bank i) = [] := by
    refine ⟨?_,(hstable _ (Or.inl ⟨i,rfl⟩)).trans (hblank i).2⟩
    rw [hD]; exact (hblank i).1
  obtain ⟨J,L,vm,E,C,F,steps,word,hu,hseedL,hseedR,hseed,hfactor,hprofile,ht,he,hcert,hlen⟩ :=
    ports.generatedProgram_exec (body := body) g hwireL hwireR hfixed dst hdst harchiveDst hmastersDst
      hR hQ hA axis ha hn hleftRoom hrightRoom hbandRoom hgeometryRoom hprecisionRoom hvaluesFit
      coreWidth k radius hleft haCore hnCore hright Fs hF W hW hWin vi D tail hready hbank
      (by rw [hstable _ (Or.inr (Or.inr (Or.inl rfl)))]; exact hsrc)
      (by rw [hfixedStable _ (by simp [fixedControls])]; exact hcount)
      (by rw [hfixedStable _ (by simp [fixedControls])]; exact hspan)
      (by
        intro i
        rw [hfixedStable _ (List.mem_append_right _ (List.mem_ofFn.mpr ⟨i,rfl⟩))]
        exact hcontrols i)
      (by rw [hfixedStable _ (by simp [fixedControls])]; exact hsaved)
      (by rw [hfixedStable _ (by simp [fixedControls])]; exact htmp)
      localityTarget qRef Y hqRef hwindow hY
  exact ⟨vm,steps,word,_,_,hu,ht,he,J,L,E,C,F,hseedL,hseedR,hseed,hfactor,hprofile,rfl,rfl,hcert,hlen⟩

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.CyclicComplexCallerLayout
