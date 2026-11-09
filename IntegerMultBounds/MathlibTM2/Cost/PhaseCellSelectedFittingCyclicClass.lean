module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreGatherCyclicScan
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAttachedCyclicScanTime

/-! Execute one fitting class with the concrete generated callback. Ordinary
headers and blank workspace survive each iteration; numerical seeds do not. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement CyclicComplexCallerLayout
variable {T Q A : ℕ} {P U : Type} {body : P → Pr P T Q A U}

theorem selectedFittingCyclicClass_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (ct cW cV cZ : ℕ) (hcZ : 1 ≤ cZ) :
    let b := 8*executionPush (A := A) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
    ∀ (ports : CyclicComplexCallerLayout T) (g : CyclicSeedLayout T)
      (dst width origins binary work readerSaved readerTmp count saved : Fin T),
    ports.seedL = g.left → ports.seedR = g.right →
    (∀ r ∈ ports.fixedControls, ∀ j, g.masters j ≠ r) →
    (∀ j, ports.bank j ≠ dst) → dst ≠ ports.archive → (∀ j, g.masters j ≠ dst) →
    [count,saved,origins,ports.archive,dst].Nodup →
    [width,ports.span,origins,binary,g.source 6,g.source 7,work,readerSaved,readerTmp].Nodup →
    (∀ r, g.retained r → origins ≠ r ∧ g.source 6 ≠ r ∧ g.source 7 ≠ r) →
    (∀ r, ports.generatedReaderProtected dst r → r ≠ origins ∧ r ≠ g.source 6 ∧ r ≠ g.source 7) →
    (∀ r, ports.classProtected g width binary work readerSaved readerTmp r → r ≠ count ∧ r ≠ saved) →
    (∀ r, ports.classProtected g width binary work readerSaved readerTmp r →
      r ≠ origins ∧ r ≠ ports.archive ∧ r ≠ dst) →
    let p := Sizes.p m
    let s := Sizes.s m i
    let t := Sizes.t m i
    let l := haloInverseRingLog s t
    ∀ (B u target n coreWidth depth W V : ℕ) (α d : ℝ)
      (axis : RecoveryAxisBounds s t p u l α d) (hn : n ≤ s),
    let radius := depth*PhaseCellBand.width p u
    let jobs := coreGatherIndices s coreWidth radius n
    let cs := jobs.attach
    let index := fun c : {k // k ∈ jobs} => c.val
    let a := fun c : {k // k ∈ jobs} => coreStart coreWidth c.val-radius
    let ha := fun c : {k // k ∈ jobs} => coreGatherOrigin_lt c.property

    0 < coreWidth → coreWidth ≤ s → radius ≤ coreWidth →
    s/(t-s)+1 ≤ coreWidth → p^2+(PhaseCellBand.width p u)^2 ≤ coreWidth →
    u ≤ p → target ≤ ct*p → B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p →
    PhaseCellBand.width p u ≤ cZ*p →
    64*(p+1)+u < 2^B → 8*(t+1)^2+2*PhaseCellBand.width p u+8 < 2^B →
    (∀ c ∈ cs, min n (s-a c)+PhaseCellBand.width p u ≤ s ∧
      n-min n (s-a c)+PhaseCellBand.width p u ≤ s) →
    (∀ c ∈ cs, inversePrecisionRoom p l target
      (haloBoundary s t (PhaseCellBand.width p u) (a c) (a c+n)).card (PhaseCellBand.width p u) < 2^B) →
    (∀ c ∈ cs, ∀ j : Fin 8, ![p,u,l,target,s,t,a c,a c+n] j < 2^B) →
    let boundary := fun c => cyclicPrincipalBoundary s t (PhaseCellBand.width p u) (a c) n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := fun c => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (boundary c).card) 2
    let q := fun c => executionPrecision p l (stage c) 2
    let hqp := fun c => (show p+1 ≤ q c by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega)
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1),
    let Rs := fun c => (complexComponentFields Fs).map (fun F j => (2 : GaussianInt)^(q c-p-1)*F j)
    let hRs := fun c => shiftedComplexComponents_bound p (q c) (hqp c) Fs hF
    let H := fun c => axis.cyclicLeftReplicaProblem (stage c) 2 (a c) n (ha c) (Rs c) (hRs c)
    let K := fun c => axis.cyclicRightReplicaProblem (stage c) 2 (a c) n hn (Rs c) (hRs c)
    2*p+13 ≤ W → (∀ c ∈ cs, executionWidth p l (stage c) 2 ≤ W) → W ≤ cW*p → V ≤ cV*p →
    (∀ c ∈ cs, a c < 2^V) →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    (∀ c ∈ cs, cyclicPrincipalVertices s (a c) n =
      (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget (index c)).halo) →
    (∀ F ∈ complexComponentFields Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun j => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F j)).re)) →
    let time := fun c => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H c) (K c)
      p u l t (a c) n target (q c) W radius (coreLength s coreWidth (index c)) (Rs c).length Fs.length V
    ∀ (v : HS T Q A U) (S : Stacks T A) (originTail tail : List (Fin (A+4))),
    ports.ClassReady g width binary work readerSaved readerTmp B p u l target s t W V Fs.length n radius (n-2*radius) S →
    S.R origins = cs.flatMap (fun c => binSyms V (a c))++originTail →
    S.R ports.archive = cs.flatMap (fun c => cstream A W (Fs.map (packedInterval (a c) n)).flatten)++tail →
    (S.R count).length = cs.length → S.R saved = [] →
    ∃ v' steps outputs, v'.user = v.user ∧ steps ≤ (cs.map time).sum+5*cs.length+4 ∧
      (steps : ℝ) ≤ (8*(b : ℝ)+3)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) ∧
      List.Forall₂ (fun k word => PackedNormalizedOutput p W target coreWidth k localityTarget Fs Y word) jobs outputs ∧
      List.Forall₂ (fun c word =>
        PackedNormalizedOutput p W target coreWidth (index c) localityTarget Fs Y word ∧
        ∃ (J L : ReplicaHaloProblem s) (E C F : Stacks T A),
          (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedL j)).length = recoverySeedHeader (H c) W Fs.length j) ∧
          (∀ j ∈ recoverySeedHeaderPorts, (E.R (ports.seedR j)).length = recoverySeedHeader (K c) W Fs.length j) ∧
          CyclicFactorSeedInput p l s t u solveTarget (a c) n []
            (embStk (ports.small ∘ CyclicReplicaPlacement.factorReg) F) ∧
          (∀ j, (C.R (cachedFactorSeedSource (ports.small ∘ CyclicReplicaPlacement.left.plan.gather) ports.span j)).length =
            cyclicFactorMasterValues p l s t u solveTarget (a c) n j) ∧
          CyclicSecondInteriorProfile (H c) (K c) J L p solveTarget (boundary c).card) cs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        (fittingCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m)) 0
        (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
        (Host.mk v S) steps (Host.mk v' {S with R := (Function.update
          (Function.update (Function.update S.R origins originTail) ports.archive tail) dst
          (outputs.reverse.flatten++S.R dst))}) := by
  classical
  dsimp only
  obtain ⟨B₀,hB₀,hfast⟩ := selectedAttachedCyclicScan_time_le (T := T) (A := A) (U := U)
    hR hQ ct cW cV cZ hcZ
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [selectedCoreGatherCyclicScan_exec (T := T) (A := A) (U := U) (body := body)
    hR hQ hA ct cW cV cZ hcZ,hfast] with m hscan hfast
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
  intro B u target n coreWidth depth W V α d axis hn hw hwidth hguard hcell hprepare
    hu htarget hB hl htargetMax hbandMax hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit
    Fs hF hW hWin hWmax hVmax hfit localityTarget qRef Y hqRef hwindow hY
    v S originTail tail ready horigins hsource hcount hsaved
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let radius := depth*PhaseCellBand.width p u
  let jobs := coreGatherIndices s coreWidth radius n
  let index := fun c : {k // k ∈ jobs} => c.val
  let a := fun c : {k // k ∈ jobs} => coreStart coreWidth c.val-radius
  have ha (c : {k // k ∈ jobs}) : a c < s := coreGatherOrigin_lt c.property
  let boundary := fun c => cyclicPrincipalBoundary s t (PhaseCellBand.width p u) (a c) n
  let solveTarget := boundaryRecoveryTarget p (target+1)
  let stage := fun c => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (boundary c).card) 2
  let q := fun c => executionPrecision p l (stage c) 2
  have hqp (c) : p+1 ≤ q c := by dsimp only [q,executionPrecision,executionExponent,inputExponent]; omega
  let Rs := fun c => (complexComponentFields Fs).map (fun F j => (2 : GaussianInt)^(q c-p-1)*F j)
  let hRs := fun c => shiftedComplexComponents_bound p (q c) (hqp c) Fs hF
  let H := fun c => axis.cyclicLeftReplicaProblem (stage c) 2 (a c) n (ha c) (Rs c) (hRs c)
  let K := fun c => axis.cyclicRightReplicaProblem (stage c) 2 (a c) n hn (Rs c) (hRs c)
  let time := fun c => generatedOriginTimeCost (A := A) (U := U) hR hQ B (H c) (K c)
    p u l t (a c) n target (q c) W radius (coreLength s coreWidth (index c)) (Rs c).length Fs.length V
  obtain ⟨v',steps,outputs,hu',ht,hnatural,hcert,he⟩ :=
    hscan h i ports g dst width origins binary work readerSaved readerTmp count saved
      hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
      B u target n coreWidth radius W V α d axis hn hu htarget hB hl htargetMax hbandMax
      hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit Fs hF hW hWin hWmax hVmax hfit
      localityTarget qRef Y hqRef hwindow hY v S originTail tail ready horigins hsource hcount hsaved
  have hper := (List.forall₂_and_left _ _).mp
    (hcert.imp (by intro c word hc; exact ⟨hc.2,hc.1⟩))
  have hreplicas (c) : (Rs c).length = 2*Fs.length := by
    simp only [Rs,List.length_map,complexComponentFields_length]
  have htimeBound := hfast h i axis ports S coreWidth depth n Fs.length target W V B hu htarget
    hw hwidth hguard hcell hprepare H K
    (by
      intro c
      refine ⟨ha c,hn,Rs c,hRs c,hreplicas c,rfl,rfl⟩)
    hW hWmax hVmax
    (by intro c; exact hper.1 c (List.mem_attach _ c))
    hB hl htargetMax hbandMax steps (by
      change steps ≤ (jobs.attach.map time).sum+5*jobs.attach.length+4 at ht
      simpa only [time,hreplicas,List.length_attach] using ht)
  exact ⟨v',steps,outputs,hu',ht,htimeBound,hnatural,hcert,he⟩

end IntegerMultBounds.MathlibTM2.Cost
