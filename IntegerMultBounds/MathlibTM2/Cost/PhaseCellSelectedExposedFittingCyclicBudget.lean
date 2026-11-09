module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedExposedFittingCyclicClass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeometryRealGatherBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicClassOriginSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCoreWidthCharge

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
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem selectedExposedFittingCyclicClass_bounded_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
    (ct cW cV cZ cG cD cCore eCore : ℕ) (hcZ : 1 ≤ cZ)
    (hstates : FixedStreamedBank.stateCount ≤ Q) :
    let b := 8*executionPush (A := (prime+K)) (U := U) hR hQ+1
    ∃ B₀ : ℝ, 0 ≤ B₀ ∧ ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
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
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs.reverse, ∀ j, ‖value p (F j)‖ ≤ 1),
    2*p+13 ≤ W → (∀ c ∈ cs, executionWidth p l (stage c) 2 ≤ W) → W ≤ cW*p → V ≤ cV*p →
    (∀ c ∈ cs, a c < 2^V) →
    ∀ (localityTarget qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    (∀ c ∈ cs, cyclicPrincipalVertices s (a c) n =
      (PhaseCellInterface.generatedWindow s coreWidth p u localityTarget (index c)).halo) →
    (∀ F ∈ complexComponentFields Fs.reverse, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun j => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F j)).re)) →
    ∀ (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (borrowed : List (Fin (prime+K+4)))
      (Vg replicasBits D : ℕ)
      (gather : GeometryRealGatherData (Q := Q) Vg s coreWidth radius n W replicasBits D Fs borrowed S),
    Vg ≤ cG*p → D ≤ cD*p →
    D ≤ 2^replicasBits*2^Nat.clog 2 jobs.length*(n*W) →
    Fs.length ≤ Sizes.T m → coreWidth ≤ cCore*p^eCore →
    n ∈ coreGatherLengths s coreWidth radius →
    gather.route (PackedTranspose.extra 1) = ports.archive →
    ports.ClassReady g width binary work readerSaved readerTmp B p u l target s t W V Fs.length n radius (n-2*radius) S →
    S.R count = [] → S.R saved = [] →
    ∀ (e : Fin 117 → Fin T), Function.Injective e → e 109 = origins → e 116 = count →
    s+coreWidth+2*radius < 2^V → n < 2^V → 0 < V →
    (∀ j ∈ [(37 : Fin 117),32,33,34,35,36,104,106,116], e j ≠ ports.archive) →
    (∀ j : Fin 117, j.val < 31 → e j ≠ ports.archive) →
    (S.R (e 37)).length = V → S.R (e 32) = binSyms V s → S.R (e 33) = binSyms V coreWidth →
    S.R (e 34) = binSyms V radius → S.R (e 35) = binSyms V n → S.R (e 36) = [] →
    (∀ j : Fin 117, j.val < 31 → S.R (e j) = []) → S.R (e 104) = [] → S.R (e 106) = [] →
    ∃ v', ∃ steps : ℕ, ∃ outputs, v'.user = v.user ∧
      (steps : ℝ) ≤ (coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ) ∧
      List.Forall₂ (fun k word => PackedNormalizedOutput p W target coreWidth k localityTarget Fs.reverse Y word) jobs outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+
        ((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)) 0
        (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
        (Host.mk v S) steps (Host.mk v' {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}) := by
  dsimp only
  obtain ⟨B₀,hB₀,hraw⟩ := selectedExposedFittingCyclicClass_exec (T := T) (U := U) (body := body)
    hR hQ hA ct cW cV cZ hcZ
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hraw,selectedGeometryRealGatherCosts_le (T := T) (K := K) hstates cG cD cW,
    selectedCyclicClassOriginSetup_le cV, selectedPolynomialCoreRouteCharge_le cCore eCore] with m hraw hgather horigin hrouteCharge
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    B u target n coreWidth depth W V α d axis hn hw hwidth hguard hcell hprepare
    hu htarget hB hl htargetMax hbandMax hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit
    Fs hF hW hWin hWmax hVmax hfit localityTarget qRef Y hqRef hwindow hY
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume hcorePoly hlengthGroup harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let radius := depth*PhaseCellBand.width p u
  let jobs := coreGatherIndices s coreWidth radius n
  obtain ⟨v',steps,outputs,hu',htime,hcert,hwithin⟩ := hraw h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    B u target n coreWidth depth W V α d axis hn hw hwidth hguard hcell hprepare
    hu htarget hB hl htargetMax hbandMax hbandRoom hgeometryRoom hrooms hprecisionRoom hvaluesFit
    Fs hF hW hWin hWmax hVmax hfit localityTarget qRef Y hqRef hwindow hY
    v S borrowed Vg replicasBits D gather harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  obtain ⟨hgTime,hgSpace⟩ := hgather h i Vg D replicasBits coreWidth radius n W Fs borrowed S gather
    hwidth hguard (by omega) hn hVg hD hWmax hrouteFit
  obtain ⟨hoTime,hoSpace⟩ := horigin h i V coreWidth radius n hw hVmax
  refine ⟨v',steps,outputs,hu',?_,hcert,?_⟩
  · have hoR : (preparedCoreOriginsCost V s coreWidth radius n : ℝ)+
        (2*jobs.length+3 : ℕ) ≤ Sizes.T m := by exact_mod_cast hoTime
    change (gather.timeCost : ℝ) ≤ Sizes.T m+
      (coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
      24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*s*W : ℕ)*dyadicRouteCharge replicasBits (Nat.clog 2 jobs.length) at hgTime
    have hreplicaBits := selectedReplicaExponent_le h replicasBits
      (by rw [←gather.hreplicaPower] ; exact hreplicaVolume)
    have hcharge := hrouteCharge h i replicasBits coreWidth radius n
      hreplicaBits hw hcorePoly hguard hlengthGroup
    have hnonneg : 0 ≤ 24*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*s*W : ℕ) := by
      have := IntegerMultBounds.MathlibTM2.Node.swapConst_pos
      unfold generatedDyadicStageCoeff
      positivity
    have hchargeBill := mul_le_mul_of_nonneg_left hcharge hnonneg
    nlinarith only [htime,hoR,hgTime,hchargeBill]
  · have htotal : gather.stockAllowance+(3*preparedCoreOriginsCost V s coreWidth radius n+
        (fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m)) ≤
        (3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m := by
      change gather.stockAllowance ≤ Sizes.T m+
        (3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W) at hgSpace
      change 3*preparedCoreOriginsCost V s coreWidth radius n ≤ Sizes.T m at hoSpace
      omega
    apply hwithin.mono
    intro d z hz
    change mnSize z+d ≤ mnSize (Host.mk v S)+0+
      (gather.stockAllowance+(3*preparedCoreOriginsCost V s coreWidth radius n+
        (fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+45*Sizes.T m))) at hz
    exact hz.trans (Nat.add_le_add_left htotal _)

end IntegerMultBounds.MathlibTM2.Cost
