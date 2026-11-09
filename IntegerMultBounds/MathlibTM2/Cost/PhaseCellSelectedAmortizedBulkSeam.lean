module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedExposedFitting
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedSeamAfterAppend
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedExactRows

/-! Concrete selected bulk execution followed by the selected full-period seam group. -/
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
open FullLineInputPlan
variable {Ts T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem selectedAmortizedBulkSeam_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
    (ct cW cV cZ cG cD : ℕ) (hcZ : 1 ≤ cZ)
    (hstates : FixedStreamedBank.stateCount ≤ Q) :
    let b := 8*executionPush (A := (prime+K)) (U := U) hR hQ+1
    ∃ B₀ Dseam : ℝ, 0 ≤ B₀ ∧ 0 ≤ Dseam ∧ ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
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
    ∀ (u target W V : ℕ) (α d : ℝ) (axis : RecoveryAxisBounds s t p u l α d),
    let B := inverseCallerWordWidth p u l target s t
    let coreWidth := amortizedCoreWidth ct p
    let depth := localityDepth p target
    let radius := depth*PhaseCellBand.width p u
    let n := coreWidth+2*radius
    let jobs := coreGatherIndices s coreWidth radius n
    let cs := jobs.attach
    let a := fun c : {k // k ∈ jobs} => coreStart coreWidth c.val-radius

    u ≤ p → target ≤ ct*p → p+2 ≤ target → B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p →
    PhaseCellBand.width p u ≤ cZ*p →
    let boundary := fun c => cyclicPrincipalBoundary s t (PhaseCellBand.width p u) (a c) n
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := fun c => initialSchurTarget p u (boundaryTableBits p solveTarget 2 (boundary c).card) 2
    ∀ (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs.reverse, ∀ j, ‖value p (F j)‖ ≤ 1),
    2*p+13 ≤ W → (∀ c ∈ cs, executionWidth p l (stage c) 2 ≤ W) → W ≤ cW*p → V ≤ cV*p →
    (∀ c ∈ cs, a c < 2^V) →
    ∀ (qRef : ℕ) (Y : (ZMod s → GaussianInt) → ZMod s → ℝ), p+1 ≤ qRef →
    (∀ F ∈ complexComponentFields Fs.reverse, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun j => (value qRef ((2 : GaussianInt)^(qRef-p-1)*F j)).re)) →
    ∀ (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)),
    J ∘L PhaseCellOperator.exact s t α = 1 →
    ∀ (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) (borrowed : List (Fin (prime+K+4)))
      (Vg replicasBits D : ℕ)
      (gather : GeometryRealGatherData (Q := Q) Vg s coreWidth radius n W replicasBits D Fs borrowed S),
    Vg ≤ cG*p → D ≤ cD*p →
    D ≤ 2^replicasBits*2^Nat.clog 2 jobs.length*(n*W) →
    Fs.length ≤ Sizes.T m →
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
    ∀ (se : Fin Ts → Fin T) (hse : Function.Injective se)
      (input : FullLineInputPlan Ts) (producer : PackedProducerPlan Ts Q)
      (compatible : input.Compatible producer) (crops : SeamCropPlan Ts producer.result)
      (recovery : Bool),
    let ks := coreSetupGroup s coreWidth (PhaseCellBand.width p u) depth (0,s)
    ∀ (huSeam : 1 ≤ u) (hwidthSeam : 8*p ≤ 2^u)
      (hgapSeam : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
      (hbudgetSeam : (u : ℝ)*d ≤ p) (hbandSeam : PhaseCellBand.width p u ≤ s)
      (hpadSeam : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
      (Xseam Yseam : (ZMod s → GaussianInt) → ZMod s → ℝ)
      (hXseam : ∀ F ∈ Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Xseam F)
        (fun j => ((1/2 : ℂ)*value p (F j)).re))
      (hYseam : ∀ F ∈ Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Yseam F)
        (fun j => ((1/2 : ℂ)*value p (F j)).im))
      (hJseam : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
      (seamReady : SeamReady input producer crops p u l target t coreWidth Fs ks (embStk se S))
      (hoff : ∀ r, seamReadPort input producer crops ks r → se r ≠ dst),
    let C := closedGridPush (U := U) (A := (prime+K)) producer recovery
    ∃ v' : HS T Q (prime+K) U, ∃ steps seamSteps : ℕ,
      ∃ outputs : List (List (Fin (prime+K+4))), ∃ batches rss,
      v'.user = v.user ∧
      outputs = batches.map (fun rows => cstream (prime+K) W rows.flatten) ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p W coreWidth k Fs.reverse J rows)
        (coreBulkIndices s coreWidth (PhaseCellBand.width p u) depth) batches ∧
      List.Forall₂ (fun k rows => ExactCoreRows (A := (prime+K)) p (2*p+13) coreWidth k Fs.reverse J rows)
        ks.reverse rss ∧
      ((steps+seamSteps : ℕ) : ℝ) ≤ ((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(2624001*(Sizes.T m : ℝ)+(Fs.length : ℝ)*Dseam*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455) ∧
      let Sbulk := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+0+(((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86))) 0
        (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count])))) (placedSeamProgram se input producer crops recovery ks))
        (Host.mk v S) (steps+seamSteps)
        (Host.mk v' {Sbulk with R := (Function.update Sbulk.R (se crops.dst)
          ((rss.map (fun rs => cstream (prime+K) (2*p+13) rs.flatten)).flatten++Sbulk.R (se crops.dst)))}) := by
  dsimp only
  obtain ⟨B₀,hB₀,hbulk⟩ := selectedAmortizedExposedFittingCyclicClass_exec
    (T := T) (U := U) (body := body) hR hQ hA ct cW cV cZ cG cD hcZ hstates
  obtain ⟨Dseam,hDseam,hseam⟩ := selectedAmortizedSeamAfterAppend_exec
    (T := Ts) (T' := T) (Q := Q) (A := (prime+K)) (U := U) (body := body) ct
  refine ⟨B₀,Dseam,hB₀,hDseam,?_⟩
  filter_upwards [hbulk,hseam] with m hbulk hseam
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  intro se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam
    hbudgetSeam hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady hoff
  obtain ⟨vBulk,steps,outputs,huserBulk,htimeBulk,hrowsBulk,hwithinBulk⟩ := hbulk h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  have hFs : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p m) (F j)‖ ≤ 1 := by
    intro F hFmem j
    exact hF F (List.mem_reverse.mpr hFmem) j
  obtain ⟨v',seamSteps,output,rss,huser,htime,hproduced,hrows,hwithin⟩ :=
    hseam h i se hse input producer compatible crops recovery hA u target d hu htarget
      huSeam hwidthSeam hgapSeam hbudgetSeam hbandSeam hpadSeam htargetLower
      Fs hFs Xseam Yseam hXseam hYseam J hJseam v S seamReady
      _ vBulk dst outputs.reverse.flatten steps _ hoff huserBulk hwithinBulk
  obtain ⟨batches,houtputs,hbatches⟩ := hrowsBulk
  refine ⟨v',steps,seamSteps,outputs,batches,rss,huser,houtputs,hbatches,hrows,?_,hwithin⟩
  linarith

end IntegerMultBounds.MathlibTM2.Cost
