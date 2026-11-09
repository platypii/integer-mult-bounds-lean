module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedDyadicRetiredAxis
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellArchiveWidthScopeBudget
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeometryRealGatherFrame

/-! Generate the shared archive-width master once around the complete axis.
Ordinary readiness is transported across setup by static read-port separation. -/
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
open IntegerMultBounds.MathlibTM2.Layer
open FullLineInputPlan
variable {Ts T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem selectedAmortizedInitializedDyadicRetiredAxis_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
    (ct cW cV cZ cG cD cVPub cDB : ℕ) (hcZ : 1 ≤ cZ)
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

    u ≤ p → ∀ (htarget : target ≤ ct*p), p+2 ≤ target → B ≤ cZ*p → l ≤ cZ*p → target ≤ cZ*p →
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
    ∀ (v : HS T Q (prime+K) U) (S₀ : Stacks T (prime+K))
      (initReplicas initCore initWord initPacket initWidth initSaved initTmp : Fin T),
    [initReplicas,initCore,initWord,initPacket,initWidth,initSaved,initTmp].Nodup →
    (∀ r ∈ [initPacket,initWidth,initSaved,initTmp], S₀.R r = []) →
    (∀ r, ports.classProtected g width binary work readerSaved readerTmp r → r ∉ [initPacket,initWidth]) →
    (∀ r ∈ [count,saved], r ∉ [initPacket,initWidth]) →
    ∀ (borrowed : List (Fin (prime+K+4)))
      (Vg replicasBits D : ℕ)
      (gather : GeometryRealGatherData (Q := Q) Vg s coreWidth radius n W replicasBits D Fs borrowed S₀)
      (initGatherOff : ∀ r, gather.readPort r → r ∉ [initPacket,initWidth]),
    Vg ≤ cG*p → D ≤ cD*p →
    D ≤ 2^replicasBits*2^Nat.clog 2 jobs.length*(n*W) →
    Fs.length ≤ Sizes.T m →
    gather.route (PackedTranspose.extra 1) = ports.archive →
    ports.ClassReady g width binary work readerSaved readerTmp B p u l target s t W V Fs.length n radius (n-2*radius) S₀ →
    S₀.R count = [] → S₀.R saved = [] →
    ∀ (e : Fin 117 → Fin T), Function.Injective e →
    (∀ j, e j ∉ [initPacket,initWidth]) → e 109 = origins → e 116 = count →
    s+coreWidth+2*radius < 2^V → n < 2^V → 0 < V →
    (∀ j ∈ [(37 : Fin 117),32,33,34,35,36,104,106,116], e j ≠ ports.archive) →
    (∀ j : Fin 117, j.val < 31 → e j ≠ ports.archive) →
    (S₀.R (e 37)).length = V → S₀.R (e 32) = binSyms V s → S₀.R (e 33) = binSyms V coreWidth →
    S₀.R (e 34) = binSyms V radius → S₀.R (e 35) = binSyms V n → S₀.R (e 36) = [] →
    (∀ j : Fin 117, j.val < 31 → S₀.R (e j) = []) → S₀.R (e 104) = [] → S₀.R (e 106) = [] →
    let proper := gatherPublicationClass s coreWidth radius n
    let hw : 0 < coreWidth := (amortizedCoreWidth_bounds ct p u target
      (by have := _h.thirteen_le_p; omega) htarget).1
    ∀ (pubE : Fin PackedTranspose.tapeCount → Fin T) (hpubE : Function.Injective pubE)
      (initPubOff : ∀ j, pubE j ∉ [initPacket,initWidth])
      (initMasters : initReplicas = pubE PackedTranspose.replicaCount ∧
        initCore = pubE (PackedTranspose.headerReg 86) ∧ initWord = pubE (PackedTranspose.headerReg 87))
      (pubImageOff : ∀ j, pubE j ≠ dst) (bPub VPub : ℕ),
    VPub ≤ cVPub*p → 2^bPub ≤ Sizes.T m →
    let aPub := Nat.clog 2 proper.indices.length
    aPub+bPub < VPub → (proper.length*W)*2^(aPub+bPub) < 2^VPub →
    ∀ (exponent packet pad tmpPub savedPub : Fin PackedTranspose.tapeCount),
    exponent = PackedTranspose.headerReg 51 → packet = PackedTranspose.headerReg 82 →
    [exponent,packet,PackedTranspose.extra 1,pad,tmpPub,savedPub].Nodup →
    Fs.reverse.length = 2^bPub →
    ∀ (pubDst : Fin PackedTranspose.tapeCount)
      (pub : PreparedPublicationPlan PackedTranspose.tapeCount (PackedTranspose.extra 1) pubDst)
      (clock lineRows : Fin PackedTranspose.tapeCount),
    (pub.support++[PackedTranspose.extra 1,pubDst,clock,lineRows]).Nodup →
    (∀ r ∈ pub.sweepSupport++[PackedTranspose.extra 1,pubDst,lineRows], r ∉ PackedTranspose.generatedPublicationHeaderRegisters) →
    pub.window = PackedTranspose.headerReg 82 → pub.padRows = PackedTranspose.headerReg 53 →
    pub.wordWidth = PackedTranspose.headerReg 87 →
    ∀ (ambient : Fin Fs.reverse.length → List (Fin (prime+K+4))), (∀ j, (ambient j).length = s*W) →
    ∀ (outputTail : List (Fin (prime+K+4)))
      (pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp : Fin T),
    [pubCount,pubSavedCount,pubWidth,dst,pubArchive,pubE (PackedTranspose.extra 1),pubSaved,pubTmp].Nodup →
    pubCount = pubE PackedTranspose.realRows →
    pubWidth = initWidth →
    (∀ r ∈ [pubSavedCount,pubArchive,pubSaved,pubTmp], S₀.R r = []) →
    (∀ r ∈ [pubSavedCount,pubArchive,pubSaved,pubTmp], r ∉ [initPacket,initWidth]) →
    S₀.R (pubE (PackedTranspose.extra 1)) = [] →
    PackedTranspose.PublicationKernelReady pubE pad tmpPub savedPub VPub S₀ →
    (∀ r ∈ [pad,tmpPub,savedPub], r ∉ PackedTranspose.generatedPublicationHeaderRegisters) →
    (S₀.R (pubE PackedTranspose.replicaCount)).length = 2^bPub →
    (S₀.R (pubE PackedTranspose.realRows)).length = proper.indices.length →
    (S₀.R (pubE (PackedTranspose.headerReg 86))).length = proper.length →
    (S₀.R (pubE (PackedTranspose.headerReg 87))).length = W →
    (∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], S₀.R (pubE (PackedTranspose.headerReg i)) = []) →
    pub.count = PackedTranspose.headerReg 88 →
    pub.advances = PackedTranspose.headerReg 91 →
    [PackedTranspose.realRows,PackedTranspose.headerReg 86,PackedTranspose.headerReg 87,PackedTranspose.headerReg 90,pub.count,pub.advances, pub.savedAdvances,pub.savedControl,pub.tmp].Nodup →
    (∀ r ∈ pub.sweepSupport++[PackedTranspose.extra 1,pubDst,lineRows], r ≠ PackedTranspose.headerReg 90) →
    (∀ r ∈ [pad,tmpPub,savedPub], r ∉ [PackedTranspose.headerReg 88,PackedTranspose.headerReg 91,PackedTranspose.headerReg 90]) →
    (∀ r ∈ pub.uniformSetupHeaders (PackedTranspose.headerReg 90), S₀.R (pubE r) = []) →
    (∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control, pub.trash,pub.tmp,pub.retireCount,pub.gap], S₀.R (pubE r) = []) →
    S₀.R (pubE pubDst) = (List.ofFn ambient).flatten++outputTail →
    clock = PackedTranspose.headerReg 54 → (S₀.R (pubE lineRows)).length = s →
    ∀ (se : Fin Ts → Fin T) (hse : Function.Injective se)
      (input : FullLineInputPlan Ts) (producer : PackedProducerPlan Ts Q)
      (compatible : input.Compatible producer) (crops : SeamCropPlan Ts producer.result) (recovery : Bool),
    ∀ (huSeam : 1 ≤ u) (hwidthSeam : 8*p ≤ 2^u)
      (hgapSeam : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1)) (hbudgetSeam : (u : ℝ)*d ≤ p)
      (hbandSeam : PhaseCellBand.width p u ≤ s)
      (hpadSeam : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
      (Xseam Yseam : (ZMod s → GaussianInt) → ZMod s → ℝ)
      (hXseam : ∀ F ∈ Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Xseam F)
        (fun j => ((1/2 : ℂ)*value p (F j)).re))
      (hYseam : ∀ F ∈ Fs, SchurDominance.Solves (realMatrix s t p u) Finset.univ (Yseam F)
        (fun j => ((1/2 : ℂ)*value p (F j)).im))
      (hJseam : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
      (seamReady : SeamReady input producer crops p u l target t coreWidth Fs
        (boundaryCropSchedule s coreWidth) (embStk se S₀))
      (initSeamOff : ∀ r, seamReadPort input producer crops (boundaryCropSchedule s coreWidth) r → se r ∉ [initPacket,initWidth])
      (seamOff : ∀ r, seamReadPort input producer crops (boundaryCropSchedule s coreWidth) r →
        se r ≠ dst ∧ se r ≠ (pubE pubDst))
      (be : Fin 117 → Fin T) (hbe : Function.Injective be)
      (initBoundaryOff : ∀ j, be j ∉ [initPacket,initWidth])
      (hsourcePort : be 95 = se crops.dst) (houtputPort : be 96 = (pubE pubDst))
      (boundaryOff : ∀ j, be j ≠ dst) (DB : ℕ) (hvolumeFit : s*W < 2^DB) (hDB : DB ≤ cDB*p)
      (masters : Fin 11 → Fin 117)
      (seedValue : Fin 117 → ℕ)
      (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,coreWidth,W] j)
      (hseedFit : ∀ j, seedValue (boundarySeedGlobals j) < 2^DB)
      (boundaryInput : BoundaryHeaderInput (s := s) p coreWidth W DB Fs.length masters seedValue (embStk be S₀))
      (retireOff : ∀ r ∈ [pubCount,pubWidth,pubSavedCount,pubArchive,pubTmp], r ≠ pubE pubDst),
    let C := closedGridPush (U := U) (A := (prime+K)) producer recovery
    let seamStock := (((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)+
      (boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+13*(boundaryPublicationTrafficFactor cDB*(Fs.length*(s*W))))
    let retireBill := 21*(Fs.length*(s*W))+12
    let axisTime : ℝ := (((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(2*(Sizes.T m : ℝ)+(2855+100*cVPub : ℕ)*(Fs.length*s*W : ℕ)+6+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)))+(2624001*(Sizes.T m : ℝ)+(Fs.length : ℝ)*Dseam*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455+(boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+(3*(boundaryPublicationTrafficFactor cDB*(Fs.length*(s*W)))+1) : ℕ))+(retireBill : ℕ)
    let axisSpace : ℕ := (((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(2*Sizes.T m+(4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(Fs.length*s*W)+12)+seamStock+3*retireBill)
    ∃ v' : HS T Q (prime+K) U, ∃ nsteps : ℕ, ∃ lines : List (List (Fin (prime+K+4))),
      v'.user = v.user ∧ nsteps ≤ 80*(Fs.length*(s*W))+⌊axisTime⌋₊ ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j‖ ≤ 1) ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j-target j‖ ≤ 3/(2:ℝ)^p))
        (inversePublicationTargets p Fs J) lines ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S₀)+0+
        (80*(Fs.length*(s*W))+axisSpace)) 0
        (withArchiveWidth initReplicas initCore initWord initPacket initWidth initSaved initTmp
          (.seq (.seq (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
          (.seq (reverseCopyRows pubCount pubSavedCount pubWidth dst pubArchive (pubE (PackedTranspose.extra 1)) pubSaved pubTmp)
            (embProg pubE Empty.elim (PackedTranspose.uniformDyadicPublicationProgram hstates exponent packet pad tmpPub savedPub pub clock lineRows))))
          (.seq (placedSeamProgram se input producer crops recovery (boundaryCropSchedule s coreWidth))
            (preparedBoundaryArchivePublication be masters)))
          (retireCountedLine pubCount pubWidth dst pubSavedCount pubArchive pubTmp)))
        (Host.mk v S₀) nsteps
        (Host.mk v' {S₀ with R := Function.update S₀.R (pubE pubDst) (lines.flatten++outputTail)}) ∧
      mnSize (Host.mk v' {S₀ with R := Function.update S₀.R (pubE pubDst) (lines.flatten++outputTail)}) =
        mnSize (Host.mk v S₀) := by
  dsimp only
  obtain ⟨B₀,Dseam,hB₀,hDseam,haxis⟩ := selectedAmortizedDyadicRetiredAxis_exec
    (Ts := Ts) (T := T) (U := U) (body := body)
    hR hQ hA ct cW cV cZ cG cD cVPub cDB hcZ hstates
  refine ⟨B₀,Dseam,hB₀,hDseam,?_⟩
  filter_upwards [haxis,selectedAmortizedCoreGeometry ct] with m haxis hgeometry
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S₀ initReplicas initCore initWord initPacket initWidth initSaved initTmp
    hinitReg hinitBlank initClassOff initCounterOff borrowed Vg replicasBits D gather initGatherOff hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he initOriginOff h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  intro pubE hpubE initPubOff initMasters pubImageOff bPub VPub hVPub hpubVolume hbitsPub hfitPub exponent packet pad tmpPub savedPub
    hExponent hPacket hpadReg hreplicas pubDst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient outputTail
    pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp hcopy hpubCount hpubWidth hcopyFresh initCopyOff hsourceBlank
    headerReady hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh hpubDst hclock hline
  intro se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam hbudgetSeam
    hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady initSeamOff seamOff
    be hbe initBoundaryOff hsourcePort houtputPort boundaryOff DB hvolumeFit hDB masters seedValue hvalues hseedFit boundaryInput
  intro retireOff
  have initOutputOff := initPubOff pubDst
  let S := archiveWidthState initPacket initWidth Fs.length
    ((amortizedCoreWidth ct (Sizes.p m)+2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u))-
      2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u)) W S₀
  let proper := gatherPublicationClass (Sizes.s m i) (amortizedCoreWidth ct (Sizes.p m))
    (localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u)
    (amortizedCoreWidth ct (Sizes.p m)+2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u))
  have hread (r : Fin T) (hr : r ∉ [initPacket,initWidth]) : S.R r = S₀.R r := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hr
    simp only [S,archiveWidthState,Function.update_of_ne hr.2,Function.update_of_ne hr.1]
  let gatherM := gather.of_frame (fun r hr => hread r (initGatherOff r hr)) rfl
  have ready := ClassReady.frame ports g (F := S) ready rfl (fun r hr => hread r (initClassOff r hr))
  have hcountBlank := (hread count (initCounterOff _ (by simp))).trans hcountBlank
  have hsaved := (hread saved (initCounterOff _ (by simp))).trans hsaved
  have horigin (j : Fin 117) := hread (e j) (initOriginOff j)
  have h37 : (S.R (e 37)).length = V := by rw [horigin]; exact h37
  have hs := (horigin 32).trans hs
  have hcw := (horigin 33).trans hcw
  have hr := (horigin 34).trans hr
  have hnSrc := (horigin 35).trans hnSrc
  have hz := (horigin 36).trans hz
  have hblank : ∀ j : Fin 117, j.val < 31 → S.R (e j) = [] := by
    intro j hj; rw [horigin]; exact hblank j hj
  have h104 := (horigin 104).trans h104
  have h106 := (horigin 106).trans h106
  have hpub (j : Fin PackedTranspose.tapeCount) := hread (pubE j) (initPubOff j)
  have hinitReplicas : (S₀.R initReplicas).length = Fs.length := by
    rw [initMasters.1]
    exact hsourceA.trans (by simpa only [List.length_reverse] using hreplicas.symm)
  have hinitCore : (S₀.R initCore).length = proper.length := by
    rw [initMasters.2.1]
    exact hsourceC
  have hinitWord : (S₀.R initWord).length = W := by
    rw [initMasters.2.2]
    exact hword
  have headerReady := headerReady.of_frame hpadReg (fun j _ => hpub j) (fun j => rfl)
  have hpubCount : (S.R pubCount).length = proper.indices.length := by
    rw [hpubCount,hpub]
    exact hsourceB
  have hcopyFresh : ∀ r ∈ [pubSavedCount,pubArchive,pubSaved,pubTmp], S.R r = [] := by
    intro r hr
    have hoff : r ∉ [initPacket,initWidth] := initCopyOff r hr
    rw [hread r hoff]; exact hcopyFresh r hr
  have hsourceBlank := (hpub (PackedTranspose.extra 1)).trans hsourceBlank
  have hsourceA : (S.R (pubE PackedTranspose.replicaCount)).length = 2^bPub := by rw [hpub]; exact hsourceA
  have hsourceB : (S.R (pubE PackedTranspose.realRows)).length = proper.indices.length := by rw [hpub]; exact hsourceB
  have hsourceC : (S.R (pubE (PackedTranspose.headerReg 86))).length = proper.length := by rw [hpub]; exact hsourceC
  have hword : (S.R (pubE (PackedTranspose.headerReg 87))).length = W := by rw [hpub]; exact hword
  have hheaderBlank : ∀ j ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45],
      S.R (pubE (PackedTranspose.headerReg j)) = [] := by intro j hj; rw [hpub]; exact hheaderBlank j hj
  have hsetupBlank : ∀ r ∈ pub.uniformSetupHeaders (PackedTranspose.headerReg 90), S.R (pubE r) = [] := by
    intro r hr; rw [hpub]; exact hsetupBlank r hr
  have hfresh : ∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control,
      pub.trash,pub.tmp,pub.retireCount,pub.gap], S.R (pubE r) = [] := by intro r hr; rw [hpub]; exact hfresh r hr
  have hpubDst := (hpub pubDst).trans hpubDst
  have hline : (S.R (pubE lineRows)).length = Sizes.s m i := by rw [hpub]; exact hline
  have seamReady := SeamReady.frame (F := embStk se S) seamReady rfl (fun r hr => hread (se r) (initSeamOff r hr))
  have boundaryInput := BoundaryHeaderInput.of_frame _ _ _ _ _ _ _ (embStk be S₀) (embStk be S) boundaryInput
    (fun j _ _ => hread (be j) (initBoundaryOff j))
  have hrowWidth : (S.R pubWidth).length = Fs.reverse.length*
      ((gatherPublicationClass (Sizes.s m i) (amortizedCoreWidth ct (Sizes.p m))
        (localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u)
        (amortizedCoreWidth ct (Sizes.p m)+2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u))).length*W) := by
    rw [hpubWidth]
    simp only [S,archiveWidthState,Function.update_self,List.length_replicate,List.length_reverse]
    rfl
  have run (v₁ : HS T Q (prime+K) U) := by
    exact haxis h i ports g dst width origins binary work readerSaved readerTmp count saved
      hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
      u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
      Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
      v₁ S borrowed Vg replicasBits D gatherM hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
      e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
      pubE hpubE pubImageOff bPub VPub hVPub hpubVolume hbitsPub hfitPub exponent packet pad tmpPub savedPub
      hExponent hPacket hpadReg hreplicas pubDst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient outputTail
      pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp hcopy hpubCount hrowWidth hcopyFresh hsourceBlank
      headerReady hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh hpubDst hclock hline
      se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam hbudgetSeam
      hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady seamOff
      be hbe hsourcePort houtputPort boundaryOff DB hvolumeFit hDB masters seedValue hvalues hseedFit boundaryInput retireOff
  -- The quantified axis execution above supplies the consumer at the setup's
  -- actual returned control state. No execution or header bank is postulated.

  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let b := 8*executionPush (A := (prime+K)) (U := U) hR hQ+1
  let coreWidth := amortizedCoreWidth ct p
  let radius := localityDepth p target*PhaseCellBand.width p u
  let L := coreWidth+2*radius-2*radius
  let C := closedGridPush (U := U) (A := (prime+K)) producer recovery
  let seamStock := (((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)+
    (boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+13*(boundaryPublicationTrafficFactor cDB*(Fs.length*(s*W))))
  let retireBill := 21*(Fs.length*(s*W))+12
  let axisTime : ℝ := (((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(2*(Sizes.T m : ℝ)+(2855+100*cVPub : ℕ)*(Fs.length*s*W : ℕ)+6+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)))+(2624001*(Sizes.T m : ℝ)+(Fs.length : ℝ)*Dseam*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455+(boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+(3*(boundaryPublicationTrafficFactor cDB*(Fs.length*(s*W)))+1) : ℕ))+(retireBill : ℕ)
  let axisSpace : ℕ := (((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(2*Sizes.T m+(4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(Fs.length*s*W)+12)+seamStock+3*retireBill)
  let consumer : Pr P T Q (prime+K) U := (.seq (.seq (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
          (.seq (reverseCopyRows pubCount pubSavedCount pubWidth dst pubArchive (pubE (PackedTranspose.extra 1)) pubSaved pubTmp)
            (embProg pubE Empty.elim (PackedTranspose.uniformDyadicPublicationProgram hstates exponent packet pad tmpPub savedPub pub clock lineRows))))
          (.seq (placedSeamProgram se input producer crops recovery (boundaryCropSchedule s coreWidth))
            (preparedBoundaryArchivePublication be masters)))
          (retireCountedLine pubCount pubWidth dst pubSavedCount pubArchive pubTmp))
  let post := fun result : List (Fin (prime+K+4)) =>
    ∃ lines : List (List (Fin (prime+K+4))),
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j‖ ≤ 1) ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j-target j‖ ≤ 3/(2:ℝ)^p))
        (inversePublicationTargets p Fs J) lines ∧ result = lines.flatten++outputTail
  have houtput : S.R (pubE pubDst) = S₀.R (pubE pubDst) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at initOutputOff
    simp only [S,archiveWidthState,Function.update_of_ne initOutputOff.2,Function.update_of_ne initOutputOff.1]
  have hlength : ∀ result, post result → result.length = (S₀.R (pubE pubDst)).length := by
    rintro result ⟨lines,hall,rfl⟩
    have hcount : lines.length = Fs.length := by
      simpa only [inversePublicationTargets,List.length_map,List.length_reverse] using hall.length_eq.symm
    have hlines : ∀ line ∈ lines, line.length = s*W :=
      (List.forall₂_and_left _ _).mp hall.flip |>.1
    rw [←houtput,hpubDst,List.length_append,List.length_append,
      length_flatten_const lines hlines,hcount,
      length_flatten_const _ (by intro line hline; obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hline; exact hambient j),
      List.length_ofFn,List.length_reverse]
  have hconsumer : ∀ v₁ : HS T Q (prime+K) U,
      ∃ v₂ n result, v₂.user = v₁.user ∧ n ≤ ⌊axisTime⌋₊ ∧ post result ∧
        ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v₁ S)+0+axisSpace) 0 consumer
          (Host.mk v₁ S) n (Host.mk v₂ {S with R := Function.update S.R (pubE pubDst) result}) := by
    intro v₁
    obtain ⟨v₂,F,M,steps,pubSteps,seamSteps,retireSteps,outputs,lines,hu,ht,hall,hF,_,_,he,_,_⟩ := run v₁
    refine ⟨v₂,steps+pubSteps+seamSteps+retireSteps,lines.flatten++outputTail,hu,Nat.le_floor ht,
      ⟨lines,hall,rfl⟩,?_⟩
    exact he.cast rfl (congrArg (Host.mk v₂) hF)
  obtain ⟨hw,_,_,hroom,_⟩ := hgeometry h i u target htarget
  have hL : 1 ≤ L := by change 1 ≤ coreWidth+2*radius-2*radius; change 0 < coreWidth at hw; omega
  have hLfit : L ≤ s := by change 3*coreWidth+_ ≤ s at hroom; dsimp only [L]; omega
  have hR : 1 ≤ Fs.length := by
    have hr : 1 ≤ Fs.reverse.length := by rw [hreplicas]; exact Nat.two_pow_pos bPub
    simpa only [List.length_reverse] using hr
  have hWone : 1 ≤ W := by have := h.thirteen_le_p; omega
  obtain ⟨v',nsteps,result,hu,hn,hpost,hstock,he⟩ := withArchiveWidth_exec_within_traffic body
    initReplicas initCore initWord initPacket initWidth initSaved initTmp (pubE pubDst)
    hinitReg initOutputOff Fs.length s L W 0 ⌊axisTime⌋₊ axisSpace hL hLfit hR hWone v S₀
    hinitReplicas hinitCore hinitWord hinitBlank consumer post hlength hconsumer
  obtain ⟨lines,hall,rfl⟩ := hpost
  exact ⟨v',nsteps,lines,hu,hn,hall,he,hstock⟩

end IntegerMultBounds.MathlibTM2.Cost
