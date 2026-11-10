module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedDyadicPublishedBulk
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedSeamCompletion
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatherSchedule
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInverseMasterInput
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFittingCyclicWindow
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedNormalizedExactRows

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
open IntegerMultBounds.MathlibTM2.Layer
open FullLineInputPlan
variable {Ts T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

theorem selectedAmortizedDyadicPublishedAxis_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
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
    let proper := gatherPublicationClass s coreWidth radius n
    let hw : 0 < coreWidth := (amortizedCoreWidth_bounds ct p u target
      (by have := _h.thirteen_le_p; omega) htarget).1
    ∀ (pubE : Fin PackedTranspose.tapeCount → Fin T) (hpubE : Function.Injective pubE)
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
    (S.R pubCount).length = proper.indices.length →
    (S.R pubWidth).length = Fs.reverse.length*(proper.length*W) →
    (∀ r ∈ [pubSavedCount,pubArchive,pubSaved,pubTmp], S.R r = []) →
    S.R (pubE (PackedTranspose.extra 1)) = [] →
    PackedTranspose.PublicationKernelReady pubE pad tmpPub savedPub VPub S →
    (∀ r ∈ [pad,tmpPub,savedPub], r ∉ PackedTranspose.generatedPublicationHeaderRegisters) →
    (S.R (pubE PackedTranspose.replicaCount)).length = 2^bPub →
    (S.R (pubE PackedTranspose.realRows)).length = proper.indices.length →
    (S.R (pubE (PackedTranspose.headerReg 86))).length = proper.length →
    (S.R (pubE (PackedTranspose.headerReg 87))).length = W →
    (∀ i ∈ [(84 : Fin 117),85,81,51,82,53,54,55,56,57,97,98,102,40,41,42,43,44,45], S.R (pubE (PackedTranspose.headerReg i)) = []) →
    pub.count = PackedTranspose.headerReg 88 →
    pub.advances = PackedTranspose.headerReg 91 →
    [PackedTranspose.realRows,PackedTranspose.headerReg 86,PackedTranspose.headerReg 87,PackedTranspose.headerReg 90,pub.count,pub.advances, pub.savedAdvances,pub.savedControl,pub.tmp].Nodup →
    (∀ r ∈ pub.sweepSupport++[PackedTranspose.extra 1,pubDst,lineRows], r ≠ PackedTranspose.headerReg 90) →
    (∀ r ∈ [pad,tmpPub,savedPub], r ∉ [PackedTranspose.headerReg 88,PackedTranspose.headerReg 91,PackedTranspose.headerReg 90]) →
    (∀ r ∈ pub.uniformSetupHeaders (PackedTranspose.headerReg 90), S.R (pubE r) = []) →
    (∀ r ∈ [pub.savedControl,pub.savedAdvances,pub.counter,pub.zero,pub.acc,pub.control, pub.trash,pub.tmp,pub.retireCount,pub.gap], S.R (pubE r) = []) →
    S.R (pubE pubDst) = (List.ofFn ambient).flatten++outputTail →
    clock = PackedTranspose.headerReg 54 → (S.R (pubE lineRows)).length = s →
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
        (boundaryCropSchedule s coreWidth) (embStk se S))
      (seamOff : ∀ r, seamReadPort input producer crops (boundaryCropSchedule s coreWidth) r →
        se r ≠ dst ∧ se r ≠ (pubE pubDst))
      (be : Fin 117 → Fin T) (hbe : Function.Injective be)
      (hsourcePort : be 95 = se crops.dst) (houtputPort : be 96 = (pubE pubDst))
      (boundaryOff : ∀ j, be j ≠ dst) (DB : ℕ) (hvolumeFit : s*W < 2^DB) (hDB : DB ≤ cDB*p)
      (masters : Fin 11 → Fin 117)
      (boundaryInput : BoundaryDimensionSource (s := s) p coreWidth W DB Fs.length masters (embStk be S)),
    let C := gridDispatchPush (U := U) (A := (prime+K)) producer.hR producer.hQ
    let seamStock := (((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)+
      (boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+13*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W)
    ∃ v' : HS T Q (prime+K) U, ∃ F M : Stacks T (prime+K), ∃ steps pubSteps seamSteps : ℕ,
      ∃ outputs : List (List (Fin (prime+K+4))), ∃ lines : List (List (Fin (prime+K+4))),
      v'.user = v.user ∧ ((steps+pubSteps+seamSteps : ℕ) : ℝ) ≤ (((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(2*(Sizes.T m : ℝ)+(2855+100*cVPub : ℕ)*(Fs.length*s*W : ℕ)+6+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)))+(2624001*(Sizes.T m : ℝ)+(Fs.length : ℝ)*Dseam*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455+(boundaryHeaderTrafficFactor cDB*(Fs.length*(s*W))+(3*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W+1) : ℕ)) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j‖ ≤ 1) ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j-target j‖ ≤ 3/(2:ℝ)^p))
        (inversePublicationTargets p Fs J) lines ∧
      F = {M with R := (Function.update M.R (pubE pubDst) (lines.flatten++outputTail))} ∧
      F.R dst = outputs.reverse.flatten++S.R dst ∧
      outputs.reverse.flatten.length = proper.indices.length*(Fs.reverse.length*(proper.length*W)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+0+(((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(2*Sizes.T m+(4390+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(Fs.length*s*W)+12)+seamStock)) 0
        (.seq (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
          (.seq (reverseCopyRows pubCount pubSavedCount pubWidth dst pubArchive (pubE (PackedTranspose.extra 1)) pubSaved pubTmp)
            (embProg pubE Empty.elim (PackedTranspose.uniformDyadicPublicationProgram hstates exponent packet pad tmpPub savedPub pub clock lineRows))))
          (.seq (placedSeamProgram se input producer crops recovery (boundaryCropSchedule s coreWidth))
            (preparedBoundaryArchivePublication be masters)))
        (Host.mk v S) (steps+pubSteps+seamSteps) (Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ dst → r ≠ (pubE pubDst) → F.R r = S.R r := by
  dsimp only
  obtain ⟨B₀,hB₀,hbulk⟩ := selectedAmortizedDyadicPublishedBulk_exec
    (T := T) (U := U) (body := body)
    hR hQ hA ct cW cV cZ cG cD cVPub hcZ hstates
  obtain ⟨Dseam,hDseam,hseam⟩ := selectedAmortizedSeamCompletion_exec
    (T := Ts) (T' := T) (Q := Q) (A := (prime+K)) (U := U) (body := body) ct cDB
  refine ⟨B₀,Dseam,hB₀,hDseam,?_⟩
  filter_upwards [hbulk,hseam] with m hbulk hseam
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  intro pubE hpubE pubImageOff bPub VPub hVPub hpubVolume hbitsPub hfitPub exponent packet pad tmpPub savedPub
    hExponent hPacket hpadReg hreplicas pubDst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient outputTail
    pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp hcopy hpubCount hpubWidth hcopyFresh hsourceBlank
    headerReady hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh hpubDst hclock hline
  intro se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam hbudgetSeam
    hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady seamOff
    be hbe hsourcePort houtputPort boundaryOff DB hvolumeFit hDB masters boundaryInput
  obtain ⟨vm,steps,pubSteps,outputs,bulkLines,huser,htime,hgood,hvolume,hwithin⟩ := hbulk h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
    pubE hpubE pubImageOff bPub VPub hVPub hpubVolume hbitsPub hfitPub exponent packet pad tmpPub savedPub
    hExponent hPacket hpadReg hreplicas pubDst pub clock lineRows hports hpubOff hwindow hpadding hwordPort ambient hambient outputTail
    pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp hcopy hpubCount hpubWidth hcopyFresh hsourceBlank
    headerReady hpadOff hsourceA hsourceB hsourceC hword hheaderBlank hcountPort hadvancePort hsetupReg hstrideOff hpadSetupOff hsetupBlank hfresh hpubDst hclock hline
  let Sbulk := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}
  let M := {Sbulk with R := Function.update Sbulk.R (pubE pubDst) (bulkLines.flatten++outputTail)}
  have houtput : M.R (pubE pubDst) = bulkLines.flatten++outputTail := Function.update_self _ _ _
  have hraw : M.R dst = outputs.reverse.flatten++S.R dst := by
    change Function.update Sbulk.R (pubE pubDst) _ dst = _
    rw [Function.update_of_ne (pubImageOff pubDst).symm]
    exact Function.update_self _ _ _
  have hframe (r : Fin T) (hrd : r ≠ dst) (hrp : r ≠ pubE pubDst) : M.R r = S.R r :=
    (Function.update_of_ne hrp _ _).trans (Function.update_of_ne hrd _ _)
  have hi : M.inp = S.inp := rfl
  have ho : M.out = S.out := rfl
  have hl : M.L = S.L := rfl
  have seamReadyM := seamReady.frame (F := embStk se M)
    (by funext j; exact congrFun hl (se j))
    (by intro r hr; exact hframe (se r) (seamOff r hr).1 (seamOff r hr).2)
  have boundaryInputM := boundaryInput.of_frame (Sizes.p m) _ W DB Fs.length masters
    (embStk be S) (embStk be M) (by
      intro j hj95 hj96
      exact hframe (be j) (boundaryOff j) (by rw [←houtputPort]; exact hbe.ne hj96))
  have hFs : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p m) (F j)‖ ≤ 1 := by
    intro F hmem j
    exact hF F (List.mem_reverse.mpr hmem) j
  obtain ⟨lines,v',seamSteps,huser',htime',hall,heSeam⟩ := hseam
    h i se hse input producer compatible crops recovery hA u target d hu htarget
    huSeam hwidthSeam hgapSeam hbudgetSeam hbandSeam hpadSeam htargetLower
    Fs hFs (by
      have hpos : 1 ≤ Fs.reverse.length := by rw [hreplicas]; exact Nat.two_pow_pos bPub
      simpa only [List.length_reverse] using hpos) Xseam Yseam hXseam hYseam J hJseam vm M seamReadyM W hW
    be hbe hsourcePort DB hvolumeFit hDB masters boundaryInputM
    bulkLines outputTail (by rw [houtputPort]; exact houtput) hgood 0
  rw [houtputPort] at heSeam
  refine ⟨v',_,M,steps,pubSteps,seamSteps,outputs,lines,huser'.trans huser,?_,hall,rfl,?_,hvolume,
    execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hwithin heSeam,hi,ho,hl,?_⟩
  · rw [Nat.cast_add]
    linarith
  · exact (Function.update_of_ne (by
      intro heq
      exact boundaryOff 96 (houtputPort.trans heq.symm)) _ _).trans hraw
  · intro r hrd hrp
    exact (Function.update_of_ne hrp _ _).trans (hframe r hrd hrp)

end IntegerMultBounds.MathlibTM2.Cost
