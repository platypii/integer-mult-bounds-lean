module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedPublishedAxis
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRetireCountedLineStock
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedSeamCompletion
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedBulkArchivePublication
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
open FullLineInputPlan
variable {Ts t₀ cPub dPub T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

private theorem retirement_registers {a b c d e f g h : Fin T}
    (hr : [a,b,c,d,e,f,g,h].Nodup) : [a,c,d,b,e,h].Nodup := by
  regs_ne hr
  regs_nodup

theorem selectedAmortizedRetiredAxis_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
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
    ∀ (route : ArchiveTilePlan t₀ T Q cPub dPub (proper.length*W))
      (pubDst : Fin T) (pub : PreparedPublicationPlan T route.src pubDst)
      (clock lineRows pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp : Fin T),
    (pub.support++[route.src,pubDst,clock,lineRows]).Nodup →
    Fs.reverse.length = 2^dPub → proper.indices.length ≤ (2^dPub)^cPub →
    ∀ (ambient : Fin Fs.reverse.length → List (Fin (prime+K+4))),
      (∀ j, (ambient j).length = s*W) →
    ∀ (outputTail pubBorrowed : List (Fin (prime+K+4))),
    [pubCount,pubSavedCount,pubWidth,dst,pubArchive,route.src,pubSaved,pubTmp].Nodup →
    GroupedPublication.Ready proper hw route pub clock lineRows pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp
      Fs.reverse.length ambient outputTail pubBorrowed S →
    (∀ r, GroupedPublication.Reads proper route pub clock lineRows pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp r → r ≠ dst) →
    let copyBill := reverseCopyRowsCost proper.indices.length (Fs.reverse.length*(proper.length*W))
    let bill := replicaPublicationCost Fs.reverse.length s ((2^dPub)^cPub-proper.indices.length) proper.length W+
      37*s*W+6*Fs.reverse.length+31
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
        se r ≠ dst ∧ se r ≠ pubDst)
      (be : Fin 117 → Fin T) (hbe : Function.Injective be)
      (hsourcePort : be 95 = se crops.dst) (houtputPort : be 96 = pubDst)
      (boundaryOff : ∀ j, be j ≠ dst) (DB : ℕ) (hvolumeFit : s*W < 2^DB)
      (cropCount : Fin 3 → Fin 117)
      (hcropReg : ∀ slot, [cropCount slot,15,54,19,27,28,24,26].Nodup)
      (seedValue : Fin 117 → ℕ)
      (hvalues : ∀ j, seedValue (boundarySeedGlobals j) = ![s,coreWidth,W] j)
      (hseedFit : ∀ j, seedValue (boundarySeedGlobals j) < 2^DB)
      (boundaryReady : BoundarySeamReady (s := s) p coreWidth W DB Fs.length cropCount seedValue (embStk be S))
      (retireOff : ∀ r ∈ [pubCount,pubWidth,pubSavedCount,pubArchive,pubTmp], r ≠ pubDst),
    let C := closedGridPush (U := U) (A := (prime+K)) producer recovery
    let seamStock := (((C+1)*((1312000+756)*(1032+8*ct)+504)+1440)*(Fs.length*s*p)+2*(C+1)*Sizes.T m+86)+
      13*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W
    let retireBill := retireCountedLineCost proper.indices.length (Fs.reverse.length*(proper.length*W))
    ∃ v' : HS T Q (prime+K) U, ∃ F M : Stacks T (prime+K), ∃ steps pubSteps seamSteps retireSteps : ℕ,
      ∃ outputs : List (List (Fin (prime+K+4))), ∃ lines : List (List (Fin (prime+K+4))),
    let Sbulk := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)};
      v'.user = v.user ∧ ((steps+pubSteps+seamSteps+retireSteps : ℕ) : ℝ) ≤ (((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(copyBill+(route.cost Sbulk+bill) : ℕ))+(2624001*(Sizes.T m : ℝ)+(Fs.length : ℝ)*Dseam*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d m)*(p : ℝ)^(129/128 : ℝ)+
        726*(Fs.length*s*p : ℕ)+455+(3*boundarySeamCost Fs.length (2*p+13) DB s coreWidth W+1 : ℕ))+(retireBill : ℕ) ∧
      List.Forall₂ (fun target line => line.length = s*W ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j‖ ≤ 1) ∧
        (∀ j : ZMod s, ‖pairedCellRead p W line j-target j‖ ≤ 3/(2:ℝ)^p))
        (inversePublicationTargets p Fs J) lines ∧
      F = {S with R := (Function.update S.R pubDst (lines.flatten++outputTail))} ∧
      F.R dst = S.R dst ∧
      outputs.reverse.flatten.length = proper.indices.length*(Fs.reverse.length*(proper.length*W)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+0+(((((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(2*copyBill+(route.stockAllowance+2*bill)))+seamStock)+3*retireBill)) 0
        (.seq (.seq (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
          (.seq (reverseCopyRows pubCount pubSavedCount pubWidth dst pubArchive route.src pubSaved pubTmp)
            (.seq route.program (pub.replicaProgram clock lineRows))))
          (.seq (placedSeamProgram se input producer crops recovery (boundaryCropSchedule s coreWidth))
            (embProg be Empty.elim (boundarySeamPublication (P := Empty) cropCount))))
          (retireCountedLine pubCount pubWidth dst pubSavedCount pubArchive pubTmp))
        (Host.mk v S) (steps+pubSteps+seamSteps+retireSteps) (Host.mk v' F) ∧
      F.inp = S.inp ∧ F.out = S.out ∧ F.L = S.L ∧
      ∀ r, r ≠ pubDst → F.R r = S.R r := by
  dsimp only
  obtain ⟨B₀,Dseam,hB₀,hDseam,haxis⟩ := selectedAmortizedPublishedAxis_exec
    (Ts := Ts) (t₀ := t₀) (cPub := cPub) (dPub := dPub) (T := T) (U := U) (body := body)
    hR hQ hA ct cW cV cZ cG cD hcZ hstates
  refine ⟨B₀,Dseam,hB₀,hDseam,?_⟩
  filter_upwards [haxis] with m haxis
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  intro route pubDst pub clock lineRows pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp
    hports hreplicas hcapacity ambient hambient outputTail pubBorrowed hcopy pubReady hoff
  intro se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam hbudgetSeam
    hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady seamOff
    be hbe hsourcePort houtputPort boundaryOff DB hvolumeFit cropCount hcropReg seedValue hvalues hseedFit boundaryReady
  intro retireOff
  obtain ⟨vm,Fraw,M,steps,pubSteps,seamSteps,outputs,lines,huser,htime,hall,hFpub,hraw,hvolume,hwithin,hi,ho,hl,hframe⟩ :=
    haxis h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
    route pubDst pub clock lineRows pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp
    hports hreplicas hcapacity ambient hambient outputTail pubBorrowed hcopy pubReady hoff
    se hse input producer compatible crops recovery huSeam hwidthSeam hgapSeam hbudgetSeam
    hbandSeam hpadSeam Xseam Yseam hXseam hYseam hJseam seamReady seamOff
    be hbe hsourcePort houtputPort boundaryOff DB hvolumeFit cropCount hcropReg seedValue hvalues hseedFit boundaryReady
  have hstable (r : Fin T) (hr : r ∈ [pubCount,pubWidth,pubSavedCount,pubArchive,pubTmp]) :
      Fraw.R r = S.R r := by
    apply hframe r ?_ (retireOff r hr)
    apply hoff r
    apply Or.inr; apply Or.inr
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
    rcases hr with rfl | rfl | rfl | rfl | rfl <;> simp
  have hretire : [pubCount,pubWidth,dst,pubSavedCount,pubArchive,pubTmp].Nodup :=
    retirement_registers hcopy
  obtain ⟨v',nr,hu,hn,he⟩ := retireCountedLine_exec_within (body := body)
    pubCount pubWidth dst pubSavedCount pubArchive pubTmp hretire _ _ outputs.reverse.flatten (S.R dst)
    hvolume vm Fraw (by rw [hstable pubCount (by simp)]; exact pubReady.count)
    (by rw [hstable pubWidth (by simp)]; exact pubReady.rowWidth) hraw
    (by rw [hstable pubSavedCount (by simp)]; exact pubReady.fresh _ (by simp))
    (by rw [hstable pubArchive (by simp)]; exact pubReady.fresh _ (by simp))
    (by rw [hstable pubTmp (by simp)]; exact pubReady.fresh _ (by simp)) 0
  have hne : dst ≠ pubDst := by
    intro heq
    exact boundaryOff 96 (houtputPort.trans heq.symm)
  have hout : Fraw.R pubDst = lines.flatten++outputTail := by
    rw [hFpub]
    exact Function.update_self _ _ _
  have hfinal : ({Fraw with R := Function.update Fraw.R dst (S.R dst)} : Stacks T (prime+K)) =
      {S with R := Function.update S.R pubDst (lines.flatten++outputTail)} := by
    refine Stacks.ext hi ho hl ?_
    funext r
    by_cases hr : r = dst
    · subst r
      simp only [Function.update_self,Function.update_of_ne hne]
    · by_cases hp : r = pubDst
      · subst r
        simp only [Function.update_of_ne hne.symm,Function.update_self,hout]
      · simp only [Function.update_of_ne hr,Function.update_of_ne hp]
        exact hframe r hr hp
  have htotal := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hwithin he
  have htotalFinal := htotal.cast rfl (congrArg (Host.mk v') hfinal)
  refine ⟨v',_,M,steps,pubSteps,seamSteps,nr,outputs,lines,hu.trans huser,?_,hall,rfl,?_,hvolume,
    htotalFinal,rfl,rfl,rfl,?_⟩
  ·
    have hnReal := Nat.cast_le (α := ℝ).mpr hn
    rw [Nat.cast_add]
    linarith only [htime,hnReal]
  · exact Function.update_of_ne hne _ _
  · intro r hr
    exact Function.update_of_ne hr _ _

end IntegerMultBounds.MathlibTM2.Cost
