module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedExposedFitting
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedAmortizedReversedDyadicPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExactCoreArchiveVolume
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
open IntegerMultBounds.MathlibTM2.Layer
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K : ℕ} {P U : Type} {body : P → Pr P T Q (prime+K) U}

private theorem copy_source_off {a b c d e f g h : Fin T} (hr : [a,b,c,d,e,f,g,h].Nodup) :
    ∀ r ∈ [a,b,c,e,g,h], r ≠ d := by
  regs_ne hr
  intro r hmem
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hmem
  rcases hmem with rfl | rfl | rfl | rfl | rfl | rfl
  all_goals first | assumption | (apply Ne.symm; assumption)

theorem selectedAmortizedDyadicPublishedBulk_exec (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q) (hA : 96 ≤ prime+K)
    (ct cW cV cZ cG cD cVPub : ℕ) (hcZ : 1 ≤ cZ)
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
    let hw : 0 < coreWidth := (amortizedCoreWidth_bounds ct p u target (by have := _h.thirteen_le_p; omega) htarget).1
    ∀ (pubE : Fin PackedTranspose.tapeCount → Fin T) (hpubE : Function.Injective pubE)
      (pubImageOff : ∀ j, pubE j ≠ dst) (bPub VPub : ℕ),
    VPub ≤ cVPub*p → 2^bPub ≤ Sizes.T m →
    let aPub := Nat.clog 2 proper.indices.length
    aPub+bPub < VPub → (proper.length*W)*2^(aPub+bPub) < 2^VPub →
    ∀ (exponent packet pad tmpPub savedPub : Fin PackedTranspose.tapeCount),
    [exponent,packet,PackedTranspose.extra 1,pad,tmpPub,savedPub].Nodup →
    Fs.reverse.length = 2^bPub →
    ∀ (pubDst : Fin PackedTranspose.tapeCount)
      (pub : PreparedPublicationPlan PackedTranspose.tapeCount (PackedTranspose.extra 1) pubDst)
      (clock lineRows : Fin PackedTranspose.tapeCount),
    (pub.support++[PackedTranspose.extra 1,pubDst,clock,lineRows]).Nodup →
    (∀ r ∈ pub.support++[PackedTranspose.extra 1,pubDst,clock,lineRows], r ∉ PackedTranspose.countedPublicationHeaderRegisters) →
    ∀ (ambient : Fin Fs.reverse.length → List (Fin (prime+K+4))), (∀ j, (ambient j).length = s*W) →
    ∀ (outputTail pubBorrowed : List (Fin (prime+K+4)))
      (pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp : Fin T),
    [pubCount,pubSavedCount,pubWidth,dst,pubArchive,pubE (PackedTranspose.extra 1),pubSaved,pubTmp].Nodup →
    (S.R pubCount).length = proper.indices.length →
    (S.R pubWidth).length = Fs.reverse.length*(proper.length*W) →
    (∀ r ∈ [pubSavedCount,pubArchive,pubSaved,pubTmp], S.R r = []) →
    S.R (pubE (PackedTranspose.extra 1)) = [] →
    PackedTranspose.PublicationWorkspaceReady pubE exponent packet pad tmpPub savedPub aPub bPub proper.length W VPub S →
    (∀ r ∈ [exponent,packet,pad,tmpPub,savedPub], r ∉ PackedTranspose.countedPublicationHeaderRegisters) →
    (S.R (pubE PackedTranspose.replicaCount)).length = 2^bPub →
    (S.R (pubE PackedTranspose.realRows)).length = proper.indices.length →
    (S.R (pubE PackedTranspose.packetWidth)).length = proper.length*W →
    (∀ i ∈ [(84 : Fin 117),85,97,98,102,40,41,42,43,44,45], S.R (pubE (PackedTranspose.headerReg i)) = []) →
    pub.Ready (coreSubsetPublicationWindows s coreWidth proper.length hw proper.indices proper.sublist)
      W (2^aPub-proper.indices.length) pubBorrowed (embStk pubE S) →
    S.R (pubE pubDst) = (List.ofFn ambient).flatten++outputTail →
    (S.R (pubE clock)).length = Fs.reverse.length → (S.R (pubE lineRows)).length = s →
    ∃ v' : HS T Q (prime+K) U, ∃ steps pubSteps : ℕ, ∃ outputs : List (List (Fin (prime+K+4))),
      ∃ lines : List (List (Fin (prime+K+4))),
    let Sbulk := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)};
      v'.user = v.user ∧ ((steps+pubSteps : ℕ) : ℝ) ≤ ((coreExposureTrafficFactor cG cW+6013 : ℕ)*(Fs.length*s*W : ℕ)+
        432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)+
        (8*(b : ℝ)+5)*(Sizes.T m : ℝ)+B₀*(2*(Fs.length : ℝ)+1)*
        ((t : ℝ)*(1+(PhaseCellBand.width p u : ℝ)^2/(Sizes.d m : ℝ)))*(p : ℝ)^(129/128 : ℝ))+(2*(Sizes.T m : ℝ)+(2255+100*cVPub : ℕ)*(Fs.length*s*W : ℕ)+6+
        108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*s*W : ℕ)*Sizes.d m*((Sizes.ℓ m : ℝ)^Parameters.tau+1)) ∧
      proper.BankAccurate p W (inversePublicationTargets p Fs J) lines (3/(2 : ℝ)^p) ∧
      outputs.reverse.flatten.length = proper.indices.length*(Fs.reverse.length*(proper.length*W)) ∧
      ExecWithin body (fun z state => mnSize state+z ≤ mnSize (Host.mk v S)+0+(((3*coreExposureTrafficFactor cG cW+12+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*s*W)+
          fittingCyclicWorkspaceTrafficFactor (A := (prime+K)) (U := U) hR hQ ct cW*Fs.length*t*p+47*Sizes.T m)+(2*Sizes.T m+(3790+100*cVPub+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(Fs.length*s*W)+12))) 0
        (.seq (.seq gather.program (.seq (placedCoreOrigins e)
          (.seq (scanP count saved (ports.generatedOriginProgram g dst width origins binary work readerSaved readerTmp hR hQ))
            (clearWords [count]))))
          (.seq (reverseCopyRows pubCount pubSavedCount pubWidth dst pubArchive (pubE (PackedTranspose.extra 1)) pubSaved pubTmp)
            (embProg pubE Empty.elim (.seq (.seq PackedTranspose.countedPublicationHeadersProgram (.seq (.seq
              (ownedPrefixPadding exponent packet (PackedTranspose.extra 1) pad tmpPub savedPub (pairSym (prime+K) false false))
              (PackedTranspose.program hstates)) (pub.replicaProgram clock lineRows))) (clearWords PackedTranspose.countedPublicationHeaderRegisters)))))
        (Host.mk v S) (steps+pubSteps)
        (Host.mk v' {Sbulk with R := (Function.update Sbulk.R (pubE pubDst) (lines.flatten++outputTail))}) := by
  dsimp only
  obtain ⟨B₀,hB₀,hbulk⟩ := selectedAmortizedExposedFittingCyclicClass_exec (T := T) (U := U) (body := body)
    hR hQ hA ct cW cV cZ cG cD hcZ hstates
  have hpub := selectedAmortizedReversedDyadicPublication_exec body hstates ct cVPub
  refine ⟨B₀,hB₀,?_⟩
  filter_upwards [hbulk,hpub,selectedAmortizedGatherSchedule ct] with m hbulk hpub hschedule
  intro h i _ ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  intro pubE hpubE pubImageOff bPub VPub hVPub hpubVolume hbitsPub hfitPub exponent packet pad tmpPub savedPub
    hpadReg hreplicas pubDst pub clock lineRows hports hpubOff ambient hambient outputTail pubBorrowed
    pubCount pubSavedCount pubWidth pubArchive pubSaved pubTmp hcopy hpubCount hpubWidth hcopyFresh hsourceBlank
    headerReady hpadOff hsourceA hsourceB hsourceC hheaderBlank pubReady hpubDst hclock hline
  obtain ⟨vm,steps,outputs,huser,htime,houtputs,hwithin⟩ := hbulk h i ports g dst width origins binary work readerSaved readerTmp count saved
    hwireL hwireR hfixed hdst harchiveDst hmastersDst hreg hreader hretained hprotected hcounter hconsume
    u target W V α d axis hu htarget htargetLower hB hl htargetMax hbandMax
    Fs hF hW hWin hWmax hVmax hfit qRef Y hqRef hY J hJ
    v S borrowed Vg replicasBits D gather hVg hD hrouteFit hreplicaVolume harchive ready hcountBlank hsaved
    e he h109 h116 hwide hnfit hV hmetaOff htableOff h37 hs hcw hr hnSrc hz hblank h104 h106
  have hrowsAll := houtputs
  obtain ⟨batches,hwords,hrows⟩ := houtputs
  let Sbulk := {S with R := Function.update S.R dst (outputs.reverse.flatten++S.R dst)}
  have hread (j : Fin PackedTranspose.tapeCount) : Sbulk.R (pubE j) = S.R (pubE j) :=
    Function.update_of_ne (pubImageOff j) _ _
  have hcopyRead (r : Fin T) (hr : r ∈ [pubCount,pubSavedCount,pubWidth,pubArchive,pubSaved,pubTmp]) : Sbulk.R r = S.R r :=
    Function.update_of_ne (copy_source_off hcopy r hr) _ _
  have headers := headerReady.of_frame hpadReg (by intro j _; exact hread j) (by intro j; rfl)
  have pubReadyBulk := pubReady.of_frame (F := embStk pubE Sbulk) (by intro j _; exact hread j)
  have hWone : 1 ≤ W := by have := h.thirteen_le_p; omega
  obtain ⟨lines,v',pubSteps,huser',htime',hgood,hePub⟩ := hpub
    h i pubE hpubE u target htarget W hWone bPub VPub hVPub hpubVolume hbitsPub hfitPub (by omega)
    exponent packet pad tmpPub savedPub hpadReg Fs.reverse hreplicas J batches hrows 0 vm Sbulk
    pubCount pubSavedCount pubWidth dst pubArchive pubSaved pubTmp hcopy
    (by rw [hcopyRead pubCount (by simp)]; exact hpubCount)
    (by rw [hcopyRead pubWidth (by simp)]; exact hpubWidth) (S.R dst)
    (by intro r hr; rw [hcopyRead r (by
          simp only [List.mem_cons,List.not_mem_nil,or_false] at hr
          rcases hr with rfl | rfl | rfl | rfl <;> simp)]; exact hcopyFresh r hr)
    (by rw [hread]; exact hsourceBlank) headers hpadOff
    (by rw [hread]; exact hsourceA)
    (by rw [hread]; exact hsourceB)
    (by rw [hread]; exact hsourceC)
    (by intro i hi; rw [hread]; exact hheaderBlank i hi)
    (by simp only [Sbulk,Function.update_self,hwords]) pubDst pub clock lineRows hports hpubOff ambient hambient
    outputTail pubBorrowed pubReadyBulk
    (by change Sbulk.R (pubE pubDst) = _; rw [hread]; exact hpubDst)
    (by change (Sbulk.R (pubE clock)).length = _; rw [hread]; exact hclock)
    (by change (Sbulk.R (pubE lineRows)).length = _; rw [hread]; exact hline)
  let proper := gatherPublicationClass (Sizes.s m i) (amortizedCoreWidth ct (Sizes.p m))
    (localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u)
    (amortizedCoreWidth ct (Sizes.p m)+2*(localityDepth (Sizes.p m) target*PhaseCellBand.width (Sizes.p m) u))
  have hbulkKeys := (hschedule h i u target htarget).2.2.2.1
  have hvolume := exactCoreOutputs_volume proper.indices Fs.reverse J outputs
    (by simpa only [proper,gatherPublicationClass,hbulkKeys] using hrowsAll)
    (fun k hk => ((mem_corePublicationIndices _ _ _ _).mp (proper.sublist.subset hk)).2)
  have hwhole := execWithin_seq_two_budget body _ _ _ _ _ _ _ 0 _ _ hwithin hePub
  refine ⟨v',steps,pubSteps,outputs,lines,huser'.trans huser,?_,?_,hvolume,?_⟩
  · simp only [List.length_reverse,←hreplicas] at htime'
    simp only [Nat.mul_assoc] at htime htime' ⊢
    rw [Nat.cast_add]
    linarith only [htime,htime']
  · simpa only [List.reverse_reverse] using hgood
  · simpa only [List.length_reverse,←hreplicas,Nat.mul_assoc] using hwhole

end IntegerMultBounds.MathlibTM2.Cost
