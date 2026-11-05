module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublishedBoundaryRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSharedPreparationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCallerFormat
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedClassSetupCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublicationControls
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublicationPages
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedRawCallerGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawCallerBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPolynomialPublicationBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRetainedPublicationBudget
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedFullLineLifecycle

/-! Execute paid shared initialization, the selected proper/boundary run, and
owned-header retirement from raw caller inputs. The prepared state and every
consumer contract are produced by the actual initialization execution. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Fast
open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
open ComputedClassBanks CallerLayout CommonClassGeometry PackedTranspose FullLineInputPlan
open IntegerMultBounds.NLogN.SchurDominance

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- The raw-input contract for the selected S4 caller. Its prepared state is
an execution witness, and all initialization and retirement costs are charged. -/
noncomputable def SelectedRawPublishedBoundaryRun {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) : Prop :=
    let physicalBank := CallerLayout.bank (solverSource ∘ bank)
    let physicalInj := bank_injective (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj)
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∃ G : ℝ, 0 ≤ G ∧ ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] [NeZero (Sizes.t n₀ i)] (u target : ℕ),
    let L := amortizedCoreWidth ct (Sizes.p n₀)+
      2*(localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u)
    ∀ (_hu : u ≤ Sizes.p n₀) (_htarget : target ≤ ct*Sizes.p n₀)
    (gap : ℝ) (C : ZMod (Sizes.s n₀ i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
        (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n₀)
        (l := haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (t := Sizes.t n₀ i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).2) (V := V j) (Real.sqrt (u : ℝ)) gap C)
    (Fs : List (ZMod (Sizes.s n₀ i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n₀) (F j)‖ ≤ 1),
    let B := inverseCallerWordWidth (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
    let W := packedHaloCommonWidth (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.s n₀ i) u (target+1) 2
    let radius := localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u
    let indices := coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let p := Sizes.p n₀
    let s := Sizes.s n₀ i
    let t := Sizes.t n₀ i
    let l := haloInverseRingLog s t
    let coreWidth := amortizedCoreWidth ct p
    ∀ (Cprog depth Vg Vr replicaExp : ℕ),
    let D := canonicalCallerFormat p u l target s t B W Fs.length radius coreWidth Vg Vr
    ∀
    (_hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).clock (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).work (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).count (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).spare (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).result b.hR b.hQ)) ≤ Cprog)
    (_hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hA : 4 ≤ (prime+K))
    (v : HS (MachineTapes (T+solverRegisterCount)) Q (prime+K) U)
    (S : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K))
    (borrowed : List (Fin (prime+K+4)))
    (rawSrc : Fin 11 → Fin T) (_hrawSrc : Function.Injective rawSrc)
    (widthSource : Fin T) (widths : Fin 3 → Fin T)
    (raw : RawInput (T+solverRegisterCount) (prime+K) D p u l target s t B W Fs.length radius coreWidth Vg Vr
      (solverSource ∘ rawSrc) (solverSource widthSource) (solverSource ∘ widths) S)
    (_hword : S.R (fullHeader _ .word) = []) (_hreplicas : S.R (fullHeader _ .replicas) = [])
    (_hvolume : S.R (fullHeader _ .volume) = [])
    (_hsource : S.R (fullHeader _ .input) = Fs.flatMap (fun F => cstream (prime+K) W (chirpLine s F))++borrowed)
    (_hexposure : ∀ j : Fin 175, S.R (Fin.castAdd tapeCount (Fin.natAdd ((T+solverRegisterCount)+headerCount) j)) = [])
    (_houtput : S.R (fullExposedClassBank physicalBank (.control .source)) = [])
    (_hroutingLeft : ∀ j : Fin tapeCount, S.L (Fin.natAdd (((T+solverRegisterCount)+headerCount)+175) j) = [])
    (_hsourceLeft : S.L (control (fullExposedClassBank physicalBank) .source) = [])
    (_htable : ∀ r, S.R (numericTable (T+solverRegisterCount) r) = [])
    (_hbank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank physicalBank j) = [])
    (_hleft : ∀ j, S.L (recovery (fullExposedClassBank physicalBank) (.work j)) = [])
    (_hpubBlank : ∀ j : Fin 7, S.R (fullHeader _ (.publication j)) = [])
    (_hresultLeft : S.L (fullExposedClassBank physicalBank (.recovery (.control .result))) = [])
    (_hambientLeft : S.L (fullHeader _ .output) = [])
    (_hsolver : ∀ r : SolverRole, S.R (solverRegister T r) = [])
    (_hsolverLeft : ∀ r : SolverRole, S.L (solverRegister T r) = [])
    (movement : GatherBounds Q Vg Vr s coreWidth radius L W replicaExp Fs)
    (_hExposeWidth : Vg ≤ cV*p) (_hRouteWidth : Vr ≤ cD*p)
    (_hMetadataFit : Vr ≤ 2^replicaExp*2^Nat.clog 2 indices.length*(L*W))
    (_hReplicaVolume : Fs.length ≤ Sizes.T n₀)
    (hprecision : p+2 ≤ target)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (ambient : Fin (2^replicaExp) → List (Fin (prime+K+4))) (_hambient : ∀ j, (ambient j).length = s*W)
    (outputTail : List (Fin (prime+K+4)))
    (_hdst : S.R (fullHeader _ .output) = (List.ofFn ambient).flatten++outputTail)
    (_hPublicationVolume : s*W < 2^Vr)
    (recovery : Bool) (_hAlphabet : 96 ≤ prime+K)
    (_hboundaryPush : mnProgPush ((callerFullLineProducer T Q b.hR b.hQ).gridProgram
      (P := P) (U := U) (A := prime+K) recovery) ≤ Cprog),
    let prepTime := sharedBoundaryPreparationTime p u l target s t D Fs.length radius coreWidth Vg Vr
    let prepStock := sharedBoundaryPreparationStock p u l target s t D Fs.length radius coreWidth Vg Vr
    let prepBudget := 2*Sizes.T n₀+
      (60*(1032+8*ct)+4*(callerFormatFactor ct cV cD+1)+14)*(Fs.length*s*p)
    prepTime ≤ prepBudget ∧ prepStock ≤ 8*prepBudget ∧
    ∃ prepared : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K),
    ∃ input : SetupInput (T+solverRegisterCount) (prime+K) D p u l target s t B W Fs.length radius coreWidth Vg Vr prepared,
    ∃ hwords : ∀ f j, prepared.R (fullHeader _ (.geometry f j)) = binSyms (formatWidths B Vg Vr f) (![s,coreWidth,radius] j),
    ∃ retained : GatherRetainedInput (T+solverRegisterCount) K s W (solverSource ∘ bank) Fs borrowed prepared,
    ∃ finalLines : List (List (Fin ((prime+K)+4))),
      List.Forall₂ (fun target line => line.length = (Sizes.s n₀ i)*W ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i‖ ≤ 1) ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i-target i‖ ≤ 3/(2:ℝ)^(Sizes.p n₀)))
        (inversePublicationTargets (Sizes.p n₀) Fs J) finalLines ∧
      ∃ v', ∃ m : ℕ, v'.user = v.user ∧ (m : ℝ) ≤ rawCallerTimeBudget F G n₀ ct cV cD p u s t Fs.length ∧
        mnSize (mk v' {S with R := Function.update S.R (fullHeader _ .output) (finalLines.flatten++outputTail)}) =
          mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+rawCallerStockBudget ct cV cD Cstock Cprog n₀ s t p Fs.length) depth
          (rawBoundaryProgram bank hinj b hstates rawSrc widthSource widths recovery) (mk v S) m
          (mk v' {S with R := Function.update S.R (fullHeader _ .output) (finalLines.flatten++outputTail)})

theorem selectedRawPublishedBoundaryRun_exec {T Q K : ℕ} {U P : Type}
    {body : P → Pr P (MachineTapes (T+solverRegisterCount)) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    SelectedRawPublishedBoundaryRun (body := body) bank hinj b hstates ct cV cD := by
  unfold SelectedRawPublishedBoundaryRun
  intro physicalBank physicalInj
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedPublishedBoundaryRun_exec (body := body) bank hinj b hstates ct cV cD
  obtain ⟨G,hG,hboundaryTime⟩ := selectedFullLineLifecycleTime_fast_le ct
  refine ⟨F,hF,Cstock,G,hG,?_⟩
  let pagesPush := mnProgPush (prepareReplicaPublicationPages (P := Empty) (Q := Q) (A := prime+K) (U := U))
  filter_upwards [hclass,selectedSharedBoundaryPreparationTime_le ct,
    selectedFullLineLifecycleStock_le ct,hboundaryTime,selectedCanonicalCallerCosts_le ct cV cD,
    selectedCallerFormat_profile ct cV cD,selectedClassSetupBounds_le (callerFormatFactor ct cV cD+1),
    selectedPublicationMetadata_le cD (1032+8*ct) 1,selectedPreparedCoreOriginsCost_le cD,selectedPublicationControlCosts_le cD,selectedPublicationPagesCost_le cD (1032+8*ct) (pagesPush+1),
    selectedPolynomialPublicationCosts_le hstates cD (816*(ct+5)+18) 8,selectedRawCallerGeometry ct]
    with n₀ hn hprep hboundaryStock hboundaryTime hprices hformats hsetupPrices hmetadataPrice horiginsPrice hcontrolPrices hpagesPrice hpublicationPrices hgeometryPrice
  intro h i _ _ u target L hu htarget gap C V bounds Fs hFs
  intro B W radius indices p s t l coreWidth Cprog depth Vg Vr replicaExp D hpush hbody hA
    v S borrowed rawSrc hrawSrc widthSource widths raw hword hreplicas hvolume hsource hexposure houtput
    hroutingLeft hsourceLeft htable hbank hleft hpubBlank hresultLeft hambientLeft hsolver hsolverLeft
    movement hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hprecision J hJ ambient hambient
    outputTail hdst hPublicationVolume recovery hAlphabet hboundaryPush
    prepTime prepStock prepBudget
  have hgeometry : RawCallerGeometry p u s t coreWidth radius l B W := hgeometryPrice h i u target htarget
  obtain ⟨hp,hst,hθ,hband,hpad,hroom,hr,hrw,hwide,hW⟩ := hgeometry
  have hcore : coreWidth ≤ s := by omega
  have hnonempty : 0 < indices.length := by
    have hh := fullCoreGather_nonempty s coreWidth radius movement.widthPositive hrw hroom.le
    simpa only [indices,L] using hh
  let j : Fin indices.length := ⟨0,hnonempty⟩
  have hdom := (bounds j).hdom
  let d := gap
  have huPositive : 1 ≤ u := (bounds j).hu
  have hwidth : 8*p ≤ 2^u := (bounds j).hwidth
  have hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1) := (bounds j).hgap
  have hbudget : (u : ℝ)*d ≤ p := by
    have hh := (bounds j).hbudget
    rw [(bounds j).hαu] at hh
    exact hh
  have hμ : 0 < 1/(8*(p : ℝ)) := by
    have hpR : (0 : ℝ) < p := by exact_mod_cast (by omega : 0 < p)
    positivity
  let solve := fun rhs : ZMod s → ℝ => Classical.choose
    (solves_exists (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) hμ hdom rhs)
  have hsolve (rhs : ZMod s → ℝ) : Solves (realMatrix s t p u) Finset.univ (solve rhs) rhs :=
    Classical.choose_spec (solves_exists (realMatrix s t p u) Finset.univ (1/(8*(p : ℝ))) hμ hdom rhs)
  let X := fun F : ZMod s → GaussianInt => solve (fun j => ((1/2 : ℂ)*value p (F j)).re)
  let Y := fun F : ZMod s → GaussianInt => solve (fun j => ((1/2 : ℂ)*value p (F j)).im)
  have hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F)
      (fun j => ((1/2 : ℂ)*value p (F j)).re) := fun F _ => hsolve _
  have hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F)
      (fun j => ((1/2 : ℂ)*value p (F j)).im) := fun F _ => hsolve _
  have hcanonicalFits := canonicalCallerFormat_fits p u l target s t B W Fs.length radius coreWidth Vg Vr
    (NeZero.one_le) (by omega)
  have hvolumeFit : s*W < 2^D := hcanonicalFits.2.2.2
  obtain ⟨hprepPrice,hretirePrice,hcontrolTimePrice,hcontrolStockPrice,hpubTimePrice,hpubStockPrice⟩ :=
    hprices h i u target Fs.length radius coreWidth Vg Vr hu htarget hband
      (hrw.trans hcore) hcore hExposeWidth hRouteWidth hReplicaVolume
  obtain ⟨_,_,hDsize⟩ := hformats h i u target Fs.length radius coreWidth Vg Vr hu htarget hband
    (hrw.trans hcore) hcore hExposeWidth hRouteWidth hReplicaVolume
  obtain ⟨hsetupTimePrice,hsetupStockPrice,hsetupRetirePrice⟩ := hsetupPrices h i D hDsize
  have hprepTime : prepTime ≤ prepBudget :=
    (hprep h i u target D Fs.length radius coreWidth Vg Vr hu htarget hband (hrw.trans hcore) hcore
      (by simpa [formatWidths] using raw.bitsFit 1)
      (by simpa [formatWidths] using raw.bitsFit 2)).trans hprepPrice
  have hprepStock : prepStock ≤ 8*prepBudget :=
    (sharedBoundaryPreparationStock_le_time p u l target t D Fs.length radius coreWidth Vg Vr).trans
      (Nat.mul_le_mul_left 8 hprepTime)
  refine ⟨hprepTime,hprepStock,?_⟩
  obtain ⟨v₁,prepared,input,hu₁,numerical,retained,pubReady,hwords,ready,hL,hI,hO,hframe,n₁,hn₁,he₁⟩ :=
    prepareSharedBoundaryCaller_exec_within body rawSrc widthSource widths bank Fs borrowed v S raw hword hreplicas
      hvolume hsource hexposure houtput hroutingLeft hsourceLeft htable hbank hleft hpubBlank hresultLeft hambientLeft
      hrawSrc hst hband hsolver hsolverLeft depth
  have hretire := sharedBoundaryRetireCost_le Fs prepared input hwords retained.wordLength
    retained.replicaLength retained.volumeLength rawSrc (solverSource widthSource) ready
    (inverseFullInputWidth_le_common p u l target t)
  refine ⟨prepared,input,hwords,retained,?_⟩
  let runStock := initializedPublishedRunStock Cstock Cprog n₀ ct cV cD (Sizes.p n₀) (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
  let retainedStock := 2*Sizes.T n₀+
      (3200+3*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+40))*(Fs.length*(s*W))
  let properPublicationStock := 20*Sizes.T n₀+62*Fs.length+122+retainedStock
  let properStock := Sizes.T n₀+(runStock+properPublicationStock)
  let runTime := initializedPublishedRunTime F n₀ ct cV cD (Sizes.p n₀) u (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
  let retainedTime : ℝ := 2*Sizes.T n₀+1700*(Fs.length*(s*W) : ℕ)+
      108*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
        (Fs.length*(s*W) : ℕ)*Sizes.d n₀*((Sizes.ℓ n₀ : ℝ)^Parameters.tau+1)
  let properPublicationTime := 14*Sizes.T n₀+37*Fs.length+82+retainedTime
  let properTime := (Sizes.T n₀ : ℝ)+(runTime+properPublicationTime)+Sizes.T n₀
  let setup := makeSetup input false movement.widthPositive raw.geometryFit raw.fit raw.bitsFit
  let gatherInput := makeGatherInput input hwords (solverSource ∘ bank) retained false movement
    raw.geometryFit raw.fit raw.bitsFit hA
  let g := gatherInput.ready
  let a := Nat.clog 2 indices.length
  let Vpub := g.D
  let wrapperTime := 1700*(Fs.length*(s*W))+100*Vpub+500+Sizes.T n₀+
    2*FixedStreamedBank.restoringTimeCost hstates a g.a ((L-2*radius)*W) Vpub
  let wrapperStock := 3200*(Fs.length*(s*W))+200*Vpub+800+Sizes.T n₀+
    FixedStreamedBank.restoringStockAllowance hstates a g.a ((L-2*radius)*W) Vpub
  let pubClass := gatherPublicationClass s coreWidth radius L
  let publicationPages := prepareReplicaPublicationPagesCost Vpub s pubClass.length W pubClass.indices.length
  let publicationPagesPush := pagesPush
  let origins := (coreSubsetPublicationWindows s coreWidth pubClass.length g.hwidth
    pubClass.indices pubClass.sublist).origins
  let geometryCost := PublicationGeometryControls.timeCost Vpub s L radius
  let retireGeometryCost := 2*((L-2*radius)+s)+5
  let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
  let retireDimensionCost := 2*(g.a+a+2^a)+7
  let metadata := Sizes.T n₀+2*Fs.length
  let originCost := Sizes.T n₀
  have hcount : setup.formats.length ≤ 3 := by
    change (formats (T+solverRegisterCount)).length ≤ 3
    simpa only [formats,List.length_ofFn] using Nat.le_refl 3
  obtain ⟨hsetupTime,hsetupStock,hsetupRetire⟩ := formattedClassSetupCosts_le setup hcount
  have htSetup := hsetupTime.trans hsetupTimePrice
  have hsSetup := hsetupStock.trans hsetupStockPrice
  have hrSetup := hsetupRetire.trans hsetupRetirePrice
  let oldMetadata := PackedTranspose.publicationHeaderVolume a g.a (L-2*radius) W Vpub s indices.length
  have hkeys : indices.length ≤ s := coreGatherIndices_length_le s coreWidth radius L movement.widthPositive
  have hspan : L = coreWidth+2*radius := rfl
  have hlength : L-2*radius ≤ 3*s := by omega
  have hwideWord := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hmetadata : oldMetadata ≤ metadata := by
    simpa only [one_mul] using hmetadataPrice h i indices.length g.a Fs.length (L-2*radius) W Vpub
      hkeys g.hpower.symm hlength hwideWord hRouteWidth
  let oldOriginCost := preparedCoreOriginsCost Vpub s coreWidth radius L
  have hOrigin : oldOriginCost ≤ originCost :=
    horiginsPrice h i Vpub coreWidth radius L movement.widthPositive hRouteWidth
  have hspanBound : L ≤ 3*s := by omega
  obtain ⟨hGeometry,hRetireGeometry,hDimension,hRetireDimension,hRetireOrigins⟩ :=
    hcontrolPrices h i Vpub indices.length g.a Fs.length L radius hkeys g.hpower.symm
      hspanBound (hrw.trans hcore) hRouteWidth
  change geometryCost ≤ Sizes.T n₀ at hGeometry
  change retireGeometryCost ≤ Sizes.T n₀ at hRetireGeometry
  change dimensionCost ≤ Sizes.T n₀+19*Fs.length at hDimension
  change retireDimensionCost ≤ Sizes.T n₀+2*Fs.length at hRetireDimension
  have hOriginCount : origins.length = indices.length := by
    change (pubClass.indices.map (coreStart coreWidth)).length = indices.length
    rw [List.length_map]
    rfl
  have hOriginRetire : 2*(origins.length*Vpub+origins.length)+5 ≤ Sizes.T n₀ := by
    simpa only [hOriginCount] using hRetireOrigins
  have hpacketRows : 1 ≤ L-2*radius := by have hh := g.hwidth; omega
  have hpacketSpan : L-2*radius ≤ s := by omega
  have hwordPos : 1 ≤ W := by omega
  have hpagePrice := hpagesPrice h i Vpub pubClass.length W indices.length
    hRouteWidth hwideWord hpacketSpan hkeys
  change (publicationPagesPush+1)*publicationPages ≤ Sizes.T n₀ at hpagePrice
  have hpagesTime : publicationPages ≤ Sizes.T n₀ := by
    nlinarith only [hpagePrice,Nat.zero_le (publicationPagesPush*publicationPages)]
  have hpagesStock : publicationPagesPush*publicationPages ≤ Sizes.T n₀ := by
    nlinarith only [hpagePrice,Nat.zero_le publicationPages]
  have hcapacity : indices.length ≤ 2^a := Nat.le_pow_clog (by decide) indices.length
  let paddedVolume := 2^a*2^g.a*((L-2*radius)*W)
  have hOldVolume : indices.length*(2^g.a*((L-2*radius)*W)) ≤ paddedVolume := by
    have hh := Nat.mul_le_mul_right (2^g.a*((L-2*radius)*W)) hcapacity
    simpa only [paddedVolume,Nat.mul_assoc] using hh
  have hretained := retainedPublicationCosts_le (K := K) (U := U) hstates a g.a (L-2*radius) Vpub W
    indices.length pubClass g.hwidth rfl hpacketSpan hpacketRows hwordPos hcapacity _ hOldVolume
  have hPaddedVolume : paddedVolume ≤ 3*(Fs.length*(s*W)) := by
    have hh := publicationPaddedVolume_le
      (coreSubsetPublicationWindows s coreWidth pubClass.length g.hwidth pubClass.indices pubClass.sublist)
      hpacketSpan g.a W
    have hc : (coreSubsetPublicationWindows s coreWidth pubClass.length g.hwidth pubClass.indices
      pubClass.sublist).origins.length = indices.length := by
      change (pubClass.indices.map (coreStart coreWidth)).length = indices.length
      rw [List.length_map]
      rfl
    rw [hc] at hh
    change 2^a*2^g.a*((L-2*radius)*W) ≤ 3*(2^g.a*(s*W)) at hh
    simpa only [paddedVolume,g.hpower] using hh
  have hRetainedTime : PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
      W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W))) ≤ wrapperTime := by
    have hh := hretained.1
    change _ ≤ 500*paddedVolume+200*(2^g.a*(s*W))+100*Vpub+500+publicationPages+
      2*FixedStreamedBank.restoringTimeCost hstates a g.a ((L-2*radius)*W) Vpub at hh
    change _ ≤ 1700*(Fs.length*(s*W))+100*Vpub+500+Sizes.T n₀+
      2*FixedStreamedBank.restoringTimeCost hstates a g.a ((L-2*radius)*W) Vpub
    apply hh.trans
    rw [← g.hpower]
    dsimp only [s,Vpub,publicationPages] at hPaddedVolume hpagesTime hpagesStock ⊢
    omega
  have hRetainedStock : PackedTranspose.retainedPublicationStock (K := K) (U := U) hstates a g.a
      (L-2*radius) Vpub W indices.length pubClass ≤ wrapperStock := by
    have hh := hretained.2
    change _ ≤ 1000*paddedVolume+200*(2^g.a*(s*W))+200*Vpub+800+
      publicationPagesPush*publicationPages+
      FixedStreamedBank.restoringStockAllowance hstates a g.a ((L-2*radius)*W) Vpub at hh
    change _ ≤ 3200*(Fs.length*(s*W))+200*Vpub+800+Sizes.T n₀+
      FixedStreamedBank.restoringStockAllowance hstates a g.a ((L-2*radius)*W) Vpub
    apply hh.trans
    rw [← g.hpower]
    dsimp only [s,Vpub,publicationPages] at hPaddedVolume hpagesTime hpagesStock ⊢
    omega
  let oldProperPublicationTime := (geometryCost+(oldOriginCost+(dimensionCost+((6*oldMetadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*oldMetadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ)
  let oldProperPublicationStock := (3*geometryCost+(3*oldOriginCost+(2*dimensionCost+(2*(6*oldMetadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass))))
  have hpCore : 1 ≤ p := by have := h.thirteen_le_p; omega
  have hpreparePacket : p^2 ≤ L-2*radius := by
    have hh := amortizedCoreWidth_preparation ct p u hpCore
    change p^2+(PhaseCellBand.width p u)^2 ≤ coreWidth at hh
    omega
  have hgroup : L ∈ coreGatherLengths s coreWidth radius := by
    rw [hspan]
    simp [coreGatherLengths]
  have hkernel := hpublicationPrices h i coreWidth radius L g.a W Vpub
    (coreSubsetPublicationWindows s coreWidth pubClass.length g.hwidth pubClass.indices pubClass.sublist)
    g.hwidth (by rfl) hrw hgroup hOriginCount hpreparePacket hpacketSpan hwordPos hRouteWidth
    (by rw [←g.hpower]; exact hReplicaVolume)
  dsimp only at hkernel
  have hWindowCount : (coreSubsetPublicationWindows s coreWidth pubClass.length g.hwidth
      pubClass.indices pubClass.sublist).origins.length = indices.length := hOriginCount
  rw [hWindowCount] at hkernel
  have hkernelTime : (wrapperTime : ℝ) ≤ retainedTime := by
    have hh := hkernel.1
    change (1700*(2^g.a*(s*W) : ℕ)+100*Vpub+500+Sizes.T n₀+
      2*FixedStreamedBank.restoringTimeCost hstates a g.a ((L-2*radius)*W) Vpub : ℝ) ≤ _ at hh
    simpa only [wrapperTime,retainedTime,g.hpower,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] using hh
  have hkernelStock : wrapperStock ≤ retainedStock := by
    have hh := hkernel.2
    change 3200*(2^g.a*(s*W))+200*Vpub+800+Sizes.T n₀+
      FixedStreamedBank.restoringStockAllowance hstates a g.a ((L-2*radius)*W) Vpub ≤ _ at hh
    simpa only [wrapperStock,retainedStock,g.hpower] using hh
  have hproperPubTime : (oldProperPublicationTime : ℝ) ≤ properPublicationTime := by
    have hb : oldProperPublicationTime ≤ 14*Sizes.T n₀+37*Fs.length+82+wrapperTime := by
      dsimp only [oldProperPublicationTime]
      omega
    have hbR := (Nat.cast_le (α := ℝ)).mpr hb
    dsimp only [properPublicationTime]
    push_cast only [Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat] at hbR
    linarith only [hbR,hkernelTime]
  have hproperPubStock : oldProperPublicationStock ≤ properPublicationStock := by
    have hb : oldProperPublicationStock ≤ 20*Sizes.T n₀+62*Fs.length+122+wrapperStock := by
      dsimp only [oldProperPublicationStock]
      omega
    dsimp only [properPublicationStock]
    omega
  let oldProperTime := initializedPublishedTime setup.timeCost runTime oldProperPublicationTime setup.retireCost
  let oldProperStock := setup.stock+(runStock+oldProperPublicationStock)
  have hproperTime : oldProperTime ≤ properTime := by
    have ht : (setup.timeCost : ℝ) ≤ Sizes.T n₀ := by exact_mod_cast htSetup
    have hr : (setup.retireCost : ℝ) ≤ Sizes.T n₀ := by exact_mod_cast hrSetup
    have hpub : (oldProperPublicationTime : ℝ) ≤ properPublicationTime := hproperPubTime
    dsimp only [oldProperTime,properTime,initializedPublishedTime]
    linarith only [ht,hr,hpub]
  have hproperStock : oldProperStock ≤ properStock :=
    add_le_add hsSetup (Nat.add_le_add_left hproperPubStock runStock)
  have hpreparedOutput : prepared.R (fullHeader _ .output) = S.R (fullHeader _ .output) := by
    apply hframe
    · exact (solverRegister_ne_header T (.scratch 4) .output).symm
    all_goals first
      | exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro j; exact (fullHeader_injective _).ne (by intro he; cases he)
      | intro f j; exact (fullHeader_injective _).ne (by intro he; cases he)
  obtain ⟨rows,finalLines,haccuracy,v₂,n₂,hu₂,hn₂,hstock,he₂⟩ :=
    hn h i u target hu htarget gap C V bounds Fs hFs D Cprog depth Vg Vr replicaExp hpush hbody hwide hA
      v₁ prepared borrowed input raw.geometryFit raw.fit raw.bitsFit movement hwords retained (numerical false)
      gatherInput hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hp hprecision J hJ ambient hambient outputTail
      pubReady (hpreparedOutput.trans hdst) hPublicationVolume rawSrc
      (hrawSrc.ne (by decide)) (solverSource widthSource) recovery hAlphabet d hst huPositive hwidth hθ hgap hbudget
      hband hpad hroom hr hrw hW hvolumeFit X Y hX hY ready hboundaryPush
  have hproperCode := sharedProperProgram_eq (T := T+solverRegisterCount) (P := P) input hwords (solverSource ∘ bank)
    retained movement (Nat.le_refl _) raw.geometryFit raw.fit raw.bitsFit hA gatherInput
    ((Fin.castAdd_injective _ _).comp hinj) b hstates
  rw [hproperCode] at he₂
  let keys := PackedExactBatch.ofCommonCoreClass_keys (A := prime+K)
    (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target
    (amortizedCoreWidth ct (Sizes.p n₀)) L (Real.sqrt (u : ℝ)) gap C V bounds Fs.reverse
    (by intro F hmem j; exact hFs F (List.mem_reverse.mp hmem) j) hp hprecision J hJ
  let properLines := List.ofFn (fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j))
  let M : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K) :=
    {prepared with R := Function.update prepared.R (fullHeader _ .output) (properLines.flatten++outputTail)}
  let solveStock := (Cprog+1)*(((1312000+756)*(1032+8*ct)+504)*(Fs.length*s*p)+2*Sizes.T n₀)
  let volume := Fs.length*s*(2*p+13)
  let generateStock := Sizes.T n₀
  let prepareStock := 13*(4*(Sizes.p n₀)+5)+(generateStock+(2*(4*B+5)+(solveStock+(480*volume+86))))
  let publicationStock := Sizes.T n₀+(5597*(1032+8*ct))*(Fs.length*s*p)
  let solveTime := 2624001*(Sizes.T n₀ : ℝ)+(Fs.length : ℝ)*G*t*
      (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n₀)*(p : ℝ)^(129/128 : ℝ)+410
  let generateTime := Sizes.T n₀
  let prepareTime := (((4*p+5)+generateTime+(4*B+5)+(242*volume+45)+(2*B+3) : ℕ) : ℝ)+solveTime
  let publicationTime := Sizes.T n₀+(1335*(1032+8*ct))*(Fs.length*s*p)
  let retireSetupCost := Sizes.T n₀+(2*headerCount+2*(1032+8*ct))*(Fs.length*s*p)
  let r := fullLineGridRecord (A := prime+K) p u l target t Fs
  let producer := callerFullLineProducer T Q b.hR b.hQ
  let tape := descriptorScheduleTape producer.gridWork FamilyDispatchInput.words [r]
  let oldSolveTime := setupTime p u l target s t Fs.length+
    ((r.gridCost p l t producer.gridWork+22*tape.length+26)+(2*(∑ j, (r.words j).length)+607))
  let oldSolveStock := setupStock p u l target s t Fs.length+
    (31*tape.length+9+(Cprog+1)*producer.gridStock p l t r)
  have hsolverReady := callerSolverWidthState_ready rawSrc p u l target t W radius coreWidth Fs prepared
    ready.raw ready.zero ready.blank (fun j => ready.left (.input j)) ready.input
  have hgridReady := fullLineGridRecord_ready (A := prime+K) p u l target t
    huPositive hwidth hbudget hband hpad Fs hFs
  have hsolveTime : (oldSolveTime : ℝ) ≤ solveTime :=
    hboundaryTime h i (MachineTapes (T+solverRegisterCount)) Q (prime+K) U (callerFullLineInput T rawSrc)
      producer d u target Fs v₁ _ hu htarget hband hsolverReady hgridReady
  have hsolveStock : oldSolveStock ≤ solveStock :=
    hboundaryStock h i (MachineTapes (T+solverRegisterCount)) Q (prime+K) Cprog U (callerFullLineInput T rawSrc)
      producer d u target Fs v₁ _ hu htarget hband hsolverReady hgridReady
  let oldGenerateTime := ((2*p+13)*(4*D+10)+4*D+8)+
    boundaryCountExportCost D s coreWidth (2*p+13)+(2*D+2)
  let oldGenerateStock := 2*(4*D+4)+3*boundaryCountExportCost D s coreWidth (2*p+13)
  have hcontrols := boundaryControlCosts_le p D s coreWidth movement.widthPositive hroom
  have hgenerateTime : (oldGenerateTime : ℝ) ≤ generateTime := by
    have ht := hcontrols.1.trans hcontrolTimePrice
    exact_mod_cast ht
  have hgenerateStock : oldGenerateStock ≤ generateStock := hcontrols.2.trans hcontrolStockPrice
  let oldPrepareTime := (4*p+5)+(oldGenerateTime+((4*B+5)+((oldSolveTime+(242*volume+45))+(2*B+3))))
  let oldPrepareStock := 13*(4*p+5)+(oldGenerateStock+(2*(4*B+5)+(oldSolveStock+(480*volume+86))))
  have hprepareTime : (oldPrepareTime : ℝ) ≤ prepareTime := by
    dsimp only [oldPrepareTime,prepareTime]
    push_cast
    linarith only [hsolveTime,hgenerateTime]
  have hprepareStock : oldPrepareStock ≤ prepareStock := by
    dsimp only [oldPrepareStock,prepareStock]
    omega
  let loadCost := 6*boundarySeamHeaderVolume p s coreWidth W D Fs.length+67
  let retireCost := 2*boundarySeamHeaderVolume p s coreWidth W D Fs.length+23
  let clearCost := 2*boundaryTemporaryHeaderVolume p s coreWidth+13
  let oldPublicationTime := (loadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+retireCost)+clearCost
  have hpublication := boundaryPublicationCosts_le p s coreWidth W D Fs.length
    (NeZero.one_le) movement.widthPositive hroom hW
  have hpublicationTime : oldPublicationTime ≤ publicationTime := hpublication.1.trans hpubTimePrice
  have hpublicationStock : 2*loadCost+13*boundarySeamBudget r.inputs.length D s W ≤ publicationStock := hpublication.2.trans hpubStockPrice
  let boundaryState := callerPreparedBoundaryState (solverSource widthSource) p s coreWidth M
  let pairs := boundarySeamMasterCopies (boundaryArchiveSource (T+solverRegisterCount))
    (boundaryArchiveDestination (T+solverRegisterCount))
    (seamMasterSources (T+solverRegisterCount) (solverSource ∘ rawSrc) (solverSource widthSource))
  let oldLoadCost := (pairs.map (fun pair => 6*(boundaryState.R pair.1).length+6)).sum+1
  let oldRetireCost := 2*(pairs.map (fun pair => (boundaryState.R pair.1).length)).sum+2*pairs.length+1
  let oldClearCost := 2*((callerPreparedTemporaryHeaders (T+solverRegisterCount)).map
    (fun i => (boundaryState.R i).length)).sum+2*(callerPreparedTemporaryHeaders (T+solverRegisterCount)).length+1
  have hclear : oldClearCost = clearCost :=
    callerPreparedBoundaryClearCost_eq (solverSource widthSource) p s coreWidth M
  have readyM : BoundaryCallerReady rawSrc (solverSource widthSource) p u l target t W D radius coreWidth Fs M :=
    ready.update_output (properLines.flatten++outputTail)
  have hcopies := callerPreparedBoundaryMasterCopyCosts_eq p u l target t B W D Fs.length radius coreWidth
    (solverSource ∘ rawSrc) (solverSource widthSource) (boundaryArchiveSource (T+solverRegisterCount))
    (boundaryArchiveDestination (T+solverRegisterCount)) M readyM.raw readyM.arithmeticWidth readyM.scalars
  have hload : oldLoadCost = loadCost := hcopies.1
  have hretireCopies : oldRetireCost = retireCost := hcopies.2
  have htime : (n₂ : ℝ) ≤ oldProperTime+
      ((oldPrepareTime+((oldLoadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+oldRetireCost)+oldClearCost) : ℕ) : ℝ) := hn₂
  rw [hload,hretireCopies,hclear] at htime
  have htimeBound : (n₂ : ℝ) ≤ properTime+(prepareTime+(publicationTime : ℝ)) := by
    change (n₂ : ℝ) ≤ oldProperTime+((oldPrepareTime+oldPublicationTime : ℕ) : ℝ) at htime
    rw [Nat.cast_add] at htime
    have hpub : (oldPublicationTime : ℝ) ≤ publicationTime := by exact_mod_cast hpublicationTime
    linarith only [htime,hproperTime,hprepareTime,hpub]
  let ys := finalLines.flatten++outputTail
  obtain ⟨v₃,m,hu₃,htime,hsize,he⟩ := finishSharedBoundaryCaller_exec
    (T := T) (Q := Q) (A := prime+K) (P := P) (U := U) body S prepared hI hO hL hframe
    (raw.sharedPreparationHeaders_blank hword hreplicas hvolume) (hsolver _) ys
    (.seq (callerCanonicalInputPreparation rawSrc)
      (gatherPreparationProgram (solverSource ∘ rawSrc) (solverSource widthSource) (solverSource ∘ widths)))
    (.seq (sharedProperProgram (solverSource ∘ bank) ((Fin.castAdd_injective _ _).comp hinj) b hstates)
      (callerBoundaryCompletion rawSrc b.hR b.hQ (solverSource widthSource) recovery))
    prepBudget (properTime+(prepareTime+(publicationTime : ℝ))) (8*prepBudget)
    (max properStock (prepareStock+publicationStock)) depth v v₁ v₂ n₁ n₂ hu₁ hu₂ (hn₁.trans hprepTime) htimeBound hstock
    (he₁.mono (by intro k z hz; exact hz.trans (Nat.add_le_add_left hprepStock _)))
    (he₂.mono (by
      intro k z hz
      change mnSize z+k ≤ mnSize (mk v₁ prepared)+depth+
        max oldProperStock (oldPrepareStock+(2*oldLoadCost+13*boundarySeamBudget r.inputs.length D s W)) at hz
      rw [hload] at hz
      exact hz.trans (Nat.add_le_add_left
        (max_le_max hproperStock (add_le_add hprepareStock hpublicationStock)) _)))
  have hB := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hBwide : B ≤ (1032+8*ct)*p := by nlinarith only [hB]
  have hNpos : 1 ≤ Fs.length := by rw [g.hpower]; exact Nat.two_pow_pos _
  have hcompactStock : 8*prepBudget+max properStock (prepareStock+publicationStock) ≤
      rawCallerStockBudget ct cV cD Cstock Cprog n₀ s t p Fs.length :=
    rawCallerStock_le ct cV cD Cstock Cprog n₀ p s t D B W Fs.length
      hNpos NeZero.one_le hpCore (h.good.lt i).le hDsize hBwide hwideWord
  refine ⟨finalLines,haccuracy,v₃,m,hu₃,?_,hsize,?_⟩
  · have hretireR : (sharedBoundaryRetireCost prepared : ℝ) ≤ retireSetupCost := by
      have hr := hretire.trans hretirePrice
      exact_mod_cast hr
    change (m : ℝ) ≤ (prepBudget : ℝ)+(properTime+(prepareTime+(publicationTime : ℝ)))+
      (sharedBoundaryRetireCost prepared : ℝ) at htime
    have hcompact : (prepBudget : ℝ)+(properTime+(prepareTime+(publicationTime : ℝ)))+
        (retireSetupCost : ℝ) ≤ rawCallerTimeBudget F G n₀ ct cV cD p u s t Fs.length :=
      rawCallerTime_le F G n₀ ct cV cD p u s t D B W Fs.length
        hNpos NeZero.one_le hpCore hDsize hBwide hwideWord
    linarith only [htime,hretireR,hcompact]
  · exact he.mono (by
      intro k z hz
      change mnSize z+k ≤ mnSize (mk v S)+depth+8*prepBudget+
        max properStock (prepareStock+publicationStock) at hz
      apply hz.trans
      simpa only [Nat.add_assoc] using Nat.add_le_add_left hcompactStock (mnSize (mk v S)+depth))

end IntegerMultBounds.MathlibTM2.Cost
