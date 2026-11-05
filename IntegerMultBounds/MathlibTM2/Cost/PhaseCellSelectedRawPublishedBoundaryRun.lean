module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublishedBoundaryRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerRawProgram
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerSharedBoundaryVolume
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedSharedPreparationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellBoundaryControlCost
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
    ∀ (D Cprog depth Vg Vr replicaExp : ℕ),
    ∀
    (_hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).clock (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).work (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).count (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).spare (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).result b.hR b.hQ)) ≤ Cprog)
    (_hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (_hwide : (Sizes.s n₀ i)+(amortizedCoreWidth ct (Sizes.p n₀))+2*radius < 2^B)
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
    (hp : 4 ≤ p) (hprecision : p+2 ≤ target)
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact s t (Real.sqrt (u : ℝ)) = 1)
    (ambient : Fin (2^replicaExp) → List (Fin (prime+K+4))) (_hambient : ∀ j, (ambient j).length = s*W)
    (outputTail : List (Fin (prime+K+4)))
    (_hdst : S.R (fullHeader _ .output) = (List.ofFn ambient).flatten++outputTail)
    (_hPublicationVolume : s*W < 2^Vr)
    (recovery : Bool) (_hAlphabet : 96 ≤ prime+K)
    (d : ℝ) (hst : s < t) (_huPositive : 1 ≤ u) (_hwidth : 8*p ≤ 2^u)
    (_hθ : 1/(4*(p : ℝ)) ≤ (t : ℝ)/s-1) (_hgap : (1 : ℝ)/4 ≤ d*((t : ℝ)/s-1))
    (_hbudget : (u : ℝ)*d ≤ p) (hband : PhaseCellBand.width p u ≤ s)
    (_hpad : 2*((s/(t-s)+1)-2*PhaseCellBand.width p u) ≤ 2^l+1)
    (_hroom : 3*coreWidth < s) (_hr : 0 < radius) (_hrw : radius ≤ coreWidth)
    (_hW : 2*p+13 ≤ W) (_hvolumeFit : s*W < 2^D)
    (X Y : (ZMod s → GaussianInt) → ZMod s → ℝ)
    (_hX : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (X F) (fun j => ((1/2 : ℂ)*value p (F j)).re))
    (_hY : ∀ F ∈ Fs, Solves (realMatrix s t p u) Finset.univ (Y F) (fun j => ((1/2 : ℂ)*value p (F j)).im))
    (_hboundaryPush : mnProgPush ((callerFullLineProducer T Q b.hR b.hQ).gridProgram
      (P := P) (U := U) (A := prime+K) recovery) ≤ Cprog),
    let prepTime := sharedBoundaryPreparationTime p u l target s t D Fs.length radius coreWidth Vg Vr
    let prepStock := sharedBoundaryPreparationStock p u l target s t D Fs.length radius coreWidth Vg Vr
    let prepBudget := sharedPreparationAllowance ct (Sizes.T n₀) p s t D Fs.length
    prepTime ≤ prepBudget ∧ prepStock ≤ 8*prepBudget ∧
    ∃ prepared : Stacks (MachineTapes (T+solverRegisterCount)) (prime+K),
    ∃ input : SetupInput (T+solverRegisterCount) (prime+K) D p u l target s t B W Fs.length radius coreWidth Vg Vr prepared,
    ∃ hwords : ∀ f j, prepared.R (fullHeader _ (.geometry f j)) = binSyms (formatWidths B Vg Vr f) (![s,coreWidth,radius] j),
    ∃ retained : GatherRetainedInput (T+solverRegisterCount) K s W (solverSource ∘ bank) Fs borrowed prepared,
    let setup := makeSetup input false movement.widthPositive raw.geometryFit raw.fit raw.bitsFit
    let gatherInput : setup.GatherInput
      (makeGatherSeed input hwords (solverSource ∘ bank) retained movement (Nat.le_refl _) hA)
      (numericTable (T+solverRegisterCount)) (masterSources (T+solverRegisterCount)) (geometrySources (T+solverRegisterCount) 3) :=
      makeGatherInput input hwords (solverSource ∘ bank) retained false movement raw.geometryFit raw.fit raw.bitsFit hA
    let g := gatherInput.ready
    let pubClass := gatherPublicationClass (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let runTime := initializedPublishedRunTime F n₀ ct cV cD (Sizes.p n₀) u (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let runStock := initializedPublishedRunStock Cstock Cprog n₀ ct cV cD (Sizes.p n₀) (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let origins := (coreSubsetPublicationWindows (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      pubClass.length g.hwidth pubClass.indices pubClass.sublist).origins
    let a := Nat.clog 2 indices.length
    let Vpub := g.D
    let geometryCost := PublicationGeometryControls.timeCost Vpub (Sizes.s n₀ i) L radius
    let retireGeometryCost := 2*((L-2*radius)+Sizes.s n₀ i)+5
    let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
    let retireDimensionCost := 2*(g.a+a+2^a)+7
    let metadata := PackedTranspose.publicationHeaderVolume a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let properTime := initializedPublishedTime setup.timeCost runTime (geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ) setup.retireCost
    let properStock := (setup.stock+(runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass))))))
    let solveTime := 2624001*(Sizes.T n₀ : ℝ)+(Fs.length : ℝ)*G*t*
      (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n₀)*(p : ℝ)^(129/128 : ℝ)+410
    let solveStock := (Cprog+1)*(((1312000+756)*(1032+8*ct)+504)*(Fs.length*s*p)+2*Sizes.T n₀)
    let volume := Fs.length*s*(2*p+13)
    let generateTime := boundaryControlTimeBound p D s
    let generateStock := boundaryControlStockBound p D s
    let prepareTime := (((4*p+5)+generateTime+(4*B+5)+(242*volume+45)+(2*B+3) : ℕ) : ℝ)+solveTime
    let prepareStock := 13*(4*(Sizes.p n₀)+5)+(generateStock+(2*(4*B+5)+(solveStock+(480*volume+86))))
    let publicationTime := boundaryPublicationTimeBound Fs.length D s W
    let publicationStock := boundaryPublicationStockBound Fs.length D s W
    let retireSetupCost := sharedBoundaryRetireAllowance W Fs.length s D B Vg Vr
    ∃ finalLines : List (List (Fin ((prime+K)+4))),
      List.Forall₂ (fun target line => line.length = (Sizes.s n₀ i)*W ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i‖ ≤ 1) ∧
        (∀ i : ZMod (Sizes.s n₀ i), ‖pairedCellRead (Sizes.p n₀) W line i-target i‖ ≤ 3/(2:ℝ)^(Sizes.p n₀)))
        (inversePublicationTargets (Sizes.p n₀) Fs J) finalLines ∧
      ∃ v', ∃ m : ℕ, v'.user = v.user ∧ (m : ℝ) ≤ (prepBudget : ℝ)+(properTime+(prepareTime+(publicationTime : ℝ)))+(retireSetupCost : ℝ) ∧
        mnSize (mk v' {S with R := Function.update S.R (fullHeader _ .output) (finalLines.flatten++outputTail)}) =
          mnSize (mk v S) ∧
        ExecWithin body (fun d z => mnSize z+d ≤ mnSize (mk v S)+depth+8*prepBudget+max properStock (prepareStock+publicationStock)) depth
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
  filter_upwards [hclass,selectedSharedBoundaryPreparationTime_le ct,
    selectedFullLineLifecycleStock_le ct,hboundaryTime] with n₀ hn hprep hboundaryStock hboundaryTime
  intro h i _ _ u target L hu htarget gap C V bounds Fs hFs
  intro B W radius indices p s t l coreWidth D Cprog depth Vg Vr replicaExp hpush hbody hwide hA
    v S borrowed rawSrc hrawSrc widthSource widths raw hword hreplicas hvolume hsource hexposure houtput
    hroutingLeft hsourceLeft htable hbank hleft hpubBlank hresultLeft hambientLeft hsolver hsolverLeft
    movement hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hp hprecision J hJ ambient hambient
    outputTail hdst hPublicationVolume recovery hAlphabet d hst huPositive hwidth hθ hgap hbudget hband
    hpad hroom hr hrw hW hvolumeFit X Y hX hY hboundaryPush
    prepTime prepStock prepBudget
  have hcore : coreWidth ≤ s := by omega
  have hprepTime : prepTime ≤ prepBudget := hprep h i u target D Fs.length radius coreWidth Vg Vr
    hu htarget hband (hrw.trans hcore) hcore
    (by simpa [formatWidths] using raw.bitsFit 1)
    (by simpa [formatWidths] using raw.bitsFit 2)
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
  intro setup gatherInput g pubClass runTime runStock
    origins a Vpub geometryCost retireGeometryCost dimensionCost retireDimensionCost metadata originCost
    properTime properStock
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
  intro solveTime solveStock volume generateTime generateStock prepareTime prepareStock
    publicationTime publicationStock retireSetupCost
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
  have hgenerateTime : (oldGenerateTime : ℝ) ≤ generateTime := by exact_mod_cast hcontrols.1
  have hgenerateStock : oldGenerateStock ≤ generateStock := hcontrols.2
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
  have hpublicationTime : oldPublicationTime ≤ publicationTime := hpublication.1
  have hpublicationStock : 2*loadCost+13*boundarySeamBudget r.inputs.length D s W ≤ publicationStock := hpublication.2
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
  have htime : (n₂ : ℝ) ≤ properTime+
      ((oldPrepareTime+((oldLoadCost+(3*boundarySeamBudget r.inputs.length D s W+1)+oldRetireCost)+oldClearCost) : ℕ) : ℝ) := hn₂
  rw [hload,hretireCopies,hclear] at htime
  have htimeBound : (n₂ : ℝ) ≤ properTime+(prepareTime+(publicationTime : ℝ)) := by
    change (n₂ : ℝ) ≤ properTime+((oldPrepareTime+oldPublicationTime : ℕ) : ℝ) at htime
    rw [Nat.cast_add] at htime
    have hpub : (oldPublicationTime : ℝ) ≤ publicationTime := by exact_mod_cast hpublicationTime
    linarith only [htime,hprepareTime,hpub]
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
        max properStock (oldPrepareStock+(2*oldLoadCost+13*boundarySeamBudget r.inputs.length D s W)) at hz
      rw [hload] at hz
      exact hz.trans (Nat.add_le_add_left
        (max_le_max_left properStock (add_le_add hprepareStock hpublicationStock)) _)))
  refine ⟨finalLines,haccuracy,v₃,m,hu₃,?_,hsize,he⟩
  have hretireR : (sharedBoundaryRetireCost prepared : ℝ) ≤ retireSetupCost := by exact_mod_cast hretire
  change (m : ℝ) ≤ (prepBudget : ℝ)+(properTime+(prepareTime+(publicationTime : ℝ)))+
    (sharedBoundaryRetireCost prepared : ℝ) at htime
  linarith only [htime,hretireR]

end IntegerMultBounds.MathlibTM2.Cost
