module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublishedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupNumericalReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupGatherReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublishedPreparation

/-! Execute the fixed typed caller's class setup, selected numerical/publication
run and owned-word cleanup. Setup and seed come from the produced ordinary-input
contracts; physical address obligations are derived from the caller allocation.
Every stage receives the preceding actual host state. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Stack
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast.Main
open ComputedClassBanks CallerLayout CommonClassGeometry

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-- Numerical and gather time before publication and class setup/retirement. -/
noncomputable def initializedPublishedRunTime (F : ℝ) (n₀ ct cV cD p u s t D B W N : ℕ) : ℝ :=
  (((126*D+132 : ℕ) : ℝ)+((Sizes.T n₀+(coreExposureTrafficFactor cV (1032+8*ct)+40*cV+48*cD+6185 : ℕ)*
        (N*s*W : ℕ)+432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (N*s*W : ℕ)*Sizes.d n₀*((Sizes.ℓ n₀ : ℝ)^Parameters.tau+1))+
        8*Sizes.T n₀+F*N*(t : ℝ)*
        (1+(PhaseCellBand.width p u : ℝ)^2/Sizes.d n₀)*(p : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*N+32*(B : ℝ)+35))

/-- The corresponding bound on intermediate numerical/gather stock. -/
noncomputable def initializedPublishedRunStock (Cstock Cprog n₀ ct cV cD p s t D B W N : ℕ) : ℕ :=
  (3*(100*D+105)+
        (2*(24*B+25)+((Sizes.T n₀+(3*coreExposureTrafficFactor cV (1032+8*ct)+60*cV+72*cD+268+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(N*s*W))+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*N*t*p+
          495*D+24*N)))

noncomputable def initializedPublishedTime (setupTime : ℕ) (runTime : ℝ) (publicationTime retireTime : ℕ) : ℝ :=
  (setupTime : ℝ)+(runTime+(publicationTime : ℝ))+(retireTime : ℝ)

/-- Unit-ball preservation and error on the owned cores of actual output rows. -/
noncomputable def publishedCoreRowsAccurate (A q w : ℕ) {s width replicas : ℕ} [NeZero s]
    (pubClass : CorePublicationClass s width) (rows : Fin replicas → ℕ → List GaussianInt)
    (target : Fin replicas → ZMod s → ℂ) (error : ℝ) : Prop :=
  ∀ j k, k ∈ pubClass.indices →
    let out := packedIntervalRead (s := s) q w (coreStart width k) (Fast.cstream A w (rows j k))
    (∀ z ∈ ownedCore s width k, ‖out z‖ ≤ 1) ∧
      PhaseCellInterface.ErrorOn (ownedCore s width k) out (target j) error

/-- The normalized exact-inverse target for each retained input replica. -/
noncomputable def publishedInverseTarget (p : ℕ) {s replicas : ℕ} [NeZero s]
    (J : (ZMod s → ℂ) →L[ℂ] (ZMod s → ℂ)) (replica : Fin replicas → ZMod s → GaussianInt) :
    Fin replicas → ZMod s → ℂ :=
  fun j => (((2 : ℂ)^inverseNormalizationShift p)⁻¹ • J)
    ((1/2 : ℂ) • fun z => ShortConv.value p (replica j z))

noncomputable def publishedInverseError (p : ℕ) : ℝ := 3/(2 : ℝ)^p

theorem selectedInitializedPublishedClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P (MachineTapes T) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    let physicalBank := CallerLayout.bank bank
    let physicalInj := bank_injective bank hinj
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (_h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] [NeZero (Sizes.t n₀ i)] (u target L : ℕ)
    (_hu : u ≤ Sizes.p n₀) (_htarget : target ≤ ct*Sizes.p n₀)
    (α gap : ℝ) (C : ZMod (Sizes.s n₀ i) → GaussianInt)
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
          (localityDepth (Sizes.p n₀) target)).2) (V := V j) α gap C)
    (Fs : List (ZMod (Sizes.s n₀ i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n₀) (F j)‖ ≤ 1),
    let B := inverseCallerWordWidth (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
    let W := packedHaloCommonWidth (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.s n₀ i) u (target+1) 2
    let radius := localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u
    let indices := coreGatherIndices (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := (prime+K))
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) indices[j.val] (V j) α gap C Fs.reverse (bounds j)
        (by intro F hmem i; exact hF F (List.mem_reverse.mp hmem) i)
    ∀ (D Cprog depth Vg Vr replicaExp : ℕ),
    let rg := numericTable T
    ∀
    (_hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).clock (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).work (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).src (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).saved (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).count (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).tmp (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).spare (plan (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj)).result b.hR b.hQ)) ≤ Cprog)
    (_hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (_hwide : (Sizes.s n₀ i)+(amortizedCoreWidth ct (Sizes.p n₀))+2*radius < 2^B)
    (hA : 4 ≤ (prime+K))
    (v : HS (MachineTapes T) Q (prime+K) U) (base : Stacks (MachineTapes T) (prime+K))
    (borrowed : List (Fin (prime+K+4)))
    (input : SetupInput T (prime+K) D (Sizes.p n₀) u
      (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
      B W Fs.length radius (amortizedCoreWidth ct (Sizes.p n₀)) Vg Vr base)
    (hgeometry : amortizedCoreWidth ct (Sizes.p n₀)+2*radius < 2^D)
    (hfit : ∀ j, globalValues (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i))
      target (Sizes.s n₀ i) (Sizes.t n₀ i) B W Fs.length radius (amortizedCoreWidth ct (Sizes.p n₀)) j < 2^D)
    (hbits : ∀ f, formatWidths B Vg Vr f ≤ D)
    (clipped : Bool) (hLength : L = haloRows clipped (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius)
    (movement : GatherBounds Q Vg Vr (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L W replicaExp Fs)
    (hwords : ∀ f j, base.R (fullHeader T (.geometry f j)) =
      binSyms (formatWidths B Vg Vr f) (![Sizes.s n₀ i,amortizedCoreWidth ct (Sizes.p n₀),radius] j))
    (retained : GatherRetainedInput T K (Sizes.s n₀ i) W bank Fs borrowed base),
    let setup := makeSetup input clipped movement.widthPositive hgeometry hfit hbits
    let src := geometrySources T
    let masters := masterSources T
    ∀ (_caller : setup.NumericalInput (fullExposedClassBank physicalBank) rg src masters),
    let widthMaster := setup.widthMaster
    let zeroMaster := setup.zero
    let seed := makeGatherSeed input hwords bank retained movement
      (le_of_eq_of_le hLength (Nat.add_le_add_right
        (coreRows_le clipped (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) movement.widthPositive) (2*radius))) hA
    ∀ (gatherInput : setup.GatherInput seed rg masters (src 3)),
    let g := gatherInput.ready
    ∀ (_hExposeWidth : Vg ≤ cV*Sizes.p n₀) (_hRouteWidth : g.D ≤ cD*Sizes.p n₀)
    (_hMetadataFit : g.D ≤ 2^g.a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n₀ i)
      (amortizedCoreWidth ct (Sizes.p n₀)) radius L).length*(L*W))
    (_hReplicaVolume : Fs.length ≤ Sizes.T n₀)
    (hp : 4 ≤ Sizes.p n₀) (hprecision : Sizes.p n₀+2 ≤ target)
    (J : (ZMod (Sizes.s n₀ i) → ℂ) →L[ℂ] (ZMod (Sizes.s n₀ i) → ℂ))
    (hJ : J ∘L PhaseCellOperator.exact (Sizes.s n₀ i) (Sizes.t n₀ i) α = 1),
    let batch := (PackedExactBatch.ofCommonCoreClass (A := prime+K)
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target
      (amortizedCoreWidth ct (Sizes.p n₀)) L α gap C V bounds Fs.reverse
      (by intro F hmem j; exact hF F (List.mem_reverse.mp hmem) j) hp hprecision J hJ).withReplicaCount
        (2^g.a) (by simpa only [List.length_reverse] using g.hpower)
    let pubClass := gatherPublicationClass (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    let keys := PackedExactBatch.ofCommonCoreClass_keys (A := prime+K)
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target
      (amortizedCoreWidth ct (Sizes.p n₀)) L α gap C V bounds Fs.reverse
      (by intro F hmem j; exact hF F (List.mem_reverse.mp hmem) j) hp hprecision J hJ
    let runTime := initializedPublishedRunTime F n₀ ct cV cD (Sizes.p n₀) u (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let runStock := initializedPublishedRunStock Cstock Cprog n₀ ct cV cD (Sizes.p n₀) (Sizes.s n₀ i) (Sizes.t n₀ i) D B W Fs.length
    let runProg : Pr P (MachineTapes T) Q (prime+K) U := (inputTableClassProgram rg masters widthMaster zeroMaster (initializedClassProgram (fullExposedClassBank physicalBank) src
          (.seq g.program (inputClassProgram (fullExposedClassBank physicalBank) (fullExposedClassBank_injective physicalBank physicalInj) b rg))))
    let origins := (coreSubsetPublicationWindows (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      pubClass.length g.hwidth pubClass.indices pubClass.sublist).origins
    let replica := fun j : Fin (2^g.a) => Fs.reverse[j.val]'(by
      simpa only [List.length_reverse,g.hpower] using j.isLt)
    let a := Nat.clog 2 indices.length
    let Vpub := g.D
    let output := header T .output
    let pubSrc := publication T
    ∀ (ambient : Fin (2^g.a) → List (Fin (prime+K+4)))
    (_hambient : ∀ j, (ambient j).length = Sizes.s n₀ i*W)
    (outputTail : List (Fin (prime+K+4)))
    (_pubInput : PublicationCallerReady (classCallerRegister ∘ pubSrc) (selectedPublicationPlacement physicalBank output) base)
    (_hdstBase : base.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail)
    (_hPublicationVolume : Sizes.s n₀ i*W < 2^Vpub),
    let geometryCost := PublicationGeometryControls.timeCost Vpub (Sizes.s n₀ i) L radius
    let retireGeometryCost := 2*((L-2*radius)+Sizes.s n₀ i)+5
    let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
    let retireDimensionCost := 2*(g.a+a+2^a)+7
    let metadata := PackedTranspose.publicationHeaderVolume a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    ∃ v' : HS (MachineTapes T) Q (prime+K) U, ∃ n : ℕ, ∃ outputs : List (List (Fin (prime+K+4))), ∃ rows : batch.Rows, v'.user = v.user ∧
      (n : ℝ) ≤ initializedPublishedTime setup.timeCost runTime (geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ) setup.retireCost ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      publishedCoreRowsAccurate (prime+K) (Sizes.p n₀) W pubClass (rows.classRows pubClass keys)
        (publishedInverseTarget (Sizes.p n₀) J replica) (publishedInverseError (Sizes.p n₀)) ∧
      mnSize (Host.mk v' {base with R := (Function.update base.R (classCallerRegister output)
        ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) =
        mnSize (Host.mk v base) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v base)+depth+
        (setup.stock+(runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass))))))) depth
        (.seq setup.program (.seq (publishedClassProgram runProg g.routeSrc pubSrc (physicalBank (.recovery (.control .result))) output hstates) setup.retire))
        (Host.mk v base) n (Host.mk v' {base with R := (Function.update base.R (classCallerRegister output)
          ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) := by
  intro physicalBank physicalInj
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedTablePublishedComputedCoreClassRun_exec
    (body := body) physicalBank physicalInj b hstates ct cV cD
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ _ u target L hu htarget α gap C V bounds Fs hFs
  intro B W radius indices jobs D Cprog depth Vg Vr replicaExp rg hpush hbody hwide hA
    v base borrowed input hgeometry hfit hbits clipped hLength movement hwords retained setup src masters caller
    widthMaster zeroMaster seed gatherInput g hExposeWidth hRouteWidth
    hMetadataFit hReplicaVolume hp hprecision J hJ batch pubClass keys runTime runStock runProg
    origins replica a Vpub output pubSrc ambient hambient outputTail pubInput
    hdstBase hPublicationVolume geometryCost retireGeometryCost dimensionCost retireDimensionCost metadata originCost
  have hrg : Function.Injective rg := numericTable_injective T
  have hoff (r k) : rg r ≠ fullExposedClassBank physicalBank k := fullHeader_ne_numerical bank (tableRole r) k
  have hsrc (j k) : src j ≠ fullExposedClassBank physicalBank k := fullHeader_ne_numerical bank (geometryRole 0 j) k
  have hwidthMaster (r) : rg r ≠ widthMaster := (fullHeader_injective T).ne (tableRole_ne r (.scalar 0) rfl)
  have hzeroMaster (r) : rg r ≠ zeroMaster := (fullHeader_injective T).ne (tableRole_ne r .zero rfl)
  have hmasterOff (j r) : rg r ≠ masters j := (fullHeader_injective T).ne (tableRole_ne r (masterRole j) (masterRole_not_table j))
  have hgeometryOff (j r) : rg r ≠ src j := (fullHeader_injective T).ne (tableRole_ne r (geometryRole 0 j) (geometryRole_not_table 0 j))
  have hout : physicalBank (.recovery (.control .result)) ≠ output := (header_ne_bank bank .output _).symm
  have hpubOff (j) : pubSrc j ≠ physicalBank (.recovery (.control .result)) := publication_off_result bank j
  have hpubInj : Function.Injective pubSrc := publication_injective T
  have houtPub (j) : output ≠ pubSrc j := output_ne_publication T j
  have houtPacket := houtPub 9
  have houtCount := houtPub 6
  have houtMasters (j) (_ : j ∈ [(0 : Fin 10),1,2]) := houtPub j
  have houtGeometry (j) (_ : j ∈ [(4 : Fin 10),8]) := houtPub j
  have hRoute : g.routeSrc = routing T := rfl
  let originSources := publicationRetainedOriginSources g.routeSrc pubSrc
  have hOriginInj : Function.Injective originSources := by
    change Function.Injective (publicationRetainedOriginSources g.routeSrc (publication T))
    rw [hRoute,origins_eq]
    exact origins_injective T
  have hPubWidth : pubSrc 7 = originSources 4 := by
    change publication T 7 = publicationRetainedOriginSources g.routeSrc (publication T) 4
    rw [hRoute,origins_eq]
    exact publicationWidth T
  have hPubReplica : pubSrc 3 = g.routeSrc 6 := by rw [hRoute]; exact publicationReplicas T
  have hPubWord : pubSrc 5 = g.routeSrc 5 := by rw [hRoute]; exact publicationWord T
  have hpubOwnedOff (j) (hj : j ∈ [(0 : Fin 10),1,2,4,6,8,9]) :
      classInputPortOff masters setup.formats (classCallerRegister (pubSrc j)) := publicationOwned_off_class T j hj
  have houtCore : classCallerRegister output ≠ setup.core := (retained_off_class T .output rfl).1
  have houtHalo : classCallerRegister output ≠ setup.halo := (retained_off_class T .output rfl).2.1
  have houtFormats (r) (hr : r ∈ setup.formats) : r.2 ≠ classCallerRegister output :=
    (retained_off_class T .output rfl).2.2 r hr
  let S := setup.loaded
  let value := setup.classValues
  have layout : setup.ConsumerLayout masters (src 3) (classCallerRegister (g.exposeSrc 3))
      (classCallerRegister (g.routeSrc 3)) Vg g.D L := gatherInput.consumers
  have hLengthGroup : L ∈ coreGatherLengths (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius := by
    rw [layout.classLength]
    exact CommonClassGeometry.haloRows_mem setup.clipped _ _ _
  have hcore := CommonClassGeometry.coreRows_le setup.clipped (Sizes.s n₀ i)
    (amortizedCoreWidth ct (Sizes.p n₀)) setup.widthPositive
  have hHfit : L < 2^B := by
    rw [layout.classLength]
    dsimp only [CommonClassGeometry.haloRows]
    omega
  have hB : 0 < B := by
    by_contra hn
    have hB0 : B = 0 := by omega
    have hw := setup.widthPositive
    have hwide0 := hwide
    rw [hB0,pow_zero] at hwide0
    omega
  have hRouteTableOff := gatherInput.routeTableOff
  let st : TblSt 12 (prime+K) := ⟨commonInputValues (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i) B W Fs.length radius L,[]⟩
  have hdst : S.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail :=
    (setup.loaded_off (classCallerRegister output) houtCore houtHalo houtFormats).trans hdstBase
  have pubReady := setup.publicationReady layout (classCallerRegister ∘ pubSrc)
    (selectedPublicationPlacement physicalBank output) pubInput hpubOwnedOff
  have inputReady := caller.ready layout hB
  have hvalues (j) : value (masters j) = st.val j := by
    simpa only [st] using setup.classValues_masters layout caller.mastersInjective j
  have hfitValues (j) : st.val j < 2^D := by
    rw [←hvalues j]
    exact setup.classValues_fit layout caller.mastersInjective j
  let result (r : List (List (Fin (prime+K+4))) × batch.Rows) :=
    (List.ofFn fun j => pubClass.output W g.hwidth (r.2.classRows pubClass keys j) (ambient j)).flatten++outputTail
  let Cert (r : List (List (Fin (prime+K+4))) × batch.Rows) : Prop :=
    List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) r.1 ∧
    publishedCoreRowsAccurate (prime+K) (Sizes.p n₀) W pubClass (r.2.classRows pubClass keys)
      (publishedInverseTarget (Sizes.p n₀) J replica) (publishedInverseError (Sizes.p n₀))
  let cost : ℝ := runTime+(geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ)
  let stock : ℕ := (runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass)))))
  obtain ⟨v',n,⟨outputs,rows⟩,hu,ht,hcert,hsize,hx⟩ := setup.wrap_exec_within body
    (classCallerRegister output) houtCore houtHalo houtFormats
    (publishedClassProgram runProg g.routeSrc pubSrc (physicalBank (.recovery (.control .result))) output hstates)
    cost stock depth result Cert (fun v₁ => by
      obtain ⟨v₂,n₂,outputs,rows,hu₂,hn₂,hgood,hrows,hsize,he₂⟩ :=
        hn h i u target L hu htarget hLengthGroup α gap C V bounds Fs hFs
          D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB v₁ S src hsrc masters widthMaster
          zeroMaster value hwidthMaster hzeroMaster hmasterOff hgeometryOff hvalues inputReady Vg borrowed g
          hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hp hprecision J hJ output hout pubSrc hpubOff
          ambient hambient outputTail hpubInj houtPacket houtCount houtMasters hOriginInj hPubWidth hPubReplica
          hPubWord hRouteTableOff houtGeometry pubReady hdst hPublicationVolume
      exact ⟨v₂,n₂,(outputs,rows),hu₂,hn₂,⟨hgood,hrows⟩,hsize,he₂⟩) v
  exact ⟨v',n,outputs,rows,hu,ht,hcert.1,hcert.2,hsize,hx⟩

end IntegerMultBounds.MathlibTM2.Cost
