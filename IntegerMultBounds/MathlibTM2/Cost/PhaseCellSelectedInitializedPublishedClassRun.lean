module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPublishedClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellFormattedClassExecution
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupNumericalReadiness
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSetupGatherReadiness

/-! Execute ordinary-input setup, the selected numerical/publication run and
owned-word cleanup. Every stage receives the preceding actual host state; the
final state restores the original baseline except for the ambient destination. -/
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
open ComputedClassBanks

open IntegerMultBounds.Networks.Shared50ModularControl (prime)

theorem selectedInitializedPublishedClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] [NeZero (Sizes.t n₀ i)] (u target L : ℕ)
    (hu : u ≤ Sizes.p n₀) (htarget : target ≤ ct*Sizes.p n₀)
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
    ∀ (D Cprog depth : ℕ)
    (rg : TblR 12 → Fin ((T+175)+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (fullExposedClassBank bank) k)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).clock (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).work (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).count (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).spare (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hwide : (Sizes.s n₀ i)+(amortizedCoreWidth ct (Sizes.p n₀))+2*radius < 2^B)
    (hA : 4 ≤ (prime+K))
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (base : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K))
    (setup : FormattedClassSetup D (Sizes.p n₀) u
      (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
      B W Fs.length radius (amortizedCoreWidth ct (Sizes.p n₀)) base),
    ∀ (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (hsrc : ∀ i k, src i ≠ fullExposedClassBank bank k)
    (masters : Fin 12 → Fin ((T+175)+PackedTranspose.tapeCount))
    (caller : setup.NumericalInput (fullExposedClassBank bank) rg src masters),
    let widthMaster := setup.widthMaster
    let zeroMaster := setup.zero
    ∀ (hwidthMaster : ∀ r, rg r ≠ widthMaster) (hzeroMaster : ∀ r, rg r ≠ zeroMaster)
    (hmasterOff : ∀ j r, rg r ≠ masters j) (hgeometryOff : ∀ j r, rg r ≠ src j)
    (Vg : ℕ) (borrowed : List (Fin (prime+K+4)))
    (seed : RestoringGatherSeed (Q := Q) bank Vg (Sizes.s n₀ i)
      (amortizedCoreWidth ct (Sizes.p n₀)) radius L W Fs borrowed base)
    (gatherInput : setup.GatherInput seed rg masters (src 3)),
    let g := gatherInput.ready
    ∀ (hExposeWidth : Vg ≤ cV*Sizes.p n₀) (hRouteWidth : g.D ≤ cD*Sizes.p n₀)
    (hMetadataFit : g.D ≤ 2^g.a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n₀ i)
      (amortizedCoreWidth ct (Sizes.p n₀)) radius L).length*(L*W))
    (hReplicaVolume : Fs.length ≤ Sizes.T n₀)
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
    let runTime : ℝ := (((126*D+132 : ℕ) : ℝ)+((Sizes.T n₀+(coreExposureTrafficFactor cV (1032+8*ct)+40*cV+48*cD+6185 : ℕ)*
        (Fs.length*Sizes.s n₀ i*W : ℕ)+432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*Sizes.s n₀ i*W : ℕ)*Sizes.d n₀*((Sizes.ℓ n₀ : ℝ)^Parameters.tau+1))+
        8*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*Fs.length+32*(B : ℝ)+35))
    let runStock : ℕ := (3*(100*D+105)+
        (2*(24*B+25)+((Sizes.T n₀+(3*coreExposureTrafficFactor cV (1032+8*ct)+60*cV+72*cD+268+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*Sizes.s n₀ i*W))+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀+
          495*D+24*Fs.length)))
    let runProg : Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U := (inputTableClassProgram rg masters widthMaster zeroMaster (initializedClassProgram (fullExposedClassBank bank) src
          (.seq g.program (inputClassProgram (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj) b rg))))
    let origins := (coreSubsetPublicationWindows (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      pubClass.length g.hwidth pubClass.indices pubClass.sublist).origins
    let replica := fun j : Fin (2^g.a) => Fs.reverse[j.val]'(by
      simpa only [List.length_reverse,g.hpower] using j.isLt)
    let a := Nat.clog 2 indices.length
    let Vpub := g.D
    ∀ (output : Fin T) (hout : bank (.recovery (.control .result)) ≠ output)
    (pubSrc : Fin 10 → Fin T) (hpubOff : ∀ j, pubSrc j ≠ bank (.recovery (.control .result))),
    let originSources := publicationRetainedOriginSources g.routeSrc pubSrc
    ∀ (ambient : Fin (2^g.a) → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = Sizes.s n₀ i*W)
    (outputTail : List (Fin (prime+K+4)))
    (hpubInj : Function.Injective pubSrc)
    (houtPacket : output ≠ pubSrc 9) (houtCount : output ≠ pubSrc 6)
    (houtMasters : ∀ j ∈ [(0 : Fin 10),1,2], output ≠ pubSrc j)
    (hOriginInj : Function.Injective originSources)
    (hPubWidth : pubSrc 7 = originSources 4)
    (hPubReplica : pubSrc 3 = g.routeSrc 6) (hPubWord : pubSrc 5 = g.routeSrc 5)
    (houtGeometry : ∀ j ∈ [(4 : Fin 10),8], output ≠ pubSrc j)
    (pubInput : PublicationCallerReady (classCallerRegister ∘ pubSrc) (selectedPublicationPlacement bank output) base)
    (hpubOwnedOff : ∀ j ∈ [(0 : Fin 10),1,2,4,6,8,9],
      classInputPortOff masters setup.formats (classCallerRegister (pubSrc j)))
    (hdstBase : base.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail)
    (hPublicationVolume : Sizes.s n₀ i*W < 2^Vpub)
    (houtCore : classCallerRegister output ≠ setup.core)
    (houtHalo : classCallerRegister output ≠ setup.halo)
    (houtFormats : ∀ r ∈ setup.formats, r.2 ≠ classCallerRegister output),
    let geometryCost := PublicationGeometryControls.timeCost Vpub (Sizes.s n₀ i) L radius
    let retireGeometryCost := 2*((L-2*radius)+Sizes.s n₀ i)+5
    let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
    let retireDimensionCost := 2*(g.a+a+2^a)+7
    let metadata := PackedTranspose.publicationHeaderVolume a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    ∃ v', ∃ n : ℕ, ∃ outputs, ∃ rows : batch.Rows, v'.user = v.user ∧
      (n : ℝ) ≤ (setup.timeCost : ℝ)+(runTime+(geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ))+(setup.retireCost : ℝ) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      (∀ j k, k ∈ pubClass.indices →
        let out := packedIntervalRead (Sizes.p n₀) W (coreStart (amortizedCoreWidth ct (Sizes.p n₀)) k)
          (Fast.cstream (prime+K) W (rows.classRows pubClass keys j k))
        (∀ z ∈ ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k, ‖out z‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k) out
          ((((2 : ℂ)^inverseNormalizationShift (Sizes.p n₀))⁻¹ • J)
            ((1/2 : ℂ) • fun z => ShortConv.value (Sizes.p n₀) (replica j z))) (3/(2 : ℝ)^(Sizes.p n₀))) ∧
      mnSize (Host.mk v' {base with R := (Function.update base.R (classCallerRegister output)
        ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) =
        mnSize (Host.mk v base) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v base)+depth+
        (setup.stock+(runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass))))))) depth
        (.seq setup.program (.seq (publishedClassProgram runProg g.routeSrc pubSrc (bank (.recovery (.control .result))) output hstates) setup.retire))
        (Host.mk v base) n (Host.mk v' {base with R := (Function.update base.R (classCallerRegister output)
          ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) := by
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedTablePublishedComputedCoreClassRun_exec
    (body := body) bank hinj b hstates ct cV cD
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ _ u target L hu htarget α gap C V bounds Fs hFs
  intro B W radius indices jobs D Cprog depth rg hrg hoff hpush hbody hwide hA
    v base setup src hsrc masters caller widthMaster zeroMaster hwidthMaster hzeroMaster hmasterOff
    hgeometryOff Vg borrowed seed gatherInput g hExposeWidth hRouteWidth
    hMetadataFit hReplicaVolume hp hprecision J hJ batch pubClass keys runTime runStock runProg
    origins replica a Vpub output hout pubSrc hpubOff originSources ambient hambient outputTail hpubInj
    houtPacket houtCount houtMasters hOriginInj hPubWidth hPubReplica hPubWord houtGeometry pubInput hpubOwnedOff
    hdstBase hPublicationVolume houtCore houtHalo houtFormats geometryCost
    retireGeometryCost dimensionCost retireDimensionCost metadata originCost
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
    (selectedPublicationPlacement bank output) pubInput hpubOwnedOff
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
    (∀ j k, k ∈ pubClass.indices →
        let out := packedIntervalRead (Sizes.p n₀) W (coreStart (amortizedCoreWidth ct (Sizes.p n₀)) k)
          (Fast.cstream (prime+K) W (r.2.classRows pubClass keys j k))
        (∀ z ∈ ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k, ‖out z‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k) out
          ((((2 : ℂ)^inverseNormalizationShift (Sizes.p n₀))⁻¹ • J)
            ((1/2 : ℂ) • fun z => ShortConv.value (Sizes.p n₀) (replica j z))) (3/(2 : ℝ)^(Sizes.p n₀)))
  let cost : ℝ := runTime+(geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ)
  let stock : ℕ := (runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass)))))
  obtain ⟨v',n,⟨outputs,rows⟩,hu,ht,hcert,hsize,hx⟩ := setup.wrap_exec_within body
    (classCallerRegister output) houtCore houtHalo houtFormats
    (publishedClassProgram runProg g.routeSrc pubSrc (bank (.recovery (.control .result))) output hstates)
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
