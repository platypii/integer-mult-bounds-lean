module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedTableRestoringClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonCorePublicationBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchReplicaCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedPublicationPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublicationOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedOriginPacket
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGeneratedPublicationMasterWords
public import IntegerMultBounds.MathlibTM2.Host.RestoringSequence
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellGatherPublicationBounds
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationGeometryControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationOrigins

/-! Selected numerical execution feeds its actual result directly to restoring
publication. The final state updates only the ambient caller destination. -/
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

theorem selectedTablePublishedComputedCoreClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] [NeZero (Sizes.t n₀ i)] (u target L : ℕ)
    (hu : u ≤ Sizes.p n₀) (htarget : target ≤ ct*Sizes.p n₀)
    (hLengthGroup : L ∈ coreGatherLengths (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
      (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u))
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
    let st : TblSt 12 (prime+K) := ⟨commonInputValues (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i) B W Fs.length radius L,[]⟩
    ∀ (D Cprog depth : ℕ)
    (rg : TblR 12 → Fin ((T+175)+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (fullExposedClassBank bank) k)
     (hfitValues : ∀ i, st.val i < 2^D)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).clock (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).work (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).count (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).spare (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hwide : (Sizes.s n₀ i)+(amortizedCoreWidth ct (Sizes.p n₀))+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ (prime+K)) (hV : 0 < B)
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K)) 
    (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount))
    (hsrc : ∀ i k, src i ≠ fullExposedClassBank bank k)
    (hs : S.R (src 0) = binSyms B (Sizes.s n₀ i)) (hw' : S.R (src 1) = binSyms B (amortizedCoreWidth ct (Sizes.p n₀)))
    (hr : S.R (src 2) = binSyms B radius) (hL' : S.R (src 3) = binSyms B L)
    (masters : Fin 12 → Fin ((T+175)+PackedTranspose.tapeCount))
    (widthMaster zeroMaster : Fin ((T+175)+PackedTranspose.tapeCount))
    (value : Fin ((T+175)+PackedTranspose.tapeCount) → ℕ)
    (hwidthMaster : ∀ r, rg r ≠ widthMaster) (hzeroMaster : ∀ r, rg r ≠ zeroMaster)
    (hmasterOff : ∀ j r, rg r ≠ masters j) (hgeometryOff : ∀ j r, rg r ≠ src j)
    (hvalues : ∀ j, value (masters j) = st.val j)
    (hwidthWord : (S.R widthMaster).length = D) (hzeroWord : S.R zeroMaster = [])
    (hmasterWords : ∀ j, S.R (masters j) = binSyms D (value (masters j)))
    (htableBlank : ∀ r, S.R (rg r) = [])
    (Vg : ℕ) (borrowed : List (Fin (prime+K+4)))
    (g : RestoringGatherData (Q := Q) bank Vg (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L W Fs borrowed (loadedInputTable rg masters D value S))
    (hExposeWidth : Vg ≤ cV*Sizes.p n₀) (hRouteWidth : g.D ≤ cD*Sizes.p n₀)
    (hMetadataFit : g.D ≤ 2^g.a*2^Nat.clog 2 (coreGatherIndices (Sizes.s n₀ i)
      (amortizedCoreWidth ct (Sizes.p n₀)) radius L).length*(L*W))
    (hReplicaVolume : Fs.length ≤ Sizes.T n₀)
    (hblank : ∀ j, j ≠ .control .source → S.R (fullExposedClassBank bank j) = [])
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank bank) (.work j)) = [])
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
    (hpacketBlank : S.R (classCallerRegister (pubSrc 9)) = [])
    (hcountBlank : S.R (classCallerRegister (pubSrc 6)) = [])
    (houtPacket : output ≠ pubSrc 9) (houtCount : output ≠ pubSrc 6)
    (hmastersBlank : ∀ j ∈ [(0 : Fin 10),1,2], S.R (classCallerRegister (pubSrc j)) = [])
    (houtMasters : ∀ j ∈ [(0 : Fin 10),1,2], output ≠ pubSrc j)
    (hOriginInj : Function.Injective originSources)
    (hPubWidth : pubSrc 7 = originSources 4)
    (hPubReplica : pubSrc 3 = g.routeSrc 6) (hPubWord : pubSrc 5 = g.routeSrc 5)
    (hRouteTableOff : ∀ j r, rg r ≠ classCallerRegister (g.routeSrc j))
    (hgeometryBlank : ∀ j ∈ [(4 : Fin 10),8], S.R (classCallerRegister (pubSrc j)) = [])
    (houtGeometry : ∀ j ∈ [(4 : Fin 10),8], output ≠ pubSrc j)
    (hpubLeft : ∀ j, (embStk (selectedPublicationPlacement bank output) S).L j = [])
    (hdst : S.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail)
    (hPublicationVolume : Sizes.s n₀ i*W < 2^Vpub),
    let e := publicationOriginPlacement (Fin.castAdd 175 ∘ originSources)
    let pubSources := Fin.castAdd 175 ∘ pubSrc
    let geometrySources := PackedTranspose.publicationGeometrySources (Fin.castAdd 175 ∘ originSources) pubSources
    let geometryPlacement := PackedTranspose.publicationGeometryPlacement geometrySources
    let geometryBaseline := PublicationGeometryControls.loaded geometryPlacement (Sizes.s n₀ i) (L-2*radius) S
    let geometryCost := PublicationGeometryControls.timeCost Vpub (Sizes.s n₀ i) L radius
    let retireGeometryCost := 2*((L-2*radius)+Sizes.s n₀ i)+5
    let originBaseline := originPacketState (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) Vpub origins geometryBaseline
    let dimensionSources := PackedTranspose.publicationDimensionSources pubSources
    let pubBaseline := PackedTranspose.publicationDimensionsLoaded dimensionSources g.a indices.length originBaseline
    let dimensionCost := PackedTranspose.publicationDimensionsTimeCost g.a indices.length
    let retireDimensionCost := 2*(g.a+a+2^a)+7
    let metadata := publicationMetadataVolume pubSources pubBaseline
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    ∃ v', ∃ n : ℕ, ∃ outputs, ∃ rows : batch.Rows, v'.user = v.user ∧
      (n : ℝ) ≤ runTime+(geometryCost+(originCost+(dimensionCost+((6*metadata+61)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+21))+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost))))) : ℕ) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      (∀ j k, k ∈ pubClass.indices →
        let out := packedIntervalRead (Sizes.p n₀) W (coreStart (amortizedCoreWidth ct (Sizes.p n₀)) k)
          (Fast.cstream (prime+K) W (rows.classRows pubClass keys j k))
        (∀ z ∈ ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k, ‖out z‖ ≤ 1) ∧
        PhaseCellInterface.ErrorOn (ownedCore (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) k) out
          ((((2 : ℂ)^inverseNormalizationShift (Sizes.p n₀))⁻¹ • J)
            ((1/2 : ℂ) • fun z => ShortConv.value (Sizes.p n₀) (replica j z))) (3/(2 : ℝ)^(Sizes.p n₀))) ∧
      mnSize (Host.mk v' {S with R := (Function.update S.R (classCallerRegister output)
        ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) =
        mnSize (Host.mk v S) ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (runStock+(3*geometryCost+(3*originCost+(2*dimensionCost+(2*(6*metadata+61)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass)))))) depth
        (.seq runProg (.seq (PublicationGeometryControls.program geometryPlacement) (.seq (placedPublicationOrigins e) (.seq (PackedTranspose.publicationDimensionsProgram dimensionSources) (.seq (PackedTranspose.callerPublicationProgram pubSources
          (Fin.castAdd 175 (bank (.recovery (.control .result)))) (Fin.castAdd 175 output) hstates)
          (.seq (clearWords [Fin.castAdd PackedTranspose.tapeCount (dimensionSources 2),
            Fin.castAdd PackedTranspose.tapeCount (dimensionSources 3),Fin.castAdd PackedTranspose.tapeCount (dimensionSources 4)])
            (.seq (clearWords [classCallerRegister (pubSrc 9),classCallerRegister (pubSrc 6)])
              (clearWords [geometryPlacement 3,geometryPlacement 4]))))))))
        (Host.mk v S) n (Host.mk v' {S with R := (Function.update S.R (classCallerRegister output)
          ((List.ofFn fun j => pubClass.output W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail))}) := by
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedTableRestoringComputedCoreClassRun_exec (body := body) bank hinj b hstates ct cV cD
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ _ u target L hu htarget hLengthGroup α gap C V bounds Fs hFs
  intro B W radius indices jobs st D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB
    v S src hsrc hs hw' hr hL' masters widthMaster zeroMaster value hwidthMaster hzeroMaster hmasterOff
    hgeometryOff hvalues hwidthWord hzeroWord hmasterWords htableBlank Vg borrowed g hExposeWidth hRouteWidth
    hMetadataFit hReplicaVolume hblank hleft hp hprecision J hJ batch pubClass keys runTime runStock runProg
    origins replica a Vpub output hout pubSrc hpubOff originSources ambient hambient outputTail hpubInj hpacketBlank hcountBlank
    houtPacket houtCount hmastersBlank houtMasters hOriginInj hPubWidth hPubReplica hPubWord hRouteTableOff hgeometryBlank houtGeometry hpubLeft
    hdst hPublicationVolume e pubSources geometrySources geometryPlacement geometryBaseline geometryCost retireGeometryCost originBaseline dimensionSources pubBaseline dimensionCost retireDimensionCost metadata originCost
  obtain ⟨v₁,n₁,outputs,hu₁,hn₁,hgood,he₁⟩ := hn h i u target L hu htarget hLengthGroup α gap C V bounds Fs hFs
    D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB v S src hsrc hs hw' hr hL'
    masters widthMaster zeroMaster value hwidthMaster hzeroMaster hmasterOff hgeometryOff hvalues
    hwidthWord hzeroWord hmasterWords htableBlank Vg borrowed g hExposeWidth hRouteWidth hMetadataFit hReplicaVolume hblank hleft
  have hprefix (k : Fin T) : Fin.castAdd PackedTranspose.tapeCount (Fin.castAdd 175 k) = classCallerRegister k := rfl
  have hresult : (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result =
      classCallerRegister (bank (.recovery (.control .result))) := by
    simp only [plan,RecoveryBanks.plan,recovery,fullExposedClassBank_apply]
  have hsource : S.R (classCallerRegister (bank (.recovery (.control .result)))) = [] := by
    simpa only [fullExposedClassBank_apply] using hblank (.recovery (.control .result)) (by decide)
  rw [hresult,hsource,List.append_nil] at he₁
  change (n₁ : ℝ) ≤ runTime at hn₁
  have hformat : batch.W = W := rfl
  have hbatch : batch.records = List.ofFn jobs := rfl
  have hjobCount : batch.records.length = indices.length := by rw [hbatch,List.length_ofFn]
  have hwidth : ∀ r ∈ batch.records, r.coreWidth = amortizedCoreWidth ct (Sizes.p n₀) := by
    rw [hbatch]
    intro r hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    rfl
  have hOriginRoute (j : Fin 5) : originSources (Fin.castAdd 2 j) = g.routeSrc (Fin.castAdd 2 j) :=
    publicationRetainedOriginSources_route _ _ j
  have hOriginPacket : originSources 5 = pubSrc 9 := publicationRetainedOriginSources_packet _ _
  have hOriginCount : originSources 6 = pubSrc 6 := publicationRetainedOriginSources_count _ _
  have pubBounds : PackedTranspose.PublicationShapeBounds a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length :=
    PackedTranspose.gatherPublicationShapeBounds _ _ _ _ _ _ _ g.hwidth g.hgroup g.hpacket
      g.hbits g.hfit hPublicationVolume
  have hOriginWide : Sizes.s n₀ i+amortizedCoreWidth ct (Sizes.p n₀)+2*radius < 2^Vpub := g.hDwide
  have hOriginLength : L < 2^Vpub := g.hDLfit
  have hrouteRead (j) : (loadedInputTable rg masters D value S).R (classCallerRegister (g.routeSrc j)) =
      S.R (classCallerRegister (g.routeSrc j)) :=
    loadedInputTable_off rg masters D value S _ (fun r => (hRouteTableOff j r).symm)
  have hOriginWords : ∀ j : Fin 4, S.R (classCallerRegister (originSources (Fin.castAdd 3 j))) =
      binSyms Vpub (![Sizes.s n₀ i,amortizedCoreWidth ct (Sizes.p n₀),radius,L] j) := by
    intro j
    have hport : originSources (Fin.castAdd 3 j) = g.routeSrc (Fin.castAdd 3 j) :=
      hOriginRoute (Fin.castAdd 1 j)
    rw [hport]
    fin_cases j
    · exact (hrouteRead 0).symm.trans g.hRs
    · exact (hrouteRead 1).symm.trans g.hRw
    · exact (hrouteRead 2).symm.trans g.hRr
    · exact (hrouteRead 3).symm.trans g.hRL
  have hOriginWidth : (S.R (classCallerRegister (originSources 4))).length = Vpub := by
    have hport : originSources 4 = g.routeSrc 4 := hOriginRoute 4
    rw [hport,←hrouteRead 4]
    exact g.hRV
  have hOriginOff (j : Fin 7) : originSources j ≠ bank (.recovery (.control .result)) := by
    by_cases h5 : j = 5
    · subst j; rw [hOriginPacket]; exact hpubOff 9
    by_cases h6 : j = 6
    · subst j; rw [hOriginCount]; exact hpubOff 6
    have hj : j.val < 5 := by omega
    have hport : originSources j = g.routeSrc (Fin.castAdd 2 (⟨j.val,hj⟩ : Fin 5)) := hOriginRoute ⟨j.val,hj⟩
    rw [hport]
    exact g.hRouteOff _ _
  have hpubBlank (j) : S.R (Fin.natAdd (T+175) j) = [] := by
    by_cases hj : ∃ r, rg r = Fin.natAdd (T+175) j
    · obtain ⟨r,hr⟩ := hj
      rw [←hr]
      exact htableBlank r
    · have hh := g.hRblank j
      rw [loadedInputTable_off rg masters D value S _ (by intro r hr; exact hj ⟨r,hr.symm⟩)] at hh
      exact hh
  have hcorePacket := pubBounds.packetPositive
  have hpubBits := pubBounds.stageBits
  have hW : 1 ≤ batch.W := by
    change 1 ≤ W
    by_contra hz
    have hw : W = 0 := by omega
    simp only [hw,Nat.mul_zero,lt_self_iff_false] at hcorePacket
  have hcaller : Function.Injective (classCallerRegister : Fin T → Fin ((T+175)+PackedTranspose.tapeCount)) :=
    (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
  have hsrcSep (j k : Fin 10) (hjk : j ≠ k) :
      classCallerRegister (pubSrc j) ≠ classCallerRegister (pubSrc k) := hcaller.ne (hpubInj.ne hjk)
  let numerical := classCallerRegister (bank (.recovery (.control .result)))
  have he : Function.Injective e := publicationOriginPlacement_injective _ ((Fin.castAdd_injective _ _).comp hOriginInj)
  have he109 : e 109 = classCallerRegister (pubSrc 9) := by
    have hh := publicationOriginPlacement_shared (Fin.castAdd 175 ∘ originSources) 5
    rw [show publicationOriginIndex 5 = (109 : Fin 117) from rfl] at hh
    simpa only [Function.comp_apply,hprefix,hOriginPacket] using hh
  have he116 : e 116 = classCallerRegister (pubSrc 6) := by
    have hh := publicationOriginPlacement_shared (Fin.castAdd 175 ∘ originSources) 6
    rw [show publicationOriginIndex 6 = (116 : Fin 117) from rfl] at hh
    simpa only [Function.comp_apply,hprefix,hOriginCount] using hh
  have heOff (j : Fin 117) : e j ≠ numerical := by
    simpa only [hprefix] using publicationOriginPlacement_off_prefix (Fin.castAdd 175 ∘ originSources)
      (Fin.castAdd 175 (bank (.recovery (.control .result))))
      (fun k => (Fin.castAdd_injective _ _).ne (hOriginOff k)) j
  have hcorePos : 0 < L-2*radius := by
    by_contra hz
    have hh : L-2*radius = 0 := by omega
    simp only [hh,Nat.zero_mul,lt_self_iff_false] at hcorePacket
  have hsplit : L-2*radius+2*radius = L := Nat.sub_add_cancel (by omega)
  have hBinaryOff (j : Fin 4) (k : Fin 10) (hk : k ∈ [(4 : Fin 10),8]) :
      originSources (Fin.castAdd 3 j) ≠ pubSrc k := by
    intro heq
    have hh := congrArg List.length (hOriginWords j)
    rw [heq,hgeometryBlank k hk,List.length_nil,length_binSyms] at hh
    omega
  have hOriginGeometryOff (j : Fin 7) (k : Fin 10) (hk : k ∈ [(4 : Fin 10),8]) : originSources j ≠ pubSrc k := by
    by_cases h4 : j = 4
    · subst j; rw [←hPubWidth]; exact hpubInj.ne (by intro heq; rw [←heq] at hk; simp at hk)
    by_cases h5 : j = 5
    · subst j; rw [hOriginPacket]; exact hpubInj.ne (by intro heq; rw [←heq] at hk; simp at hk)
    by_cases h6 : j = 6
    · subst j; rw [hOriginCount]; exact hpubInj.ne (by intro heq; rw [←heq] at hk; simp at hk)
    have hj : j.val < 4 := by omega
    exact hBinaryOff ⟨j.val,hj⟩ k hk
  have hgeometrySrcInj : Function.Injective geometrySources :=
    PackedTranspose.publicationGeometrySources_injective _ _ ((Fin.castAdd_injective _ _).comp hOriginInj)
      ((Fin.castAdd_injective _ _).comp hpubInj)
      (by intro j _ k hk; exact (Fin.castAdd_injective _ _).ne (hOriginGeometryOff j k hk))
  have hgeometryInj : Function.Injective geometryPlacement :=
    PackedTranspose.publicationGeometryPlacement_injective _ hgeometrySrcInj
  have hgeoPort (j : Fin 5) : geometryPlacement (Fin.castAdd 4 j) = Fin.castAdd PackedTranspose.tapeCount (geometrySources j) :=
    PackedTranspose.publicationGeometryPlacement_shared _ j
  have hgeo0 : geometryPlacement 0 = classCallerRegister (originSources 0) := hgeoPort 0
  have hgeo1 : geometryPlacement 1 = classCallerRegister (originSources 2) := hgeoPort 1
  have hgeo2 : geometryPlacement 2 = classCallerRegister (originSources 3) := hgeoPort 2
  have hgeo3 : geometryPlacement 3 = classCallerRegister (pubSrc 4) := hgeoPort 3
  have hgeo4 : geometryPlacement 4 = classCallerRegister (pubSrc 8) := hgeoPort 4
  have hgeometryOff (j : Fin 9) : geometryPlacement j ≠ numerical := by
    apply PackedTranspose.publicationGeometryPlacement_off_prefix geometrySources
      (Fin.castAdd 175 (bank (.recovery (.control .result)))) ?_ j
    intro k
    fin_cases k <;> simp only [geometrySources,PackedTranspose.publicationGeometrySources,
      pubSources,Function.comp_apply] <;>
      exact (Fin.castAdd_injective _ _).ne (by first | exact hOriginOff _ | exact hpubOff _)
  obtain ⟨vG,nG,huG,hnG,heG⟩ := PublicationGeometryControls.after_update_exec_within body
    geometryPlacement hgeometryInj Vpub (Sizes.s n₀ i) (L-2*radius) radius
    (by omega) (by omega) (by simpa only [hsplit] using hOriginLength)
    numerical outputs.reverse.flatten hgeometryOff v₁ S
    (by rw [hgeo0]; exact hOriginWords 0)
    (by rw [hgeo1]; exact hOriginWords 2)
    (by rw [hgeo2,hsplit]; exact hOriginWords 3)
    (by
      intro j hj
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl | rfl | rfl | rfl
      · rw [hgeo3]; exact hgeometryBlank 4 (by simp)
      · rw [hgeo4]; exact hgeometryBlank 8 (by simp)
      all_goals
        change S.R (PackedTranspose.publicationGeometryPlacement geometrySources _) = []
        rw [PackedTranspose.publicationGeometryPlacement_private geometrySources _ (by decide)]
        exact hpubBlank _) depth
  simp only [hsplit] at hnG heG
  have hGoff (k) (h4 : k ≠ classCallerRegister (pubSrc 4)) (h8 : k ≠ classCallerRegister (pubSrc 8)) :
      geometryBaseline.R k = S.R k := PublicationGeometryControls.loaded_off _ _ _ S k
        (by simpa only [hgeo3] using h4) (by simpa only [hgeo4] using h8)
  have hGpub (j : Fin 10) (h4 : j ≠ 4) (h8 : j ≠ 8) :
      geometryBaseline.R (classCallerRegister (pubSrc j)) = S.R (classCallerRegister (pubSrc j)) :=
    hGoff _ (hsrcSep _ _ h4) (hsrcSep _ _ h8)
  have hGorigin (j : Fin 7) : geometryBaseline.R (classCallerRegister (originSources j)) =
      S.R (classCallerRegister (originSources j)) :=
    hGoff _ (hcaller.ne (hOriginGeometryOff j 4 (by simp))) (hcaller.ne (hOriginGeometryOff j 8 (by simp)))
  have hGblank (j) : geometryBaseline.R (Fin.natAdd (T+175) j) = [] := by
    apply (hGoff _ ?_ ?_).trans (hpubBlank j)
    all_goals simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc _)) j).symm
  have hGsource : geometryBaseline.R numerical = [] :=
    (hGoff _ (hcaller.ne (hpubOff 4)).symm (hcaller.ne (hpubOff 8)).symm).trans hsource
  have hGdst : geometryBaseline.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail :=
    (hGoff _ (hcaller.ne (houtGeometry 4 (by simp))) (hcaller.ne (houtGeometry 8 (by simp)))).trans hdst
  have originInput : PublicationOriginInput e Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L geometryBaseline :=
    publicationOriginPlacement_input _ geometryBaseline Vpub _ _ _ _ hOriginWide hOriginLength
      (by intro j; simpa only [Function.comp_apply,hprefix,hGorigin] using hOriginWords j)
      (by simpa only [Function.comp_apply,hprefix,hGorigin] using hOriginWidth) hGblank
  obtain ⟨vO,nO,huO,hnO,heO⟩ := placedOwnedPublicationOrigins_after_update_exec_within (body := body) e he
    (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) he109 he116 numerical outputs.reverse.flatten heOff
    g.hwidth originInput.geometryFit originInput.lengthFit hA (by omega) vG geometryBaseline
    originInput.widthLength originInput.ambientWord originInput.coreWidthWord originInput.radiusWord
    originInput.haloLengthWord originInput.zero originInput.tableBlank
    (by rw [he109,hGpub 9 (by decide) (by decide)]; exact hpacketBlank) originInput.savedBlank originInput.tmpBlank
    (by rw [he116,hGpub 6 (by decide) (by decide)]; exact hcountBlank) depth
  have hpOff : classCallerRegister (pubSrc 9) ≠ numerical := hcaller.ne (hpubOff 9)
  have hcOff : classCallerRegister (pubSrc 6) ≠ numerical := hcaller.ne (hpubOff 6)
  have hOoff (k) (hp : k ≠ classCallerRegister (pubSrc 9)) (hc : k ≠ classCallerRegister (pubSrc 6)) :
      originBaseline.R k = geometryBaseline.R k := originPacketState_off _ _ _ _ geometryBaseline k hp hc
  have hN : origins.length = indices.length := by
    simp only [origins,coreSubsetPublicationWindows,PublicationWindows.restrict,List.length_map,
      pubClass,gatherPublicationClass]
    rfl
  have hdimInj : Function.Injective dimensionSources :=
    PackedTranspose.publicationDimensionSources_injective pubSources ((Fin.castAdd_injective _ _).comp hpubInj)
  have hdimPort (j : Fin 5) : Fin.castAdd PackedTranspose.tapeCount (dimensionSources j) =
      classCallerRegister (pubSrc (PackedTranspose.publicationDimensionSourceIndex j)) := rfl
  have hdimOff (j : Fin 5) : dimensionSources j ≠ Fin.castAdd 175 (bank (.recovery (.control .result))) :=
    (Fin.castAdd_injective _ _).ne (hpubOff _)
  have hdimBlank (j : Fin 5) (hj : j ∈ [(2 : Fin 5),3,4]) :
      originBaseline.R (Fin.castAdd PackedTranspose.tapeCount (dimensionSources j)) = [] := by
    rw [hdimPort]
    have hi : PackedTranspose.publicationDimensionSourceIndex j ∈ [(0 : Fin 10),1,2] := by
      simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
      rcases hj with rfl | rfl | rfl <;> decide
    exact (hOoff _ (hsrcSep _ 9 (by intro he; rw [he] at hi; simp at hi))
      (hsrcSep _ 6 (by intro he; rw [he] at hi; simp at hi))).trans ((hGpub _ (by intro heq; rw [heq] at hi; simp at hi)
        (by intro heq; rw [heq] at hi; simp at hi)).trans (hmastersBlank _ hi))
  have hblankO (j) : originBaseline.R (Fin.natAdd (T+175) j) = [] := by
    apply (hOoff _ ?_ ?_).trans (hGblank j)
    · simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc 9)) j).symm
    · simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc 6)) j).symm
  have hreplicaLength : (geometryBaseline.R (classCallerRegister (pubSrc 3))).length = 2^g.a := by
    have hh := g.hRrep
    rw [hrouteRead 6,←hPubReplica] at hh
    exact (congrArg List.length (hGpub 3 (by decide) (by decide))).trans hh
  have hwordLength : (geometryBaseline.R (classCallerRegister (pubSrc 5))).length = W := by
    have hh := g.hRword
    rw [hrouteRead 5,←hPubWord] at hh
    exact (congrArg List.length (hGpub 5 (by decide) (by decide))).trans hh
  have hpubCore : (geometryBaseline.R (classCallerRegister (pubSrc 4))).length = L-2*radius := by
    simp [geometryBaseline,PublicationGeometryControls.loaded,hgeo3,hgeo4,hsrcSep 4 8 (by decide)]
  have hpubAmbient : (geometryBaseline.R (classCallerRegister (pubSrc 8))).length = Sizes.s n₀ i := by
    simp [geometryBaseline,PublicationGeometryControls.loaded,hgeo4]
  obtain ⟨vD,nD,huD,hnD,heD⟩ := PackedTranspose.publicationDimensions_after_update_exec_within body
    dimensionSources hdimInj g.a indices.length depth
    (Fin.castAdd 175 (bank (.recovery (.control .result)))) outputs.reverse.flatten hdimOff vO originBaseline
    (by
      rw [hdimPort]
      change (originBaseline.R (classCallerRegister (pubSrc 3))).length = _
      rw [hOoff _ (hsrcSep 3 9 (by decide)) (hsrcSep 3 6 (by decide))]
      exact hreplicaLength)
    (by
      rw [hdimPort]
      change (originBaseline.R (classCallerRegister (pubSrc 6))).length = _
      simp [originBaseline,originPacketState,hN])
    hdimBlank hblankO
  simp only [hprefix] at heD
  have hinputD : PackedTranspose.PublicationHeaderInput (classCallerRegister ∘ pubSrc)
      a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) origins [] pubBaseline := by
    have hh := PackedTranspose.publicationHeaderInput_of_generated_masters pubSources
      ((Fin.castAdd_injective _ _).comp hpubInj) g.a (L-2*radius) W Vpub (Sizes.s n₀ i) origins geometryBaseline
      (by
        intro k hk
        rcases PackedTranspose.publicationFundamentalIndex_cases k hk with rfl | rfl | rfl | rfl | rfl
        · simpa [pubSources,Function.comp_apply,hprefix,PackedTranspose.publicationHeaderWords] using hreplicaLength
        · simpa [pubSources,Function.comp_apply,hprefix,PackedTranspose.publicationHeaderWords] using hpubCore
        · simpa [pubSources,Function.comp_apply,hprefix,PackedTranspose.publicationHeaderWords] using hwordLength
        · simpa [pubSources,Function.comp_apply,hprefix,hPubWidth,PackedTranspose.publicationHeaderWords] using (congrArg List.length (hGorigin 4)).trans hOriginWidth
        · simpa [pubSources,Function.comp_apply,hprefix,PackedTranspose.publicationHeaderWords] using hpubAmbient)
    simpa only [PackedTranspose.publicationGeneratedMasterState,pubBaseline,dimensionSources,originBaseline,a,
      pubSources,Function.comp_def,hprefix,hN] using hh
  have hDoff (k) (h0 : k ≠ classCallerRegister (pubSrc 0)) (h1 : k ≠ classCallerRegister (pubSrc 1))
      (h2 : k ≠ classCallerRegister (pubSrc 2)) (h9 : k ≠ classCallerRegister (pubSrc 9))
      (h6 : k ≠ classCallerRegister (pubSrc 6)) : pubBaseline.R k = geometryBaseline.R k := by
    exact (PackedTranspose.publicationDimensionsLoaded_off dimensionSources g.a indices.length originBaseline k h1 h0 h2).trans
      (hOoff k h9 h6)
  have hblankD (j) : pubBaseline.R (Fin.natAdd (T+175) j) = [] := by
    apply (hDoff _ ?_ ?_ ?_ ?_ ?_).trans (hGblank j)
    all_goals simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc _)) j).symm
  have hsourceD : pubBaseline.R numerical = [] :=
    (hDoff _ (hcaller.ne (hpubOff 0)).symm (hcaller.ne (hpubOff 1)).symm
      (hcaller.ne (hpubOff 2)).symm hpOff.symm hcOff.symm).trans hGsource
  have hdstD : pubBaseline.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail :=
    (hDoff _ (hcaller.ne (houtMasters 0 (by simp))) (hcaller.ne (houtMasters 1 (by simp)))
      (hcaller.ne (houtMasters 2 (by simp))) (hcaller.ne houtPacket) (hcaller.ne houtCount)).trans hGdst
  obtain ⟨rows,v₂,n₂,hu₂,hn₂,he₂⟩ := PackedTranspose.caller_publish_outputs_exec_within body
    (Fin.castAdd 175 (bank (.recovery (.control .result)))) (Fin.castAdd 175 output)
    ((Fin.castAdd_injective _ _).ne hout) hstates a g.a (L-2*radius) Vpub batch outputs
    (by rw [hbatch]; exact hgood) pubClass keys hwidth g.hwidth rfl hW (by simpa only [hformat,hjobCount] using pubBounds) hA depth ambient hambient outputTail vD pubBaseline
    [] pubSources (fun j => (Fin.castAdd_injective _ _).ne (hpubOff j))
    (by simpa only [pubSources,Function.comp_def,hprefix,hformat] using hinputD)
    hblankD hpubLeft (by simpa only [hprefix] using hsourceD)
    (by simpa only [hprefix] using hdstD)
  have hraw : outputs.reverse.flatten.length = indices.length*(2^g.a*((L-2*radius)*W)) := by
    have hh := batch.outputs_volume outputs (by rw [hbatch]; exact hgood)
    simpa only [hjobCount,hformat] using hh
  simp only [hformat,hjobCount,hraw] at hn₂
  let ys := (List.ofFn fun j => pubClass.output batch.W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail
  obtain ⟨vR,huR,heR⟩ := PackedTranspose.retirePublicationDimensions_exec_within body
    dimensionSources hdimInj g.a indices.length (Fin.castAdd 175 output)
    (by
      intro j hj
      have hi : PackedTranspose.publicationDimensionSourceIndex j ∈ [(0 : Fin 10),1,2] := by
        simp only [List.mem_cons,List.not_mem_nil,or_false] at hj
        rcases hj with rfl | rfl | rfl <;> decide
      exact (Fin.castAdd_injective _ _).ne (houtMasters _ hi).symm)
    ys v₂ originBaseline hdimBlank depth
  simp only [hprefix] at heR
  obtain ⟨v₃,hu₃,he₃⟩ := retireOriginPacket_exec_within body
    (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) (hsrcSep 9 6 (by decide)) Vpub origins
    (classCallerRegister output) (hcaller.ne houtPacket) (hcaller.ne houtCount) ys vR geometryBaseline
    ((hGpub 9 (by decide) (by decide)).trans hpacketBlank)
    ((hGpub 6 (by decide) (by decide)).trans hcountBlank) depth
  obtain ⟨v₄,hu₄,he₄⟩ := PublicationGeometryControls.retire_exec_within body geometryPlacement hgeometryInj
    (Sizes.s n₀ i) (L-2*radius) (classCallerRegister output)
    (by rw [hgeo3]; exact hcaller.ne (houtGeometry 4 (by simp)))
    (by rw [hgeo4]; exact hcaller.ne (houtGeometry 8 (by simp))) ys v₃ S
    (by rw [hgeo3]; exact hgeometryBlank 4 (by simp))
    (by rw [hgeo4]; exact hgeometryBlank 8 (by simp)) depth
  have hreplicas : Fs.reverse = List.ofFn replica := by
    apply List.ext_getElem
    · simp only [List.length_reverse,List.length_ofFn,g.hpower]
    · intro j hj hj'
      simp only [List.getElem_ofFn]
      rfl
  have hmetadata (r) (hr : r ∈ batch.records) :
      r.p = Sizes.p n₀ ∧ r.Fs = Fs.reverse ∧ batch.J r = J := by
    rw [hbatch] at hr
    obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
    exact ⟨rfl,rfl,rfl⟩
  have hrowSpec := rows.classRows_spec pubClass keys (Sizes.p n₀) replica J
    (fun r hr => (hmetadata r hr).1) hwidth
    (fun r hr => (hmetadata r hr).2.1.trans hreplicas) (fun r hr => (hmetadata r hr).2.2)
  have hpublishedLength (j : Fin (2^g.a)) :
      (pubClass.output batch.W g.hwidth (rows.classRows pubClass keys j) (ambient j)).length = Sizes.s n₀ i*W := by
    simpa only [hformat] using pubClass.output_length batch.W g.hwidth (rows.classRows pubClass keys j)
      (rows.classRows_length pubClass keys hwidth j) (ambient j)
      (by simpa only [hformat] using hambient j)
  have hysLength : ys.length = (S.R (classCallerRegister output)).length := by
    have hp : ∀ row ∈ List.ofFn (fun j => pubClass.output batch.W g.hwidth (rows.classRows pubClass keys j) (ambient j)),
        row.length = Sizes.s n₀ i*W := by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact hpublishedLength j
    have ha : ∀ row ∈ List.ofFn ambient, row.length = Sizes.s n₀ i*W := by
      intro row hr
      obtain ⟨j,rfl⟩ := List.mem_ofFn.mp hr
      exact hambient j
    simp only [ys,hdst,List.length_append,Fast.length_flatten_const _ hp,Fast.length_flatten_const _ ha,List.length_ofFn]
  have hsize := mn_replace_right_size_of_length v v₄ S (classCallerRegister output) ys hysLength
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add heG (mn_seq_within_add heO (mn_seq_within_add heD (mn_seq_within_add he₂ (mn_seq_within_add heR (mn_seq_within_add he₃ he₄))))))
  refine ⟨v₄,n₁+(nG+(nO+(nD+(n₂+(retireDimensionCost+((2*(origins.length*Vpub+origins.length)+5)+retireGeometryCost)))))),outputs,rows,
    hu₄.trans (hu₃.trans (huR.trans (hu₂.trans (huD.trans (huO.trans (huG.trans hu₁)))))),?_,hgood,?_,?_,?_⟩
  · simp only [Nat.cast_add]
    exact add_le_add hn₁ (add_le_add (by exact_mod_cast hnG) (add_le_add (by exact_mod_cast hnO) (add_le_add (by exact_mod_cast hnD) (add_le_add (by exact_mod_cast hn₂) le_rfl))))
  · simpa only [hformat] using hrowSpec
  · simpa only [ys,hformat] using hsize
  · simpa only [hprefix,hformat,hjobCount,numerical,ys,Nat.add_zero,retireDimensionCost,retireGeometryCost,a] using hwhole

end IntegerMultBounds.MathlibTM2.Cost
