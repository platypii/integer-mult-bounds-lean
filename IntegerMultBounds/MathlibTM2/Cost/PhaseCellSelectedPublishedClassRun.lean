module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedTableRestoringClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCallerPublication
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonCorePublicationBatch
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedBatchReplicaCount
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedPublicationPlacement
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPlacedPublicationOrigins
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOwnedOriginPacket
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
    ∀ (a Vpub : ℕ) (output : Fin T) (hout : bank (.recovery (.control .result)) ≠ output)
    (pubSrc : Fin 13 → Fin T) (hpubOff : ∀ j, pubSrc j ≠ bank (.recovery (.control .result)))
    (ambient : Fin (2^g.a) → List (Fin (prime+K+4)))
    (hambient : ∀ j, (ambient j).length = Sizes.s n₀ i*W)
    (outputTail : List (Fin (prime+K+4)))
    (hpubInj : Function.Injective pubSrc)
    (hpacketBlank : S.R (classCallerRegister (pubSrc 9)) = [])
    (hcountBlank : S.R (classCallerRegister (pubSrc 6)) = [])
    (houtPacket : output ≠ pubSrc 9) (houtCount : output ≠ pubSrc 6)
    (originSources : Fin 7 → Fin T) (hOriginInj : Function.Injective originSources)
    (hOriginPacket : originSources 5 = pubSrc 9) (hOriginCount : originSources 6 = pubSrc 6)
    (hOriginOff : ∀ j, originSources j ≠ bank (.recovery (.control .result)))
    (hOriginWide : Sizes.s n₀ i+amortizedCoreWidth ct (Sizes.p n₀)+2*radius < 2^Vpub)
    (hOriginLength : L < 2^Vpub)
    (hOriginWords : ∀ j : Fin 4, S.R (classCallerRegister (originSources (Fin.castAdd 3 j))) =
      binSyms Vpub (![Sizes.s n₀ i,amortizedCoreWidth ct (Sizes.p n₀),radius,L] j))
    (hOriginWidth : (S.R (classCallerRegister (originSources 4))).length = Vpub)
    (hpubWords : ∀ j, j ≠ 6 → j ≠ 9 → S.R (classCallerRegister (pubSrc j)) =
      PackedTranspose.publicationHeaderWords a g.a (L-2*radius) W Vpub (Sizes.s n₀ i)
        (coreSubsetPublicationWindows (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀))
          pubClass.length g.hwidth pubClass.indices pubClass.sublist).origins [] j)
    (hpubBlank : ∀ j, S.R (Fin.natAdd (T+175) j) = [])
    (hpubLeft : ∀ j, (embStk (selectedPublicationPlacement bank output) S).L j = [])
    (hdst : S.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail)
    (pubBounds : PackedTranspose.PublicationShapeBounds a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) indices.length),
    let e := publicationOriginPlacement (Fin.castAdd 175 ∘ originSources)
    let pubSources := Fin.castAdd 175 ∘ pubSrc
    let pubBaseline := originPacketState (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) Vpub origins S
    let metadata := publicationMetadataVolume pubSources pubBaseline
    let originCost := preparedCoreOriginsCost Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L
    ∃ v', ∃ n : ℕ, ∃ outputs, ∃ rows : batch.Rows, v'.user = v.user ∧
      (n : ℝ) ≤ runTime+(originCost+((6*metadata+79)+
        (PackedTranspose.retainedPublicationTimeCost (K := K) hstates a g.a (L-2*radius) Vpub
          W indices.length pubClass g.hwidth (indices.length*(2^g.a*((L-2*radius)*W)))+(2*metadata+27))+(2*(origins.length*Vpub+origins.length)+5)) : ℕ) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (runStock+(3*originCost+(2*(6*metadata+79)+PackedTranspose.retainedPublicationStock (K := K) (U := U)
          hstates a g.a (L-2*radius) Vpub W indices.length pubClass)))) depth
        (.seq runProg (.seq (placedPublicationOrigins e) (.seq (PackedTranspose.callerPublicationProgram pubSources
          (Fin.castAdd 175 (bank (.recovery (.control .result)))) (Fin.castAdd 175 output) hstates)
          (clearWords [classCallerRegister (pubSrc 9),classCallerRegister (pubSrc 6)]))))
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
    origins a Vpub output hout pubSrc hpubOff ambient hambient outputTail hpubInj hpacketBlank hcountBlank
    houtPacket houtCount originSources hOriginInj hOriginPacket hOriginCount hOriginOff hOriginWide hOriginLength
    hOriginWords hOriginWidth hpubWords hpubBlank hpubLeft
    hdst pubBounds e pubSources pubBaseline metadata originCost
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
  have hcorePacket := pubBounds.packetPositive
  have hpubBits := pubBounds.stageBits
  have hW : 1 ≤ batch.W := by
    change 1 ≤ W
    by_contra hz
    have hw : W = 0 := by omega
    simp only [hw,Nat.mul_zero,lt_self_iff_false] at hcorePacket
  have hcaller : Function.Injective (classCallerRegister : Fin T → Fin ((T+175)+PackedTranspose.tapeCount)) :=
    (Fin.castAdd_injective _ _).comp (Fin.castAdd_injective _ _)
  have hsrcSep (j k : Fin 13) (hjk : j ≠ k) :
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
  have originInput : PublicationOriginInput e Vpub (Sizes.s n₀ i) (amortizedCoreWidth ct (Sizes.p n₀)) radius L S :=
    publicationOriginPlacement_input _ S Vpub _ _ _ _ hOriginWide hOriginLength
      (by intro j; simpa only [Function.comp_apply,hprefix] using hOriginWords j)
      (by simpa only [Function.comp_apply,hprefix] using hOriginWidth) hpubBlank
  obtain ⟨vO,nO,huO,hnO,heO⟩ := placedOwnedPublicationOrigins_after_update_exec_within (body := body) e he
    (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) he109 he116 numerical outputs.reverse.flatten heOff
    g.hwidth originInput.geometryFit originInput.lengthFit hA (by omega) v₁ S
    originInput.widthLength originInput.ambientWord originInput.coreWidthWord originInput.radiusWord
    originInput.haloLengthWord originInput.zero originInput.tableBlank
    (by rw [he109]; exact hpacketBlank) originInput.savedBlank originInput.tmpBlank
    (by rw [he116]; exact hcountBlank) depth
  have hpOff : classCallerRegister (pubSrc 9) ≠ numerical := hcaller.ne (hpubOff 9)
  have hcOff : classCallerRegister (pubSrc 6) ≠ numerical := hcaller.ne (hpubOff 6)
  have hDoff (k) (hp : k ≠ classCallerRegister (pubSrc 9)) (hc : k ≠ classCallerRegister (pubSrc 6)) :
      pubBaseline.R k = S.R k := originPacketState_off _ _ _ _ S k hp hc
  have hwordsD (j : Fin 13) : pubBaseline.R (classCallerRegister (pubSrc j)) =
      PackedTranspose.publicationHeaderWords a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) origins [] j :=
    PackedTranspose.publicationHeaderWords_of_owned_packet (classCallerRegister ∘ pubSrc) (hcaller.comp hpubInj)
      a g.a (L-2*radius) W Vpub (Sizes.s n₀ i) origins S hpubWords j
  have hblankD (j) : pubBaseline.R (Fin.natAdd (T+175) j) = [] := by
    apply (hDoff _ ?_ ?_).trans (hpubBlank j)
    · simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc 9)) j).symm
    · simpa only [←hprefix] using (prefix_ne_routing (Fin.castAdd 175 (pubSrc 6)) j).symm
  have hsourceD : pubBaseline.R numerical = [] := (hDoff _ hpOff.symm hcOff.symm).trans hsource
  have hdstD : pubBaseline.R (classCallerRegister output) = (List.ofFn ambient).flatten++outputTail :=
    (hDoff _ (hcaller.ne houtPacket) (hcaller.ne houtCount)).trans hdst
  obtain ⟨rows,v₂,n₂,hu₂,hn₂,he₂⟩ := PackedTranspose.caller_publish_outputs_exec_within body
    (Fin.castAdd 175 (bank (.recovery (.control .result)))) (Fin.castAdd 175 output)
    ((Fin.castAdd_injective _ _).ne hout) hstates a g.a (L-2*radius) Vpub batch outputs
    (by rw [hbatch]; exact hgood) pubClass keys hwidth g.hwidth rfl hW (by simpa only [hformat,hjobCount] using pubBounds) hA depth ambient hambient outputTail vO pubBaseline
    [] pubSources (fun j => (Fin.castAdd_injective _ _).ne (hpubOff j))
    (by intro j; simpa only [pubSources,Function.comp_apply,hprefix,hformat] using hwordsD j)
    hblankD hpubLeft (by simpa only [hprefix] using hsourceD)
    (by simpa only [hprefix] using hdstD)
  have hraw : outputs.reverse.flatten.length = indices.length*(2^g.a*((L-2*radius)*W)) := by
    have hh := batch.outputs_volume outputs (by rw [hbatch]; exact hgood)
    simpa only [hjobCount,hformat] using hh
  simp only [hformat,hjobCount,hraw] at hn₂
  let ys := (List.ofFn fun j => pubClass.output batch.W g.hwidth (rows.classRows pubClass keys j) (ambient j)).flatten++outputTail
  obtain ⟨v₃,hu₃,he₃⟩ := retireOriginPacket_exec_within body
    (classCallerRegister (pubSrc 9)) (classCallerRegister (pubSrc 6)) (hsrcSep 9 6 (by decide)) Vpub origins
    (classCallerRegister output) (hcaller.ne houtPacket) (hcaller.ne houtCount) ys v₂ S hpacketBlank hcountBlank depth
  have hwhole := mn_seq_within_add he₁ (mn_seq_within_add heO (mn_seq_within_add he₂ he₃))
  refine ⟨v₃,n₁+(nO+(n₂+(2*(origins.length*Vpub+origins.length)+5))),outputs,rows,
    hu₃.trans (hu₂.trans (huO.trans hu₁)),?_,hgood,?_⟩
  · simp only [Nat.cast_add]
    exact add_le_add hn₁ (add_le_add (by exact_mod_cast hnO) (add_le_add (by exact_mod_cast hn₂) le_rfl))
  · simpa only [hprefix,hformat,hjobCount,numerical,ys,Nat.add_zero] using hwhole

end IntegerMultBounds.MathlibTM2.Cost
