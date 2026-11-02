module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPaidRestoringClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInputTableClassRun

/-! Selected class execution includes actual external-table initialization and
retirement from retained caller words. Only certified numerical output remains. -/
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

theorem selectedTableRestoringComputedCoreClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (hstates : FixedStreamedBank.stateCount ≤ Q) (ct cV cD : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] (u target L : ℕ)
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
    (hleft : ∀ j, S.L (recovery (fullExposedClassBank bank) (.work j)) = []) ,
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      (n : ℝ) ≤ (((126*D+132 : ℕ) : ℝ)+((Sizes.T n₀+(coreExposureTrafficFactor cV (1032+8*ct)+40*cV+48*cD+6185 : ℕ)*
        (Fs.length*Sizes.s n₀ i*W : ℕ)+432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*Sizes.s n₀ i*W : ℕ)*Sizes.d n₀*((Sizes.ℓ n₀ : ℝ)^Parameters.tau+1))+
        8*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*Fs.length+32*(B : ℝ)+35)) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(3*(100*D+105)+
        (2*(24*B+25)+((Sizes.T n₀+(3*coreExposureTrafficFactor cV (1032+8*ct)+60*cV+72*cD+268+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*Sizes.s n₀ i*W))+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀+
          495*D+24*Fs.length)))) depth
        (inputTableClassProgram rg masters widthMaster zeroMaster (initializedClassProgram (fullExposedClassBank bank) src
          (.seq g.program (inputClassProgram (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj) b rg)))) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result
          (outputs.reverse.flatten++S.R (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result))}) := by
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedPaidRestoringComputedCoreClassRun_exec (body := body) bank hinj b hstates ct cV cD
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ u target L hu htarget hLengthGroup α gap C V bounds Fs hFs
  intro B W radius indices jobs st D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB
    v S src hsrc hs hw' hr hL' masters widthMaster zeroMaster value hwidthMaster hzeroMaster hmasterOff
    hgeometryOff hvalues hwidthWord hzeroWord hmasterWords htableBlank Vg borrowed g hExposeWidth hRouteWidth
    hMetadataFit hReplicaVolume hblank hleft
  let M := loadedInputTable rg masters D value S
  have hM (k) (hk : ∀ r, rg r ≠ k) : M.R k = S.R k :=
    loadedInputTable_off rg masters D value S k (fun r => (hk r).symm)
  have htable : tblHolds rg M (tblRho D (List.replicate D tick) [] st) := by
    have hh := chirpBankLoad_holds rg hrg masters D 0 value S htableBlank
    change tblHolds rg M (tblRho D (List.replicate D tick) [] ⟨st.val,[]⟩)
    simpa only [M,loadedInputTable,List.replicate_zero,hvalues] using hh
  have hfresh (j) (hj : j ≠ .control .source) : M.R (fullExposedClassBank bank j) = [] :=
    (hM _ (fun r => hoff r j)).trans (hblank j hj)
  have hfit : ∀ j, value (masters j) < 2^D := by
    intro j
    rw [hvalues]
    exact hfitValues j
  have hresult (r) : rg r ≠ (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result := by
    simpa only [plan,RecoveryBanks.plan,recovery] using hoff r (.recovery (.control .result))
  let runTime : ℝ := (Sizes.T n₀+(coreExposureTrafficFactor cV (1032+8*ct)+40*cV+48*cD+6185 : ℕ)*
        (Fs.length*Sizes.s n₀ i*W : ℕ)+432*(generatedDyadicStageCoeff FixedStreamedBank.tapeCount 6 1+300)*
          (Fs.length*Sizes.s n₀ i*W : ℕ)*Sizes.d n₀*((Sizes.ℓ n₀ : ℝ)^Parameters.tau+1))+
        8*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*Fs.length+32*(B : ℝ)+35
  let runStock : ℕ := 
        (2*(24*B+25)+((Sizes.T n₀+(3*coreExposureTrafficFactor cV (1032+8*ct)+60*cV+72*cD+268+
          12*(streamedDyadicStockCoeff FixedStreamedBank.tapeCount+700))*(Fs.length*Sizes.s n₀ i*W))+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀+
          495*D+24*Fs.length))
  have hrun (w : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) :=
    hn h i u target L hu htarget hLengthGroup α gap C V bounds Fs hFs
      D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB w M src hsrc
      ((hM _ (hgeometryOff 0)).trans hs) ((hM _ (hgeometryOff 1)).trans hw')
      ((hM _ (hgeometryOff 2)).trans hr) ((hM _ (hgeometryOff 3)).trans hL')
      Vg borrowed g hExposeWidth hRouteWidth hMetadataFit hReplicaVolume htable hfresh hleft
  obtain ⟨v',n,outputs,hu,ht,hvalid,he⟩ := inputTableClassRun_exec_within body rg hrg masters widthMaster zeroMaster
    hwidthMaster hzeroMaster hmasterOff D value hfit v S hwidthWord hzeroWord hmasterWords htableBlank
    (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result hresult
    (initializedClassProgram (fullExposedClassBank bank) src
      (.seq g.program (inputClassProgram (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj) b rg)))
    runTime runStock depth (List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs)) hrun
  change (n : ℝ) ≤ (((126*D+132 : ℕ) : ℝ)+runTime) at ht
  exact ⟨v',n,outputs,hu,ht,hvalid,he⟩

end IntegerMultBounds.MathlibTM2.Cost
