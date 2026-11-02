module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedCommonCoreClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRestoringGatherData
/-! Common-format numerical execution from caller metadata and fresh private
banks. The complete trace retains certified output and restores every workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Fast.Main IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
namespace ComputedClassBanks
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
variable {T Q K s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)
theorem restoringCommonCoreClassRun_exec (b : RawRecoveryProgramBounds Q (prime+K) U)
    (p u l target t width L : ℕ) (α gap : ℝ) (C : ZMod s → GaussianInt)
    (V : Fin (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices s width (localityDepth p target*PhaseCellBand.width p u) L)[j.val]
      PackedHaloParameterBounds (p := p) (l := l) (t := t) (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).1)
        (b := (coreHaloEndpoints s width k (PhaseCellBand.width p u) (localityDepth p target)).2) (V := V j) α gap C)
    (Fs : List (ZMod s → GaussianInt)) (hF : ∀ F ∈ Fs, ∀ j, ‖value p (F j)‖ ≤ 1) :
    let B := inverseCallerWordWidth p u l target s t
    let W := packedHaloCommonWidth p l s u (target+1) 2
    let radius := localityDepth p target*PhaseCellBand.width p u
    let indices := coreGatherIndices s width radius L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := (prime+K))
      p u l target t width indices[j.val] (V j) α gap C Fs.reverse (bounds j)
        (by intro F hmem i; exact hF F (List.mem_reverse.mp hmem) i)
    let st : TblSt 12 (prime+K) := ⟨commonInputValues p u l target s t B W Fs.length radius L,[]⟩
    ∀     (D Cprog reserve depth : ℕ)
    (rg : TblR 12 → Fin ((T+175)+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (fullExposedClassBank bank) k)
     (hfitValues : ∀ i, st.val i < 2^D)
    (hstock : ∀ r ∈ (List.ofFn jobs), (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).coreStock b B r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).clock (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).work (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).src (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).saved (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).count (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).tmp (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).spare (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hcoreWidth : 0 < width) (hwide : s+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ (prime+K)) (hV : 0 < B)
    (v : HS ((T+175)+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks ((T+175)+PackedTranspose.tapeCount) (prime+K)) 
    (src : Fin 4 → Fin ((T+175)+PackedTranspose.tapeCount)) (hsrc : ∀ i k, src i ≠ (fullExposedClassBank bank) k)
    (hs : S.R (src 0) = binSyms B s) (hw : S.R (src 1) = binSyms B width)
    (hr : S.R (src 2) = binSyms B radius) (hL : S.R (src 3) = binSyms B L)
    (Vg : ℕ) (borrowed : List (Fin (prime+K+4)))
    (g : RestoringGatherData (Q := Q) bank Vg s width radius L W Fs borrowed S)
    (hinput : tblHolds rg S (tblRho D (List.replicate D tick) [] st))
    (hblank : ∀ i, i ≠ .control .source → S.R ((fullExposedClassBank bank) i) = [])
    (hleft : ∀ i, S.L (recovery (fullExposedClassBank bank) (.work i)) = []) ,
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ (24*B+25)+((g.timeCost+(unaryCopiesCost D st.val (inputCopies (fullExposedClassBank bank))+((preparedCoreOriginsCost B s width radius L+recoveryPayloadCountCost Fs.length L W)+
        (((List.ofFn jobs).map ((plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+(2*((List.ofFn jobs).length+Fs.length*(L*W))+5))+(2*inputVolume st.val+2*(inputRegisters (fullExposedClassBank bank)).length+1)))+(8*B+9)) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+(2*(24*B+25)+
        (g.stockAllowance+(3*unaryCopiesCost D st.val (inputCopies (fullExposedClassBank bank))+(((3*preparedCoreOriginsCost B s width radius L+2*recoveryPayloadCountCost Fs.length L W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters (fullExposedClassBank bank)).length+1)))))) depth
        (initializedClassProgram (fullExposedClassBank bank) src (.seq g.program (inputClassProgram (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj) b rg))) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result
          (outputs.reverse.flatten++S.R (plan (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj)).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S src hsrc hs hw hr hL Vg borrowed g hinput hblank hleft
  have hsourceBlank : S.R (control (fullExposedClassBank bank) .source) = [] := by
    simpa only [control,fullExposedClassBank_apply,classCallerRegister,embStk,Function.comp_apply] using g.houtput
  apply initializedPreparedCommonCoreClassRun_exec (body := body)
    (fullExposedClassBank bank) (fullExposedClassBank_injective bank hinj) b
    p u l target t width L α gap C V bounds Fs hF
    D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody hcoreWidth hwide hHfit hA hB
    v S src hsrc hs hw hr hL g.program g.timeCost g.stockAllowance hsourceBlank ?_ hinput hblank hleft
  intro w
  exact g.exec hinj src body w depth

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
