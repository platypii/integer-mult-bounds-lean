module
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposedInputClassRun
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCommonCoreClassRun
/-! Actual common-format proper-core jobs consume the physical ambient gather
stream with its explicit reversed replica order. -/
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
variable {t₀ T Q c d W₀ K s : ℕ} [NeZero s] {P U : Type} {body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U}
  (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
open ComputedRecoveryPlan (routedPayload)
theorem allocatedExposedCommonCoreClassRun_exec (b : RawRecoveryProgramBounds Q (prime+K) U)
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
    (rg : TblR 12 → Fin (T+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (extendedBank bank) k)
     (hfitValues : ∀ i, st.val i < 2^D)
    (hstock : ∀ r ∈ (List.ofFn jobs), (plan (extendedBank bank) (extendedBank_injective bank hinj)).coreStock b B r Cprog ≤ reserve)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).clock (plan (extendedBank bank) (extendedBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (extendedBank bank) (extendedBank_injective bank hinj)).work (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).count (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).spare (plan (extendedBank bank) (extendedBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hcoreWidth : 0 < width) (hwide : s+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ (prime+K)) (hV : 0 < B)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) 
    (Vg a Dg : ℕ)
     (borrowed : List (Fin (prime+K+4)))
    (g : AllocatedRealGatherData (Q := Q) bank Vg s width radius L W a Dg Fs borrowed S)
    (hready : InputReady (extendedBank bank) (extendedBank_injective bank hinj) rg B D s width radius L st S) ,
    ∃ v' n outputs, v'.user = v.user ∧
      n ≤ g.timeCost+(unaryCopiesCost D st.val (inputCopies (extendedBank bank))+((preparedCoreOriginsCost B s width radius L+recoveryPayloadCountCost Fs.length L W)+
        (((List.ofFn jobs).map ((plan (extendedBank bank) (extendedBank_injective bank hinj)).coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+(2*((List.ofFn jobs).length+Fs.length*(L*W))+5))+(2*inputVolume st.val+2*(inputRegisters (extendedBank bank)).length+1)) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (g.stockAllowance+(3*unaryCopiesCost D st.val (inputCopies (extendedBank bank))+(((3*preparedCoreOriginsCost B s width radius L+2*recoveryPayloadCountCost Fs.length L W)+reserve)+3*(2*inputVolume st.val+2*(inputRegisters (extendedBank bank)).length+1))))) depth
        (.seq g.program (inputClassProgram (extendedBank bank) (extendedBank_injective bank hinj) b rg)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result
          (outputs.reverse.flatten++S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result))}) := by
  intro B W radius indices jobs st D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hcoreWidth hwide hHfit hA hB v S Vg a Dg borrowed g hready
  apply preparedCommonCoreClassRun_exec (body := body) (extendedBank bank) (extendedBank_injective bank hinj) b p u l target t width L α gap C V bounds Fs hF
    D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody hcoreWidth hwide hHfit hA hB v S
    g.program g.timeCost g.stockAllowance g.houtput ?_ hready
  obtain ⟨v',n,hu,hn,he⟩ := g.exec body v depth
  exact ⟨v',n,hu,hn,he⟩

end ComputedClassBanks
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
