module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPreparedClassRun
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassBill
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCommonInputCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedExposedCommonCoreClassRun

/-! Selected numerical and generated-input bounds apply to the actual exposed
proper-core run. Physical gather costs remain explicit in the same trace. -/
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

theorem selectedAllocatedExposedComputedCoreClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P (T+PackedTranspose.tapeCount) Q (prime+K) U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q (prime+K) U) (ct : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∃ Cstock : ℕ, ∀ᶠ n₀ : ℕ in Filter.atTop, ∀ (h : Sizes.Big n₀)
    (i : Fin (Sizes.d n₀)) [NeZero (Sizes.s n₀ i)] (u target width L : ℕ)
    (hu : u ≤ Sizes.p n₀) (htarget : target ≤ ct*Sizes.p n₀)
    (hw : 0 < width) (hwidth : width ≤ Sizes.s n₀ i) (hL : L ≤ Sizes.s n₀ i)
    (hguard : localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u ≤ width)
    (hcell : Sizes.s n₀ i/(Sizes.t n₀ i-Sizes.s n₀ i)+1 ≤ width)
    (hprepare : (Sizes.p n₀)^2+(PhaseCellBand.width (Sizes.p n₀) u)^2 ≤ width)
    (α gap : ℝ) (C : ZMod (Sizes.s n₀ i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n₀ i) width
      (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n₀ i) width
        (localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n₀)
        (l := haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (t := Sizes.t n₀ i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n₀ i) width k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n₀ i) width k (PhaseCellBand.width (Sizes.p n₀) u)
          (localityDepth (Sizes.p n₀) target)).2) (V := V j) α gap C)
    (Fs : List (ZMod (Sizes.s n₀ i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n₀) (F j)‖ ≤ 1),
    let B := inverseCallerWordWidth (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i)
    let W := packedHaloCommonWidth (Sizes.p n₀) (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) (Sizes.s n₀ i) u (target+1) 2
    let radius := localityDepth (Sizes.p n₀) target*PhaseCellBand.width (Sizes.p n₀) u
    let indices := coreGatherIndices (Sizes.s n₀ i) width radius L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := (prime+K))
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i) width indices[j.val] (V j) α gap C Fs.reverse (bounds j)
        (by intro F hmem i; exact hF F (List.mem_reverse.mp hmem) i)
    let st : TblSt 12 (prime+K) := ⟨commonInputValues (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.s n₀ i) (Sizes.t n₀ i) B W Fs.length radius L,[]⟩
    ∀ (D Cprog depth : ℕ)
    (rg : TblR 12 → Fin (T+PackedTranspose.tapeCount)) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ (extendedBank bank) k)
     (hfitValues : ∀ i, st.val i < 2^D)
    (hpush : mnProgPush (descriptorSolverSchedule (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).clock (plan (extendedBank bank) (extendedBank_injective bank hinj)).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan (extendedBank bank) (extendedBank_injective bank hinj)).work (plan (extendedBank bank) (extendedBank_injective bank hinj)).src (plan (extendedBank bank) (extendedBank_injective bank hinj)).saved (plan (extendedBank bank) (extendedBank_injective bank hinj)).count (plan (extendedBank bank) (extendedBank_injective bank hinj)).tmp (plan (extendedBank bank) (extendedBank_injective bank hinj)).spare (plan (extendedBank bank) (extendedBank_injective bank hinj)).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hwide : (Sizes.s n₀ i)+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ (prime+K)) (hV : 0 < B)
    (v : HS (T+PackedTranspose.tapeCount) Q (prime+K) U) (S : Stacks (T+PackedTranspose.tapeCount) (prime+K)) 
    (Vg a Dg : ℕ)
     (borrowed : List (Fin (prime+K+4)))
    (g : AllocatedRealGatherData (Q := Q) bank Vg (Sizes.s n₀ i) width radius L W a Dg Fs borrowed S)
    (hready : InputReady (extendedBank bank) (extendedBank_injective bank hinj) rg B D (Sizes.s n₀ i) width radius L st S) ,
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      (n : ℝ) ≤ (g.timeCost : ℝ)+
        8*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*Fs.length ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (g.stockAllowance+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀+
          495*D+24*Fs.length)) depth
        (.seq g.program (inputClassProgram (extendedBank bank) (extendedBank_injective bank hinj) b rg)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result
          (outputs.reverse.flatten++S.R (plan (extendedBank bank) (extendedBank_injective bank hinj)).result))}) := by
  obtain ⟨F,hF,Cstock,hclass⟩ := selectedPreparedComputedCoreClassRun_exec (body := body) (extendedBank bank) (extendedBank_injective bank hinj) b ct
  refine ⟨F,hF,Cstock,?_⟩
  filter_upwards [hclass] with n₀ hn
  intro h i _ u target width L hu htarget hw hwidth hL hguard hcell hprepare α gap C V bounds Fs hFs
  intro B W radius indices jobs st D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB
    v S Vg a Dg borrowed g hready
  apply hn h i u target width L hu htarget hw hwidth hL hguard hcell hprepare α gap C V bounds Fs hFs
    D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB v S
    g.program g.timeCost g.stockAllowance g.houtput ?_ hready
  obtain ⟨v',n,hu,hn,he⟩ := g.exec body v depth
  exact ⟨v',n,hu,hn,he⟩


end IntegerMultBounds.MathlibTM2.Cost
