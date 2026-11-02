module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassBill
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCommonInputCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPreparedCommonCoreClassRun

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

theorem selectedPreparedComputedCoreClassRun_exec {T Q K : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q (prime+K) U}
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
    (rg : TblR 12 → Fin T) (hrg : Function.Injective rg) (hoff : ∀ r k, rg r ≠ bank k)
     (hfitValues : ∀ i, st.val i < 2^D)
    (hpush : mnProgPush (descriptorSolverSchedule (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).tmp (plan bank hinj).clock (plan bank hinj).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := (prime+K))
        (plan bank hinj).work (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).count (plan bank hinj).tmp (plan bank hinj).spare (plan bank hinj).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hwide : (Sizes.s n₀ i)+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ (prime+K)) (hV : 0 < B)
    (v : HS T Q (prime+K) U) (S : Stacks T (prime+K)) 
    (prep : Pr P T Q (prime+K) U) (prepTime prepStock : ℕ)
    (hsourceBlank : S.R (control bank .source) = [])
    (hprep : ∃ v' n, v'.user = v.user ∧ n ≤ prepTime ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+prepStock)
        depth prep (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (control bank .source)
          (coreSupplierStream (prime+K) width radius L W Fs.reverse))}))
    (hready : InputReady bank hinj rg B D (Sizes.s n₀ i) width radius L st S) ,
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      (n : ℝ) ≤ (prepTime : ℝ)+
        8*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ)+
        165*(D : ℝ)+8*Fs.length ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        (prepStock+
          (45+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀+
          495*D+24*Fs.length)) depth
        (.seq prep (inputClassProgram bank hinj b rg)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update S.R (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  obtain ⟨F,hF,hbill⟩ := selectedComputedCoreClassBill_time_le (T := T) b ct
  obtain ⟨Cstock,hstockBound⟩ := selectedComputedCoreClassStock_sum_le (T := T) b ct
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  refine ⟨F,hF,Cstock+3*(6*cW+9),?_⟩
  filter_upwards [hbill,hstockBound,selectedComputedClassControlTime_linear_le cB cW,selectedCommonInputCost_le ct] with n₀ hn hstockAt hcontrolAt hinputAt
  intro h i _ u target width L hu htarget hw hwidth hL hguard hcell hprepare α gap C V bounds Fs hFs
  intro B W radius indices jobs st D Cprog depth rg hrg hoff hfitValues hpush hbody hwide hHfit hA hB
    v S prep prepTime prepStock hsourceBlank hprep hready
  have hFreverse : ∀ F ∈ Fs.reverse, ∀ j, ‖value (Sizes.p n₀) (F j)‖ ≤ 1 := by
    intro F hmem j; exact hFs F (List.mem_reverse.mp hmem) j
  let raw : HS 392 Q (prime+K) U := ⟨v.flag,v.sym,v.st,fun _ => 0,none,v.user⟩
  let reserve := (39+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀
  have hsum := hstockAt h i u target width L hu htarget hw hwidth hguard hcell hprepare
    α gap C V bounds Fs.reverse hFreverse raw (plan bank hinj) Cprog
  simp only [List.length_reverse] at hsum
  have hstock (r : PackedNormalizedJob (prime+K) (Sizes.s n₀ i)) (hr : r ∈ List.ofFn jobs) :
      (plan bank hinj).coreStock b B r Cprog ≤ reserve :=
    (List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)).trans hsum
  obtain ⟨v',m,outputs,huser,htime,houtputs,hexec⟩ := preparedCommonCoreClassRun_exec (body := body) bank hinj b
    (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i)
    width L α gap C V bounds Fs hFs D Cprog reserve depth rg hrg hoff hfitValues hstock hpush hbody
    hw hwide hHfit hA hB v S prep prepTime prepStock hsourceBlank hprep hready
  have hcost := hn h i u target width L hu htarget hw hwidth hL hguard hcell hprepare
    α gap C V bounds Fs.reverse hFreverse raw (plan bank hinj)
  simp only [List.length_reverse] at hcost
  have hband : PhaseCellBand.width (Sizes.p n₀) u ≤ Sizes.s n₀ i := by
    have hsquare := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (PhaseCellBand.width (Sizes.p n₀) u)
    omega
  have hscalar := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hpacket := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hinputBound : 165*D+8*inputVolume st.val+122 ≤ Sizes.T n₀+165*D+8*Fs.length :=
    hinputAt h i u target B W Fs.length radius L D hu htarget hscalar hpacket (hguard.trans hwidth) hL
  have hinputCost := inputLifecycleCost_eq bank D st.val
  refine ⟨v',m,outputs,huser,?_,houtputs,?_⟩
  · have ht := (Nat.cast_le (α := ℝ)).mpr htime
    have hc := congrArg (fun x : ℕ => (x : ℝ)) hinputCost
    have hi := (Nat.cast_le (α := ℝ)).mpr hinputBound
    push_cast at ht hc hcost hi ⊢
    nlinarith only [ht,hc,hcost,hi]
  · apply hexec.mono
    intro d z hz
    have hcontrol := hcontrolAt h i B width radius L W Fs.length hw hscalar hpacket hL
    have hprep := computedClassPreparationStock_le B (Sizes.s n₀ i) width radius L W Fs.length
    have hscaled := Nat.mul_le_mul_left 3 hcontrol
    have hpad : 3*(6*cW+9)*Fs.length*Sizes.t n₀ i*Sizes.p n₀ ≤
        3*(6*cW+9)*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀ := by
      have hh := Nat.mul_le_mul_left (3*(6*cW+9)*Fs.length*Sizes.t n₀ i*Sizes.p n₀)
        (show 1 ≤ Cprog+1 by omega)
      nlinarith only [hh]
    dsimp only [reserve] at hz
    nlinarith only [hz,hprep,hscaled,hpad,hinputCost,hinputBound]


end IntegerMultBounds.MathlibTM2.Cost
