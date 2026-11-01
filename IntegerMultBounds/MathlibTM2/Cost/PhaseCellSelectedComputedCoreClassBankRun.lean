module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassBill
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCommonCoreClassRun

/-! The selected proper-core class executes from ordinary banks with its complete
fast-time bound, output certificates, exact frame and same-run stock trace. -/
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

theorem selectedComputedCoreClassBankRun_exec {T Q A : ℕ} {U : Type} {P : Type} {body : P → Pr P T Q A U}
    (bank : ComputedClassBank → Fin T) (hinj : Function.Injective bank)
    (b : RawRecoveryProgramBounds Q A U) (ct : ℕ) :
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
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A)
      (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i) width indices[j.val] (V j) α gap C Fs (bounds j) hF
    ∀ (wl : List (Fin (A+4))) (hwl : wl.length = B)
    (Cprog depth : ℕ)
    (hpush : mnProgPush (descriptorSolverSchedule (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).tmp (plan bank hinj).clock (plan bank hinj).savedClock
      (normalizedRecoveryDescriptorStep (P := P) (U := U) (A := A)
        (plan bank hinj).work (plan bank hinj).src (plan bank hinj).saved (plan bank hinj).count (plan bank hinj).tmp (plan bank hinj).spare (plan bank hinj).result b.hR b.hQ)) ≤ Cprog)
    (hbody : ∀ f, mnProgPush (body f) ≤ Cprog)
    (hwide : (Sizes.s n₀ i)+width+2*radius < 2^B)
    (hHfit : L < 2^B) (hA : 4 ≤ A) (hB : 0 < B)
    (v : HS T Q A U) (S : Stacks T A) (tail : List (Fin (A+4)))
    (h37 : (S.R (geometry bank 37)).length = B)
    (hs : S.R (geometry bank 32) = binSyms B (Sizes.s n₀ i)) (hw : S.R (geometry bank 33) = binSyms B width)
    (hr : S.R (geometry bank 34) = binSyms B radius) (hH : S.R (geometry bank 35) = binSyms B L) (hz : S.R (geometry bank 36) = [])
    (htable : ∀ k : Fin 117, k.val < 31 → S.R (geometry bank k) = [])
    (h104 : S.R (geometry bank 104) = []) (h106 : S.R (geometry bank 106) = []) (h116 : S.R (geometry bank 116) = [])
    (hN : (S.R (plan bank hinj).replicas).length = Fs.length) (hhalo : (S.R (control bank .halo)).length = L) (hW : (S.R (plan bank hinj).packet).length = W)
    (hprepBlank : ∀ k ∈ [(control bank .symbols),(control bank .count),(control bank .prepSaved),(control bank .prepTmp)], S.R k = [])
    (hwidth : (S.R (control bank .width)).length = B)
    (hreaderBlank : ∀ k ∈ [(control bank .binary),(plan bank hinj).master.parameters 6,(plan bank hinj).master.parameters 7,
      (control bank .endpointWork),(control bank .endpointSaved),(control bank .endpointTmp)], S.R k = [])
    (hp : (S.R (recovery bank (.control .precision))).length = (Sizes.p n₀))
    (hparameters : ∀ j : Fin 8, j ≠ 6 → j ≠ 7 →
      (S.R (recovery bank (.parameter j))).length =
        ![Sizes.p n₀,u,haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i),target,Sizes.s n₀ i,Sizes.t n₀ i,0,0] j)
    (hscalarWidth : S.R (recovery bank (.scalar .wr)) = wl)
    (hscalar : ∀ i : TblR 25, i ≠ .wr → S.R (recovery bank (.scalar i)) = [])
    (hmasters : ∀ i, S.R (recovery bank (.master i)) = [])
    (hcontrols : ∀ i, i ∉ RecoveryBanks.liveControls → S.R (recovery bank (.control i)) = [])
    (hleft : ∀ i, S.L (recovery bank (.work i)) = [])
    (hoffset : (S.R (recovery bank (.control .cropOffset))).length = radius)
    (hrows : (S.R (recovery bank (.control .cropRows))).length = L-2*radius)
    (hblank : ∀ i, S.R ((plan bank hinj).work i) = []) (hsaved : S.R (control bank .saved) = []) (htmp : S.R (control bank .tmp) = [])
    (hsource : S.R (control bank .source) = coreSupplierStream A width radius L W Fs++tail) (hloopSaved : S.R (control bank .loopSaved) = []),
    ∃ v', ∃ n : ℕ, ∃ outputs, v'.user = v.user ∧
      (n : ℝ) ≤ 7*Sizes.T n₀+F*Fs.length*(Sizes.t n₀ i : ℝ)*
        (1+(PhaseCellBand.width (Sizes.p n₀) u : ℝ)^2/Sizes.d n₀)*(Sizes.p n₀ : ℝ)^(129/128 : ℝ) ∧
      List.Forall₂ PackedNormalizedJob.output (List.ofFn jobs) outputs ∧
      ExecWithin body (fun d z => mnSize z+d ≤ mnSize (Host.mk v S)+depth+
        ((42+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀)) depth
        ((plan bank hinj).classRun b (normalize bank hinj) (queue bank hinj) (crop bank hinj) (link bank hinj) (geometry bank) (control bank .symbols) (control bank .prepSaved) (control bank .prepTmp) (control bank .width) (control bank .halo) (control bank .binary) (control bank .endpointWork)
          (control bank .endpointSaved) (control bank .endpointTmp) (control bank .count) (control bank .source) (control bank .saved) (control bank .tmp) (control bank .loopSaved)) (Host.mk v S) n
        (Host.mk v' {S with R := (Function.update (Function.update S.R (control bank .source) tail) (plan bank hinj).result
          (outputs.reverse.flatten++S.R (plan bank hinj).result))}) := by
  obtain ⟨F,hF,hbill⟩ := selectedComputedCoreClassBill_time_le (T := T) b ct
  obtain ⟨Cstock,hstockBound⟩ := selectedComputedCoreClassStock_sum_le (T := T) b ct
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  refine ⟨F,hF,Cstock+3*(6*cW+9),?_⟩
  filter_upwards [hbill,hstockBound,selectedComputedClassControlTime_linear_le cB cW] with n₀ hn hstockAt hcontrolAt
  intro h i _ u target width L hu htarget hw hwidth hL hguard hcell hprepare α gap C V bounds Fs hFs
  intro B W radius indices jobs
  intro wl hwl Cprog depth hpush hbody hwide hHfit hA hB
    v S tail h37 hs hw' hr hH hz htable h104 h106 h116 hN hhalo hW hprepBlank hwidth'
    hreaderBlank hp hparameters hscalarWidth hscalar hmasters hcontrols hleft hoffset hrows
    hblank hsaved htmp hsource hloopSaved
  let raw : HS 392 Q A U := ⟨v.flag,v.sym,v.st,fun _ => 0,none,v.user⟩
  let reserve := (39+3*Cprog)*Sizes.T n₀+Cstock*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀
  have hsum := hstockAt h i u target width L hu htarget hw hwidth hguard hcell hprepare
    α gap C V bounds Fs hFs raw (plan bank hinj) Cprog
  have hstock (r : PackedNormalizedJob A (Sizes.s n₀ i)) (hr : r ∈ List.ofFn jobs) :
      (plan bank hinj).coreStock b B r Cprog ≤ reserve :=
    (List.le_sum_of_mem (List.mem_map.mpr ⟨r,hr,rfl⟩)).trans hsum
  obtain ⟨v',m,outputs,huser,htime,houtputs,hexec⟩ := commonCoreClassRun_exec (body := body) bank hinj b
    (Sizes.p n₀) u (haloInverseRingLog (Sizes.s n₀ i) (Sizes.t n₀ i)) target (Sizes.t n₀ i)
    width L α gap C V bounds Fs hFs wl hwl Cprog reserve depth hstock hpush hbody
    hw hwide hHfit hA hB v S tail h37 hs hw' hr hH hz htable h104 h106 h116
    hN hhalo hW hprepBlank hwidth' hreaderBlank hp hparameters hscalarWidth hscalar hmasters
    hcontrols hleft hoffset hrows hblank hsaved htmp hsource hloopSaved
  have hcost := hn h i u target width L hu htarget hw hwidth hL hguard hcell hprepare
    α gap C V bounds Fs hFs raw (plan bank hinj)
  refine ⟨v',m,outputs,huser,(Nat.cast_le.mpr htime).trans hcost,houtputs,?_⟩
  have hband : PhaseCellBand.width (Sizes.p n₀) u ≤ Sizes.s n₀ i := by
    have hsquare := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (PhaseCellBand.width (Sizes.p n₀) u)
    omega
  have hscalar := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hpacket := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hcontrol := hcontrolAt h i B width radius L W Fs.length hw hscalar hpacket hL
  have hprep := computedClassPreparationStock_le B (Sizes.s n₀ i) width radius L W Fs.length
  have hscaled := Nat.mul_le_mul_left 3 hcontrol
  have hpad : 3*(6*cW+9)*Fs.length*Sizes.t n₀ i*Sizes.p n₀ ≤
      3*(6*cW+9)*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀ := by
    have hh := Nat.mul_le_mul_left (3*(6*cW+9)*Fs.length*Sizes.t n₀ i*Sizes.p n₀)
      (show 1 ≤ Cprog+1 by omega)
    nlinarith only [hh]
  have hallow : (3*preparedCoreOriginsCost B (Sizes.s n₀ i) width radius L+
      2*recoveryPayloadCountCost Fs.length L W)+reserve ≤
      (42+3*Cprog)*Sizes.T n₀+(Cstock+3*(6*cW+9))*(Cprog+1)*Fs.length*Sizes.t n₀ i*Sizes.p n₀ := by
    dsimp only [reserve]
    nlinarith only [hprep,hscaled,hpad]
  exact hexec.mono (by intro d z hz; exact hz.trans (Nat.add_le_add_left hallow _))

end IntegerMultBounds.MathlibTM2.Cost
