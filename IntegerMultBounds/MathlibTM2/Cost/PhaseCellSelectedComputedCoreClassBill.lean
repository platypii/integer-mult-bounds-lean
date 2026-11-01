module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassTime
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellComputedCoreClassControl

/-! The complete executed class bill includes generated origins/counts,
actual computed core calls, scan overhead and final counter retirement. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedComputedCoreClassBill_time_le {T Q A : ℕ} {U : Type}
    (b : RawRecoveryProgramBounds Q A U) (ct : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ᶠ n : ℕ in Filter.atTop, ∀ (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target width L : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hw : 0 < width) (hwidth : width ≤ Sizes.s n i) (hL : L ≤ Sizes.s n i)
    (hguard : localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u ≤ width)
    (hcell : Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width)
    (hprepare : (Sizes.p n)^2+(PhaseCellBand.width (Sizes.p n) u)^2 ≤ width)
    (α gap : ℝ) (C : ZMod (Sizes.s n i) → GaussianInt)
    (V : Fin (coreGatherIndices (Sizes.s n i) width
      (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L).length → ℕ)
    (bounds : ∀ j, let k := (coreGatherIndices (Sizes.s n i) width
        (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L)[j.val]
      PackedHaloParameterBounds (p := Sizes.p n)
        (l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) (t := Sizes.t n i)
        (u := u) (target := target+1) (rhsExp := 2)
        (a := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).1)
        (b := (coreHaloEndpoints (Sizes.s n i) width k (PhaseCellBand.width (Sizes.p n) u)
          (localityDepth (Sizes.p n) target)).2) (V := V j) α gap C)
    (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
    (hF : ∀ F ∈ Fs, ∀ j, ‖value (Sizes.p n) (F j)‖ ≤ 1)
    (v : HS 392 Q A U) (plan : ComputedRecoveryPlan T),
    let indices := coreGatherIndices (Sizes.s n i) width
      (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A) (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) width indices[j.val]
      (V j) α gap C Fs (bounds j) hF
    let B := inverseCallerWordWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      target (Sizes.s n i) (Sizes.t n i)
    let W := packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      (Sizes.s n i) u (target+1) 2
    let radius := localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u
    (((preparedCoreOriginsCost B (Sizes.s n i) width radius L+recoveryPayloadCountCost Fs.length L W)+
      (((List.ofFn jobs).map (plan.coreTimeCost b B)).sum+5*(List.ofFn jobs).length+4)+
      (2*((List.ofFn jobs).length+Fs.length*(L*W))+5) : ℕ) : ℝ) ≤
      7*Sizes.T n+F*Fs.length*(Sizes.t n i : ℝ)*(1+(PhaseCellBand.width (Sizes.p n) u : ℝ)^2/Sizes.d n)*
        (Sizes.p n : ℝ)^(129/128 : ℝ) := by
  let cB := 2*(ct+21)+22
  let cW := 1032+8*ct
  obtain ⟨F,hF,hcore⟩ := selectedComputedCoreClass_time_le (T := T) b ct
  refine ⟨F+(6*cW+9 : ℕ),by positivity,?_⟩
  filter_upwards [hcore,selectedComputedClassControlTime_le cB cW] with n hn hc
  intro h i _ u target width L hu htarget hw hwidth hL hguard hcell hprepare α gap C V bounds Fs hFs v plan
  dsimp only
  let B := inverseCallerWordWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    target (Sizes.s n i) (Sizes.t n i)
  let W := packedHaloCommonWidth (Sizes.p n) (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
    (Sizes.s n i) u (target+1) 2
  let radius := localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u
  have htime := hn h i u target width L hu htarget hw hwidth hguard hcell hprepare α gap C V bounds Fs hFs v plan
  have hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
    have hsquare := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (PhaseCellBand.width (Sizes.p n) u)
    omega
  have hB := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  have hW := selectedPackedHaloCommonWidth_le ct h i u target htarget hband
  have hcontrol := hc h i B width radius L W Fs.length (PhaseCellBand.width (Sizes.p n) u) hw hB hW hL
  simp only [List.length_ofFn]
  rw [computedClassTimeBill_eq]
  push_cast at htime hcontrol ⊢
  nlinarith only [htime,hcontrol]

end IntegerMultBounds.MathlibTM2.Cost
