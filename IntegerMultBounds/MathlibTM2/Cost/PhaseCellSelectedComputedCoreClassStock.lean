module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreClassProfile
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedComputedCoreStock

/-! The actual proper-core family discharges the complete stock profiles.
A single derived sum supplies a reserve for every call in the class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedComputedCoreClassStock_sum_le {T Q A : ℕ} {U : Type}
    (b : RawRecoveryProgramBounds Q A U) (ct : ℕ) :
    ∃ Cstock : ℕ, ∀ᶠ n : ℕ in Filter.atTop, ∀ (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target width L : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hw : 0 < width) (hwidth : width ≤ Sizes.s n i)
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
    (v : HS 392 Q A U) (plan : ComputedRecoveryPlan T) (Cprog : ℕ),
    let indices := coreGatherIndices (Sizes.s n i) width
      (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
    let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A) (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) width indices[j.val]
      (V j) α gap C Fs (bounds j) hF
    let B := inverseCallerWordWidth (Sizes.p n) u (haloInverseRingLog (Sizes.s n i) (Sizes.t n i))
      target (Sizes.s n i) (Sizes.t n i)
    ((List.ofFn jobs).map (fun r => plan.coreStock b B r Cprog)).sum ≤
      (39+3*Cprog)*Sizes.T n+Cstock*(Cprog+1)*Fs.length*Sizes.t n i*Sizes.p n := by
  let cB := 2*(ct+21)+22
  let cH := 1032+8*ct
  let cw := 16*20+8*cH+8*2+128
  let cVratio := 2*cw+426009
  let cZ := cB+cH+ct+20
  obtain ⟨Cstock,hbound⟩ := selectedComputedCoreStock_sum_le b cZ cB cVratio 20 cw 20 (cVratio*cw) cH ct
    (by dsimp only [cZ,cB,cH]; omega)
  refine ⟨Cstock,?_⟩
  filter_upwards [hbound] with n hn
  intro h i _ u target width L hu htarget hw hwidth hguard hcell hprepare α gap C V bounds Fs hFs v plan Cprog
  dsimp only
  let indices := coreGatherIndices (Sizes.s n i) width
    (localityDepth (Sizes.p n) target*PhaseCellBand.width (Sizes.p n) u) L
  let jobs := fun j : Fin indices.length => PackedNormalizedJob.ofCoreCommon (A := A) (Sizes.p n) u
    (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) target (Sizes.t n i) width indices[j.val]
    (V j) α gap C Fs (bounds j) hFs
  have hprofile := selectedCoreClassComputed_profile (A := A) ct h i u target width L hu htarget hw hwidth
    hguard hcell hprepare α gap C V bounds Fs hFs
  dsimp only at hprofile
  obtain ⟨hcount,hparams,hN,hcoords,hspan,htargets,hvolume,hsetup⟩ := hprofile
  have hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i := by
    have hsquare := Nat.le_self_pow (by decide : (2 : ℕ) ≠ 0) (PhaseCellBand.width (Sizes.p n) u)
    omega
  have hB := selectedInverseCallerWordWidth_le ct h i hu htarget hband
  exact hn h i v plan _ (List.ofFn jobs) Fs.length Cprog
    hcount hparams hN hcoords hspan
    (fun r hr => (hsetup r hr).2) hB
    (fun r hr => congrArg List.length (hsetup r hr).1)

end IntegerMultBounds.MathlibTM2.Cost
