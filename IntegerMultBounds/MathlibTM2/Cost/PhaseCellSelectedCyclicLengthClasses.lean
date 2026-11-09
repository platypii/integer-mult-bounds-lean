module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedActualFittingCyclicComplexCore
import Mathlib.Tactic.Linarith

/-! The actual two fitting length classes reuse the complete selected step
estimate; shared setup is counted once for each class that executes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_classes_le {ι : Type} (classes : List ι) (steps : ι → ℕ) (B : ℝ)
    (h : ∀ L ∈ classes, (steps L : ℝ) ≤ B) :
    ((classes.map steps).sum : ℝ) ≤ classes.length*B := by
  induction classes with
  | nil => simp
  | cons L classes ih =>
    have hL := h L (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.cast_add,Nat.cast_one]
    nlinarith only [hL,hs]

theorem selectedActualFittingCyclicLengthClasses_time_le (ct cW : ℕ) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n)
      (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] {u : ℕ} {α d : ℝ},
      ∀ axis : RecoveryAxisBounds (Sizes.s n i) (Sizes.t n i) (Sizes.p n) u
        (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) α d,
      ∀ width depth replicas target W : ℕ,
      u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      let p := Sizes.p n
      let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
      let band := PhaseCellBand.width p u
      let classes := coreGatherLengths (Sizes.s n i) width (depth*band)
      let origin := fun k => coreStart width k-depth*band
      let N := fun L k => (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i) band (origin k) L).card
      let stage := fun L k => initialSchurTarget p u
        (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 (N L k)) 2
      let q := fun L k => executionPrecision p l (stage L k) 2
      0 < width → width ≤ Sizes.s n i → depth*band ≤ width →
      Sizes.s n i/(Sizes.t n i-Sizes.s n i)+1 ≤ width → p^2+band^2 ≤ width →
      ∀ H K J M : ℕ → ℕ → ReplicaHaloProblem (Sizes.s n i),
      (∀ L ∈ classes, ∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        ∃ (ha : origin k < Sizes.s n i) (hn : L ≤ Sizes.s n i)
          (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
          (hF : ∀ F ∈ Fs, ∀ j, ‖value (q L k) (F j)‖ ≤ (2 : ℝ)^2),
          Fs.length = replicas ∧
          H L k = axis.cyclicLeftReplicaProblem (stage L k) 2 (origin k) L ha Fs hF ∧
          K L k = axis.cyclicRightReplicaProblem (stage L k) 2 (origin k) L hn Fs hF) →
      (∀ L ∈ classes, ∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        CyclicSecondInteriorProfile (H L k) (K L k) (J L k) (M L k) p
          (boundaryRecoveryTarget p (target+1)) (N L k)) →
      2*p+13 ≤ W → W ≤ cW*p → ∀ fields steps : ℕ → ℕ → ℕ,
      (∀ L ∈ classes, ∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L, fields L k ≤ replicas) →
      (∀ L ∈ classes, ∀ k ∈ coreGatherIndices (Sizes.s n i) width (depth*band) L,
        steps L k ≤ cyclicComplexCoreTimeCost (H L k) (K L k) p u l (Sizes.t n i)
          (origin k) L target (q L k) W (depth*band) (coreLength (Sizes.s n i) width k)
          replicas (fields L k)) →
      ((classes.map (fun L => ((coreGatherIndices (Sizes.s n i) width (depth*band) L).map (steps L)).sum)).sum : ℝ) ≤
      10*(Sizes.T n : ℝ)+2*A*(replicas+1)*
        ((Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n))*(Sizes.p n : ℝ)^(129/128 : ℝ) := by
  obtain ⟨A,hA,hbase⟩ := selectedActualFittingCyclicComplexCore_time_le ct cW
  refine ⟨A,hA,?_⟩
  filter_upwards [hbase] with n hb
  intro h i _ u α d axis width depth replicas target W hu htarget
  dsimp only
  intro hw hwidth hguard hcell hprepare H K J M hactual hprofile hW hWbound fields steps hfields hsteps
  let band := PhaseCellBand.width (Sizes.p n) u
  let classes := coreGatherLengths (Sizes.s n i) width (depth*band)
  let B : ℝ := 5*(Sizes.T n : ℝ)+A*(replicas+1)*
    ((Sizes.t n i : ℝ)*(1+(band : ℝ)^2/Sizes.d n))*(Sizes.p n : ℝ)^(129/128 : ℝ)
  have hs := sum_classes_le classes
    (fun L => ((coreGatherIndices (Sizes.s n i) width (depth*band) L).map (steps L)).sum) B (by
      intro L hL
      exact hb h i axis width depth L replicas target W hu htarget hw hwidth hguard hcell hprepare
        (H L) (K L) (J L) (M L) (hactual L hL) (hprofile L hL) hW hWbound
        (fields L) (hfields L hL) (steps L) (hsteps L hL))
  have hc : (classes.length : ℝ) ≤ 2 := by
    exact_mod_cast coreGatherLengths_length (Sizes.s n i) width (depth*band)
  have hB : 0 ≤ B := by dsimp only [B]; positivity
  have hm := mul_le_mul_of_nonneg_right hc hB
  dsimp only [classes,B,band] at hs hm
  push_cast at hs hm ⊢
  nlinarith only [hs,hm]

end IntegerMultBounds.MathlibTM2.Cost
