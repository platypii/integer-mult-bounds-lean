module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellFittingCyclicInputLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellDistinctCoreSetup
public import IntegerMultBounds.NLogN.PhaseCellCoreGatherVolume

/-! Ordinary input setup is paid at its actual core-call frequency. Conversion
traffic is charged by summed local spans, never by a whole axis per core. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem fittingCyclicInputScheduleTime_le {ι : Type} {s T A : ℕ} [NeZero s]
    (jobs : List ι) (ports : CyclicComplexCallerLayout T)
    (H K : ι → ReplicaHaloProblem s) (S : ι → Stacks T A) (p W N cw cW : ℕ)
    (hW : W ≤ cW*p)
    (hparams : ∀ j ∈ jobs, (H j).p = p ∧ (K j).p = p ∧
      (H j).wordWidth ≤ cw*p ∧ (K j).wordWidth ≤ cw*p)
    (hcount : ∀ j ∈ jobs, (H j).Fs.length = 2*N ∧ (K j).Fs.length = 2*N)
    (hheaders : ∀ j ∈ jobs,
      (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedL k)).length = recoverySeedHeader (H j) W N k) ∧
      (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedR k)).length = recoverySeedHeader (K j) W N k)) :
    (jobs.map (fun j => ports.inputTimeCost (H j) (K j) W N (S j))).sum ≤
      (jobs.map (fun j => fittingCyclicInputSharedTime (H j) (K j) W)).sum+
        (32*cW+2*(4*cW+12*cw+28)+70)*N*
          (jobs.map (fun j => (H j).span+(K j).span+1)).sum*p := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hs := ih (by intro k hk; exact hparams k (by simp [hk]))
      (by intro k hk; exact hcount k (by simp [hk]))
      (by intro k hk; exact hheaders k (by simp [hk]))
    obtain ⟨hpH,hpK,hwH,hwK⟩ := hparams j (by simp)
    obtain ⟨hN,hN'⟩ := hcount j (by simp)
    obtain ⟨hleft,hright⟩ := hheaders j (by simp)
    have hrow := fittingCyclicInputRowTime_le (H j) (K j) W cw cW (hpK.trans hpH.symm)
      (by simpa only [hpH] using hwH) (by simpa only [hpK] using hwK)
      (by simpa only [hpH] using hW)
    rw [hpH] at hrow
    have htraffic := Nat.mul_le_mul_left N hrow
    simp only [List.map_cons,List.sum_cons]
    rw [fittingCyclicInputTime_affine ports (H j) (K j) W N (S j) hN hN' hleft hright]
    nlinarith only [hs,htraffic]

/-- One shared allowance covers every actual preparation call in the axis
schedule, independently of replica count. -/
theorem selectedFittingCyclicInputSharedSchedule_le (cw cW scale : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (jobs : List ι) (H K : ι → ReplicaHaloProblem (Sizes.s m i)) (W : ℕ),
      jobs.length ≤ 2*Sizes.t m i → W ≤ cW*Sizes.p m →
      (∀ j ∈ jobs, ∀ D ∈ [H j,K j], D.p = Sizes.p m ∧ D.t = Sizes.t m i ∧
        D.l ≤ 20*Sizes.p m ∧ D.u ≤ Sizes.p m ∧ D.wordWidth ≤ cw*Sizes.p m) →
      scale*(jobs.map (fun j => fittingCyclicInputSharedTime (H j) (K j) W)).sum ≤ Sizes.T m := by
  filter_upwards [selectedDistinctCoreSetup_volume_le (2000006*(cw+cW+21)^2) 2 2 scale] with m hsetup
  intro ι h i _ jobs H K W hcount hW hparams
  apply hsetup i jobs (fun j => fittingCyclicInputSharedTime (H j) (K j) W) hcount
  intro j hj
  apply fittingCyclicInputSharedTime_axis (H j) (K j) W (Sizes.p m) (Sizes.t m i) cw cW
    (h.good.lt i) (by have := h.thirteen_le_p; omega) hW
  exact hparams j hj

/-- Fixed row overhead is also local: the whole fitting class has at most
seven axis lengths of input coordinates, including empty-piece overhead. -/
theorem fittingCyclicInputCoordinates_sum_le {s : ℕ} (width radius L : ℕ)
    (H K : ℕ → ReplicaHaloProblem s) (hw : 0 < width) (hwidth : width ≤ s) (hradius : radius ≤ width)
    (hspan : ∀ j ∈ coreGatherIndices s width radius L, (H j).span+(K j).span ≤ L) :
    ((coreGatherIndices s width radius L).map (fun j => (H j).span+(K j).span+1)).sum ≤ 7*s := by
  let jobs := coreGatherIndices s width radius L
  have hs := List.sum_le_length_nsmul (jobs.map (fun j => (H j).span+(K j).span+1)) (L+1) (by
    intro x hx
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hx
    have := hspan j hj
    omega)
  simp only [List.length_map, nsmul_eq_mul] at hs
  have hv := coreGather_volume_le_six s width radius L hwidth hradius
  have hc := coreGatherIndices_length_le s width radius L hw
  dsimp only [jobs] at hs
  nlinarith only [hs,hv,hc]

/-- Complete ordinary input time over a real job list. Shared setup is summed
before absorption, and the replica term uses the summed local coordinates. -/
theorem selectedFittingCyclicInputScheduleTime_le {T A : ℕ} (cw cW : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ {ι : Type} (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)]
      (jobs : List ι) (ports : CyclicComplexCallerLayout T)
      (H K : ι → ReplicaHaloProblem (Sizes.s m i)) (S : ι → Stacks T A) (W N volume : ℕ),
      jobs.length ≤ 2*Sizes.t m i → W ≤ cW*Sizes.p m →
      (∀ j ∈ jobs, ∀ D ∈ [H j,K j], D.p = Sizes.p m ∧ D.t = Sizes.t m i ∧
        D.l ≤ 20*Sizes.p m ∧ D.u ≤ Sizes.p m ∧ D.wordWidth ≤ cw*Sizes.p m) →
      (∀ j ∈ jobs, (H j).Fs.length = 2*N ∧ (K j).Fs.length = 2*N) →
      (∀ j ∈ jobs,
        (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedL k)).length = recoverySeedHeader (H j) W N k) ∧
        (∀ k ∈ recoverySeedHeaderPorts, ((S j).R (ports.seedR k)).length = recoverySeedHeader (K j) W N k)) →
      (jobs.map (fun j => (H j).span+(K j).span+1)).sum ≤ volume →
      (jobs.map (fun j => ports.inputTimeCost (H j) (K j) W N (S j))).sum ≤ Sizes.T m+
        (32*cW+2*(4*cW+12*cw+28)+70)*N*volume*Sizes.p m := by
  filter_upwards [selectedFittingCyclicInputSharedSchedule_le cw cW 1] with m hsetup
  intro ι h i _ jobs ports H K S W N volume hlen hW hparams hcount hheaders hvolume
  have hs := hsetup h i jobs H K W hlen hW hparams
  simp only [one_mul] at hs
  have hlocal := fittingCyclicInputScheduleTime_le jobs ports H K S (Sizes.p m) W N cw cW hW (by
    intro j hj
    have hH := hparams j hj (H j) (by simp)
    have hK := hparams j hj (K j) (by simp)
    exact ⟨hH.1,hK.1,hH.2.2.2.2,hK.2.2.2.2⟩) hcount hheaders
  have hv := Nat.mul_le_mul_right (Sizes.p m)
    (Nat.mul_le_mul_left ((32*cW+2*(4*cW+12*cw+28)+70)*N) hvolume)
  omega

end IntegerMultBounds.MathlibTM2.Cost
