module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellAmortizedCoreGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGeneratedReplicaFactory
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCouplingSetup

/-! Sum polynomial setup over distinct cores before absorbing it into volume.
The generic list estimate also applies to filtered or grouped core schedules. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

private theorem sum_map_le_length_mul {α : Type} (records : List α) (cost : α → ℕ) (B : ℕ)
    (h : ∀ r ∈ records, cost r ≤ B) : (records.map cost).sum ≤ records.length*B := by
  induction records with
  | nil => simp
  | cons r records ih =>
    have hr := h r (by simp)
    have hs := ih (by intro x hx; exact h x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,List.length_cons]
    nlinarith only [hr,hs]

/-- One shared volume reserve pays all polynomial setup calls in an axis
schedule. The number of replicas does not enter this setup bill. -/
theorem selectedDistinctCoreSetup_volume_le (C pExp tExp scale : ℕ) {α : Type} :
    ∀ᶠ n : ℕ in atTop, ∀ (i : Fin (Sizes.d n)) (records : List α) (cost : α → ℕ),
      records.length ≤ 2*Sizes.t n i →
      (∀ r ∈ records, cost r ≤ C*Sizes.t n i^tExp*Sizes.p n^pExp) →
      scale*(records.map cost).sum ≤ Sizes.T n := by
  filter_upwards [selectedAxisPolynomial_le_volume (2*scale*C) pExp (tExp+1)] with n hv
  intro i records cost hcount hcost
  have hs := sum_map_le_length_mul records cost _ hcost
  have hcount' := hcount
  calc
    scale*(records.map cost).sum ≤ scale*(records.length*(C*Sizes.t n i^tExp*Sizes.p n^pExp)) :=
      Nat.mul_le_mul_left _ hs
    _ ≤ scale*((2*Sizes.t n i)*(C*Sizes.t n i^tExp*Sizes.p n^pExp)) :=
      Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ hcount')
    _ = (2*scale*C)*Sizes.t n i^(tExp+1)*Sizes.p n^pExp := by rw [pow_succ]; ring
    _ ≤ Sizes.T n := hv i

/-- The actual ordinary-header factor factory is paid once for every core,
including the short final core, with one total setup-volume allowance. -/
theorem selectedCoreFactorySchedule_volume_le (ct scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (width : ℕ) (H : ℕ → ReplicaHaloProblem (Sizes.s n i)) (target : ℕ → ℕ),
      0 < width → width ≤ Sizes.s n i →
      (∀ k ∈ coreIndices (Sizes.s n i) width,
        (H k).p = Sizes.p n ∧ (H k).t = Sizes.t n i ∧
        (H k).l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) ∧
        (H k).u ≤ Sizes.p n ∧ target k ≤ ct*Sizes.p n ∧ (H k).rhsExp = 2 ∧
        (H k).target = boundaryHaloTarget (H k).p (H k).u (boundaryRecoveryTarget (H k).p (target k+1)) (H k).rhsExp
          (haloBoundary (Sizes.s n i) (H k).t (H k).band (H k).origin ((H k).origin+(H k).span)).card) →
      scale*((coreIndices (Sizes.s n i) width).map
        (fun k => generatedReplicaBoundaryFactoryCost (H k) (target k+1))).sum ≤ Sizes.T n := by
  obtain ⟨C,hfactory⟩ := selectedGeneratedReplicaBoundaryFactoryCost_poly_le ct
  filter_upwards [hfactory,selectedDistinctCoreSetup_volume_le C 4 6 scale] with n hf hs
  intro h i _ width H target hw hwidth hparams
  apply hs i (coreIndices (Sizes.s n i) width)
    (fun k => generatedReplicaBoundaryFactoryCost (H k) (target k+1))
  · have hslots := coreSlots_le_two (Sizes.s n i) width hwidth
    have hlen := Nat.le_mul_of_pos_right (coreIndices (Sizes.s n i) width).length hw
    have hst := h.good.lt i
    omega
  · intro k hk
    obtain ⟨hp,ht,hl,hu,htarget,hrhs,hsetup⟩ := hparams k hk
    exact hf h i (H k) (target k) hp ht hl hu htarget hrhs hsetup

/-- Header, coefficient, mask and retirement setup is also shared over the
complete core schedule; replicas never multiply this setup charge. -/
theorem selectedCoreCachedCouplingSchedule_volume_le (cw cV scale : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (width : ℕ) (H : ℕ → ReplicaHaloProblem (Sizes.s n i)),
      0 < width → width ≤ Sizes.s n i →
      (∀ k ∈ coreIndices (Sizes.s n i) width,
        (H k).p = Sizes.p n ∧ (H k).t = Sizes.t n i ∧
        (H k).wordWidth ≤ cw*(H k).p ∧ (H k).u ≤ (H k).p ∧ (H k).metadataWidth ≤ cV*(H k).p) →
      scale*((coreIndices (Sizes.s n i) width).map
        (fun k => cachedReplicaCouplingSharedTime (H k))).sum ≤ Sizes.T n := by
  let C := 20000000*(2*cw+cV+500000)^5
  filter_upwards [selectedDistinctCoreSetup_volume_le C 5 5 scale] with n hs
  intro h i _ width H hw hwidth hparams
  apply hs i (coreIndices (Sizes.s n i) width) (fun k => cachedReplicaCouplingSharedTime (H k))
  · have hslots := coreSlots_le_two (Sizes.s n i) width hwidth
    have hlen := Nat.le_mul_of_pos_right (coreIndices (Sizes.s n i) width).length hw
    have hst := h.good.lt i
    omega
  · intro k hk
    obtain ⟨hp,ht,hw,hu,hV⟩ := hparams k hk
    have hc := selectedCachedReplicaCouplingSharedTime_poly_le cw cV h i (H k) hp ht hw hu hV
    apply hc.trans_eq
    rw [hp,ht]
    dsimp only [C]
    ring

end IntegerMultBounds.MathlibTM2.Cost
