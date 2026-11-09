module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPreparedResidualBatchFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicPreparedVolume
import Mathlib.Tactic.Linarith

/-! Price the actual prepared batches over one computed fitting class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.NLogN.PhaseCellMatrix

private theorem batch_controls_le (cw p w N replicas : ℕ) (hp : 1 ≤ p) (hw : w ≤ cw*p) :
    N*(6*w+9)+16+replicas*(22*N*w+25) ≤
      (30*cw+50)*(replicas+1)*(N+1)*p := by
  have hN := Nat.mul_le_mul_left N hw
  have hr := Nat.mul_le_mul_left replicas hN
  have hNp := Nat.mul_le_mul_left N hp
  have hrp := Nat.mul_le_mul_left replicas hp
  have hNr := Nat.mul_le_mul_left replicas hNp
  ring_nf at hN hr hNp hrp hNr ⊢
  omega

private theorem sum_batch_le {ι : Type} (jobs : List ι) (cost volume : ι → ℕ)
    (K : ℝ) (hcost : ∀ j ∈ jobs, (cost j : ℝ) ≤ K*(volume j : ℝ)) :
    ((jobs.map cost).sum : ℝ) ≤ K*((jobs.map volume).sum : ℝ) := by
  induction jobs with
  | nil => simp
  | cons j jobs ih =>
    have hj := hcost j (by simp)
    have hs := ih (by intro x hx; exact hcost x (by simp [hx]))
    simp only [List.map_cons,List.sum_cons,Nat.cast_add]
    nlinarith only [hj,hs]

theorem computedFittingCyclicPreparedSchedule_fast_le (cw : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ {s t : ℕ} [NeZero s], s < t →
      ∀ p width band depth L replicas : ℕ, 1 ≤ p → 0 < width → width ≤ s →
      depth*band ≤ width → 1 ≤ band → band^2 ≤ width →
      ∀ q : ℕ → ℕ,
      (∀ k ∈ coreGatherIndices s width (depth*band) L, 2*q k+8 ≤ cw*p) →
      (((coreGatherIndices s width (depth*band) L).map (fun k =>
        preparedResidualBatchCost (q k) (2*q k+8)
          (cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L).card
          (24*band+1) replicas)).sum : ℝ) ≤
      800*((30*cw+50 : ℕ)*(replicas+1)*(p : ℝ)+
        replicas*C*(p : ℝ)^(129/128 : ℝ))*((s+(t-s)*band^2 : ℕ) : ℝ) := by
  obtain ⟨C,hC,hfast⟩ := preparedResidualBatch_fast_le cw
  refine ⟨C,hC,?_⟩
  intro s t _ hst p width band depth L replicas hp hw hwidth hguard hband hprepare q hq
  let jobs := coreGatherIndices s width (depth*band) L
  let volume := fun k => ((cyclicPrincipalBoundary s t band
    (coreStart width k-depth*band) L).card+1)*(24*band+1)
  let K : ℝ := (30*cw+50 : ℕ)*(replicas+1)*(p : ℝ)+replicas*C*(p : ℝ)^(129/128 : ℝ)
  have hs := sum_batch_le jobs (fun k => preparedResidualBatchCost (q k) (2*q k+8)
    (cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L).card
    (24*band+1) replicas) volume K (by
      intro k hk
      let N := (cyclicPrincipalBoundary s t band (coreStart width k-depth*band) L).card
      have hf := hfast p (q k) N (24*band+1) replicas hp (hq k hk) (by omega)
      have hc := (Nat.cast_le (α := ℝ)).mpr
        (batch_controls_le cw p (2*q k+8) N replicas hp (hq k hk))
      have hW : (1 : ℝ) ≤ (24*band+1 : ℕ) := by exact_mod_cast (show 1 ≤ 24*band+1 by omega)
      have hm := mul_le_mul_of_nonneg_left hW
        (by positivity : (0 : ℝ) ≤ ((30*cw+50 : ℕ) : ℝ)*(replicas+1)*(N+1)*(p : ℝ))
      dsimp only [volume,K]
      change (preparedResidualBatchCost _ _ N _ _ : ℝ) ≤ _
      push_cast at hf hc hm ⊢
      nlinarith only [hf,hc,hm])
  have hv := (Nat.cast_le (α := ℝ)).mpr
    (computedFittingCyclicPreparedVolume_sum_le hst width band depth L hw hwidth hguard hband hprepare)
  have hK : 0 ≤ K := by dsimp only [K]; positivity
  have hm := mul_le_mul_of_nonneg_left hv hK
  dsimp only [jobs,volume,K] at hs hm
  push_cast at hs hm ⊢
  nlinarith only [hs,hm]

end IntegerMultBounds.MathlibTM2.Cost
