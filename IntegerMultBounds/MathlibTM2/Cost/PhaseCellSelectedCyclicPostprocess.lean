module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicNormalizationSetup
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicPublicationTraffic
import Mathlib.Tactic.Linarith

/-! Full normalization, merge, crop and component assembly on a fitting class. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

def cyclicPostprocessTimeCost (p q W s a n leftSpan rightSpan radius core replicas fields : ℕ) : ℕ :=
  (PackedRecoveryNormalization.normalizationCost p q W a (min n (s-a)) replicas+
    PackedRecoveryNormalization.normalizationCost p q W 0 (n-min n (s-a)) replicas)+
  cyclicPublicationTrafficCost leftSpan rightSpan (2*q+8) W radius core n replicas fields

private theorem sum_pair {ι : Type} (jobs : List ι) (f g : ι → ℕ) :
    (jobs.map (fun k => f k+g k)).sum = (jobs.map f).sum+(jobs.map g).sum := by
  induction jobs with
  | nil => simp
  | cons k jobs ih => simp only [List.map_cons,List.sum_cons,ih]; omega

theorem selectedFittingCyclicPostprocess_time_le (cw cW : ℕ) :
    ∀ᶠ n : ℕ in atTop, ∀ (h : Sizes.Big n) (i : Fin (Sizes.d n))
      (width radius L replicas W : ℕ),
      0 < width → width ≤ Sizes.s n i → radius ≤ width →
      2*Sizes.p n+13 ≤ W → W ≤ cW*Sizes.p n →
      ∀ q leftSpan rightSpan fields : ℕ → ℕ,
      (∀ k ∈ coreGatherIndices (Sizes.s n i) width radius L,
        2*q k+8 ≤ cw*Sizes.p n ∧ leftSpan k+rightSpan k ≤ L ∧ fields k ≤ replicas) →
      ((coreGatherIndices (Sizes.s n i) width radius L).map (fun k =>
        cyclicPostprocessTimeCost (Sizes.p n) (q k) W (Sizes.s n i)
          (coreStart width k-radius) L (leftSpan k) (rightSpan k) radius
          (coreLength (Sizes.s n i) width k) replicas (fields k))).sum ≤
      Sizes.T n+7600*(replicas+1)*Sizes.s n i*(cw*Sizes.p n+W+1) := by
  filter_upwards [selectedCyclicNormalizationSetupSchedule_volume_le cw cW 1] with n hs
  intro h i width radius L replicas W hw hwidth hradius hW hWbound q leftSpan rightSpan fields hparams
  let jobs := coreGatherIndices (Sizes.s n i) width radius L
  have hq : ∀ k ∈ jobs, 2*q k+8 ≤ cw*Sizes.p n := fun k hk => (hparams k hk).1
  have hcount : jobs.length ≤ 2*Sizes.t n i := by
    have hc := coreGatherIndices_length_le (Sizes.s n i) width radius L hw
    have ht := h.good.lt i
    dsimp only [jobs]
    omega
  have hsetup := hs h i jobs q (fun k => coreStart width k-radius) (fun _ => L)
    W hcount hWbound (by
      intro k hk
      obtain ⟨hl,hr,hL⟩ := coreGatherIndices_spec (Sizes.s n i) width radius L k hk
      have ht := h.good.lt i
      exact ⟨hq k hk,by omega,by omega⟩)
  simp only [one_mul] at hsetup
  have hn := computedFittingCyclicNormalizationSchedule_le (Sizes.p n) W (Sizes.s n i)
    width radius L replicas cw hw hwidth hradius hW q hq
  have hp := computedFittingCyclicPublicationTraffic_sum_le (Sizes.s n i) width radius L
    (Sizes.p n) cw W replicas hw hwidth hradius leftSpan rightSpan (fun k => 2*q k+8)
    fields (by
      intro k hk
      obtain ⟨hq,hs,hf⟩ := hparams k hk
      exact ⟨hs,hq,hf⟩)
  have heq := sum_pair jobs
    (fun k => PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q k) W
      (coreStart width k-radius) (min L (Sizes.s n i-(coreStart width k-radius))) replicas+
      PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q k) W 0
        (L-min L (Sizes.s n i-(coreStart width k-radius))) replicas)
    (fun k => cyclicPublicationTrafficCost (leftSpan k) (rightSpan k) (2*q k+8) W radius
      (coreLength (Sizes.s n i) width k) L replicas (fields k))
  change _ ≤ _ at hn
  dsimp only [jobs] at hsetup heq
  change ((coreGatherIndices (Sizes.s n i) width radius L).map (fun k =>
    (PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q k) W (coreStart width k-radius)
      (min L (Sizes.s n i-(coreStart width k-radius))) replicas+
      PackedRecoveryNormalization.normalizationCost (Sizes.p n) (q k) W 0
        (L-min L (Sizes.s n i-(coreStart width k-radius))) replicas)+
    cyclicPublicationTrafficCost (leftSpan k) (rightSpan k) (2*q k+8) W radius
      (coreLength (Sizes.s n i) width k) L replicas (fields k))).sum ≤ _
  rw [heq]
  have hcost := Nat.add_le_add (hn.trans (Nat.add_le_add_right hsetup _)) hp
  have hmono := Nat.mul_le_mul_right (600*Sizes.s n i*(cw*Sizes.p n+W+1)) (Nat.le_add_right replicas 1)
  nlinarith only [hcost,hmono]

end IntegerMultBounds.MathlibTM2.Cost
