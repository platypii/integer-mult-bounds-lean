module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellReplicaRecoveryInteriorFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRecoveryLocalVolume
import Mathlib.Tactic.Linarith

/-! A second interior with the same layout uses the same local-volume ledger
as the first pass, independently of its RHS and joint accuracy target. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem replicaRecoveryInterior_layout_local_fast_le (cl cw cr cV : ℕ) :
    ∃ F : ℝ, 0 ≤ F ∧ ∀ {s : ℕ} [NeZero s] (H J : ReplicaHaloProblem s),
      H.SameLayout J → H.l ≤ cl*H.p → H.wordWidth ≤ cw*H.p →
      2^H.l ≤ cr*H.p → H.metadataWidth ≤ cV*H.p →
      H.t-s ≤ s → H.l = haloInverseRingLog s H.t →
      (replicaRecoveryInteriorTime H J : ℝ) ≤
        (initializedReplicaHaloSharedTime J+18 : ℕ)+
        F*H.Fs.length*(replicaRecoveryLocalVolume H : ℝ)*(H.p : ℝ)^(129/128 : ℝ) := by
  obtain ⟨D,hD,hfast⟩ := replicaRecoveryInterior_layout_fast_le cl cw cr cV
  let K := (10*cV+57)*cw+37
  refine ⟨D+K,by positivity,?_⟩
  intro s _ H J layout hl hw hr hV hgap hring
  have hh := hfast H J layout hl hw hr hV hgap hring
  let G := replicaRecoveryLocalVolume H
  obtain ⟨_,hrows,_,_⟩ := replicaRecoveryLocalVolume_bounds H
  have hspan : H.span ≤ G := by dsimp only [G]; omega
  have hcard : (haloInterior s H.t H.band H.origin (H.origin+H.span)).card ≤ G := by
    unfold G replicaRecoveryLocalVolume replicaHaloLocalCoordinates
    omega
  have hG : 1 ≤ G := by dsimp only [G]; omega
  have hGp : 1 ≤ G*H.p := Nat.mul_pos hG H.p_pos
  have hsw := Nat.mul_le_mul hspan hw
  have hcw := Nat.mul_le_mul hcard hw
  have hn : 38*(H.span*H.wordWidth)+37+
      (10*cV+19)*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) ≤ K*G*H.p := by
    dsimp only [K]
    nlinarith only [hsw,hGp,Nat.mul_le_mul_left (10*cV+19) hcw]
  have hnR : ((H.Fs.length*(38*(H.span*H.wordWidth)+37)+
      (10*cV+19)*H.Fs.length*((haloInterior s H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ) : ℝ) ≤
      ((K*H.Fs.length*G*H.p : ℕ) : ℝ) := by
    exact_mod_cast (by nlinarith only [Nat.mul_le_mul_left H.Fs.length hn] : _ ≤ K*H.Fs.length*G*H.p)
  have hp1 : (1 : ℝ) ≤ H.p := by exact_mod_cast H.p_pos
  have hpow := mul_le_mul_of_nonneg_left
    (Real.self_le_rpow_of_one_le hp1 (by norm_num : (1 : ℝ) ≤ 129/128))
    (by positivity : (0 : ℝ) ≤ (K : ℝ)*H.Fs.length*G)
  have hcoords : (replicaHaloLocalCoordinates H : ℝ) ≤ G := by
    have hc : replicaHaloLocalCoordinates H ≤ G := by unfold G replicaRecoveryLocalVolume; omega
    exact_mod_cast hc
  have hd := mul_le_mul_of_nonneg_left hcoords
    (by positivity : (0 : ℝ) ≤ D*H.Fs.length*(H.p : ℝ)^(129/128 : ℝ))
  dsimp only [G] at hnR hpow hd
  push_cast at hh hnR hpow hd ⊢
  nlinarith only [hh,hnR,hpow,hd]

end IntegerMultBounds.MathlibTM2.Cost
