module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellInitializedReplicaFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock

/-! Selected precision and dimensions discharge every fast-time width premise
for the initialized packed interior pass. Shared factories stay explicit. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedInitializedReplicaHalo_fast_le (ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := (2*cw+426009)*cw
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ initializedReplicaHaloTime H →
      (steps : ℝ) ≤
        (initializedReplicaHaloSharedTime H+H.Fs.length*(10*(H.span*H.wordWidth)+9)+
          (10*cV+19)*H.Fs.length*((haloInterior
            (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  let cV := (2*cw+426009)*cw
  obtain ⟨D,hD,hfast⟩ := initializedReplicaHalo_fast_le 20 cw 20 cV
  refine ⟨D,hD,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hn
  obtain ⟨hl',hr,hw,hV⟩ := selectedHaloGatheredWidths ct ce h i H.u H.target H.rhsExp hu htarget hrhs
  have hlH : H.l ≤ 20*H.p := by simpa only [hl,hp] using hl'
  have hrH : 2^H.l ≤ 20*H.p := by simpa only [hl,hp] using hr
  have hwH : H.wordWidth ≤ cw*H.p := by
    simpa only [ReplicaHaloProblem.wordWidth,hl,hp,cw] using hw
  have hVw : H.metadataWidth ≤ (2*cw+426009)*H.wordWidth := by
    simpa only [ReplicaHaloProblem.metadataWidth,ReplicaHaloProblem.precision,ReplicaHaloProblem.wordWidth,hp,ht,hl,cw] using hV
  have hVp : H.metadataWidth ≤ cV*H.p := by
    calc
      _ ≤ (2*cw+426009)*H.wordWidth := hVw
      _ ≤ (2*cw+426009)*(cw*H.p) := Nat.mul_le_mul_left _ hwH
      _ = cV*H.p := by dsimp only [cV]; ring
  have hg : H.t-Sizes.s n i ≤ Sizes.s n i := by rw [ht]; exact selectedAxis_gap_le_source h i
  have hlRing : H.l = haloInverseRingLog (Sizes.s n i) H.t := by rw [ht]; exact hl
  have hc := hfast H hlH hwH hrH hVp hg hlRing
  have hnR : (steps : ℝ) ≤ initializedReplicaHaloTime H := by exact_mod_cast hn
  exact hnR.trans hc

end IntegerMultBounds.MathlibTM2.Cost
