module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellRealReplicaHaloOutput
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInitializedReplicaFast
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInitializedReplicaStock

/-! Paid real projection adds only native rectangular traffic to the initialized
pass. The fast exponent and shared-factory accounting are unchanged. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} {U : Type}

def realInitializedReplicaHaloTime (H : ReplicaHaloProblem s) :=
  initializedReplicaHaloTime H+realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

noncomputable def realInitializedReplicaHaloLocalWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ) :=
  initializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K cV+
    2*realReplicaRowsCost H.Fs.length (H.span*H.wordWidth)

theorem selectedRealInitializedReplicaHalo_fast_le (ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := (2*cw+426009)*cw
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ realInitializedReplicaHaloTime H →
      (steps : ℝ) ≤
        (initializedReplicaHaloSharedTime H+12+H.Fs.length*(22*(H.span*H.wordWidth)+18)+
          (10*cV+19)*H.Fs.length*((haloInterior
            (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  obtain ⟨D,hD,hfast⟩ := selectedInitializedReplicaHalo_fast_le ct ce
  refine ⟨D,hD,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hn
  have hc := hfast h i H hp ht hl hu htarget hrhs (initializedReplicaHaloTime H) (le_refl _)
  have hnR : (steps : ℝ) ≤ (initializedReplicaHaloTime H : ℝ)+
      realReplicaRowsCost H.Fs.length (H.span*H.wordWidth) := by exact_mod_cast hn
  unfold realReplicaRowsCost at hnR
  push_cast at hc hnR ⊢
  nlinarith only [hc,hnR]

end IntegerMultBounds.MathlibTM2.Cost
