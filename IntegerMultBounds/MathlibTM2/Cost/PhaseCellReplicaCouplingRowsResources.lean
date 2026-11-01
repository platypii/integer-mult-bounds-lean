module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInitializedReplicaCouplingRows
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRealReplicaResources

/-! Aligned RHS queue construction adds only linear native traffic to the real
interior pass. Every original RHS word is retained for subsequent recovery. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {s Q A : ℕ} {U : Type}

def initializedReplicaCouplingRowsTime (H : ReplicaHaloProblem s) :=
  realInitializedReplicaHaloTime H+reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)

noncomputable def initializedReplicaCouplingRowsLocalWorkspace (H : ReplicaHaloProblem s)
    (hQ : SS.states ≤ Q) (R K cV : ℕ) :=
  realInitializedReplicaHaloLocalWorkspace (A := A) (U := U) H hQ R K cV+
    2*reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth)

theorem selectedInitializedReplicaCouplingRows_fast_le (ct ce : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    let cV := (2*cw+426009)*cw
    ∃ D : ℝ, 0 ≤ D ∧ ∀ {n : ℕ} (_h : Sizes.Big n) (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)]
      (H : ReplicaHaloProblem (Sizes.s n i)), H.p = Sizes.p n → H.t = Sizes.t n i →
      H.l = haloInverseRingLog (Sizes.s n i) (Sizes.t n i) →
      H.u ≤ Sizes.p n → H.target ≤ ct*Sizes.p n → H.rhsExp ≤ ce*Sizes.p n →
      ∀ steps : ℕ, steps ≤ initializedReplicaCouplingRowsTime H →
      (steps : ℝ) ≤
        (initializedReplicaHaloSharedTime H+18+H.Fs.length*(38*(H.span*H.wordWidth)+37)+
          (10*cV+19)*H.Fs.length*((haloInterior
            (Sizes.s n i) H.t H.band H.origin (H.origin+H.span)).card*H.wordWidth) : ℕ)+
        D*H.Fs.length*(replicaHaloLocalCoordinates H : ℕ)*(H.p : ℝ)^(129/128 : ℝ) := by
  dsimp only
  obtain ⟨D,hD,hfast⟩ := selectedRealInitializedReplicaHalo_fast_le ct ce
  refine ⟨D,hD,?_⟩
  intro n h i _ H hp ht hl hu htarget hrhs steps hn
  have hc := hfast h i H hp ht hl hu htarget hrhs (realInitializedReplicaHaloTime H) (le_refl _)
  have hnR : (steps : ℝ) ≤ (realInitializedReplicaHaloTime H : ℝ)+
      reverseCopyRowsCost H.Fs.length (H.span*H.wordWidth) := by exact_mod_cast hn
  unfold reverseCopyRowsCost at hnR
  push_cast at hc hnR ⊢
  nlinarith only [hc,hnR]

end IntegerMultBounds.MathlibTM2.Cost
