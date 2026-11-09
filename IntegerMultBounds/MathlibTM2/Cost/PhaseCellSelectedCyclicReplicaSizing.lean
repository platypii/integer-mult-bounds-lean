module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicWorkingWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems

/-! Discharge the actual joint cyclic replica target and metadata dimensions.
The two physical intervals retain the same joint boundary precision. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult.ShortConv IntegerMultBounds.NLogN IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem selectedCyclicReplicaSizing (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a span : ℕ)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    let p := Sizes.p n
    let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
    let N := (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width p u) a span).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    let stage := initialSchurTarget p u bits 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    let cw := 1032+8*ct
    let cwide := 16*20+8*cw+8*2+128
    l ≤ 20*p ∧ 2^l ≤ 20*p ∧ stage ≤ cw*p ∧ w ≤ cw*p ∧
      weightWorkspaceWidth (2^15*p) q w (Sizes.t n i) u ≤ (2*cwide+426009)*cw*p := by
  dsimp only
  let p := Sizes.p n
  let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
  let N := (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i)
    (PhaseCellBand.width p u) a span).card
  let stage := initialSchurTarget p u
    (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N) 2
  let cw := 1032+8*ct
  let cwide := 16*20+8*cw+8*2+128
  have hw : executionWidth p l stage 2 ≤ cw*p :=
    selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have hstage : stage ≤ cw*p := by
    have hj : stage ≤ executionWidth p l stage 2 := by
      unfold executionWidth executionExponent inputExponent sourceExponent
      omega
    exact hj.trans hw
  have hp : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have he : 2 ≤ 2*p := by omega
  obtain ⟨hl,hr,_,hV⟩ := selectedHaloGatheredWidths cw 2 h i u stage 2 hu hstage he
  refine ⟨hl,hr,hstage,hw,?_⟩
  calc
    _ ≤ (2*cwide+426009)*executionWidth p l stage 2 := hV
    _ ≤ (2*cwide+426009)*(cw*p) := Nat.mul_le_mul_left _ hw
    _ = _ := by ring

/-- Both executed replica constructors satisfy the selected numerical and setup
profiles. This proof uses their data fields only, independent of solutions. -/
theorem selectedCyclicReplicaProblems_profile (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] {u : ℕ} {α d : ℝ}
    (axis : RecoveryAxisBounds (Sizes.s n i) (Sizes.t n i) (Sizes.p n) u
      (haloInverseRingLog (Sizes.s n i) (Sizes.t n i)) α d)
    (target a span : ℕ) (ha : a < Sizes.s n i) (hn : span ≤ Sizes.s n i)
    (hu : u ≤ Sizes.p n) (htarget : target ≤ ct*Sizes.p n) :
    let p := Sizes.p n
    let l := haloInverseRingLog (Sizes.s n i) (Sizes.t n i)
    let N := (cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width p u) a span).card
    let stage := initialSchurTarget p u
      (boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N) 2
    let q := executionPrecision p l stage 2
    let w := executionWidth p l stage 2
    let cw := 1032+8*ct
    let cV := (2*(16*20+8*cw+8*2+128)+426009)*cw
    ∀ (Fs : List (ZMod (Sizes.s n i) → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ k, ‖value q (F k)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem stage 2 a span ha Fs hF
    let K := axis.cyclicRightReplicaProblem stage 2 a span hn Fs hF
    ∀ R ∈ [H,K], R.p = p ∧ R.t = Sizes.t n i ∧ R.l = l ∧ R.u = u ∧
      R.target = stage ∧ R.rhsExp = 2 ∧ R.Fs = Fs ∧ R.wordWidth = w ∧
      R.target ≤ cw*p ∧ R.metadataWidth ≤ cV*p ∧
      R.l ≤ 20*R.p ∧ 2^R.l ≤ 20*R.p := by
  obtain ⟨hl,hr,hs,hw,hm⟩ := selectedCyclicReplicaSizing ct h i u target a span hu htarget axis.hband
  dsimp only
  intro Fs hF R hR
  simp only [List.mem_cons,List.not_mem_nil,or_false] at hR
  rcases hR with rfl | rfl
  all_goals exact ⟨rfl,rfl,rfl,rfl,rfl,rfl,rfl,rfl,hs,hm,hl,hr⟩

end IntegerMultBounds.MathlibTM2.Cost
