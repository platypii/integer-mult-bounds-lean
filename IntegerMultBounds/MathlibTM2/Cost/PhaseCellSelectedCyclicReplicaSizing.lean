module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicWorkingWidth
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedGatheredStock
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicReplicaProblems
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSecondInteriorBudget

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

/-- The executed second-interior witnesses need no separate target or RHS
suppliers: their retained physical formats give the entire selected profile. -/
theorem selectedCyclicSecondInteriorProfile (ct : ℕ) {m : ℕ} (h : Sizes.Big m)
    (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)] {u : ℕ} {α d : ℝ}
    (axis : RecoveryAxisBounds (Sizes.s m i) (Sizes.t m i) (Sizes.p m) u
      (haloInverseRingLog (Sizes.s m i) (Sizes.t m i)) α d)
    (target a n : ℕ) (ha : a < Sizes.s m i) (hn : n ≤ Sizes.s m i)
    (hu : u ≤ Sizes.p m) (htarget : target ≤ ct*Sizes.p m) :
    let p := Sizes.p m
    let l := haloInverseRingLog (Sizes.s m i) (Sizes.t m i)
    let N := (cyclicPrincipalBoundary (Sizes.s m i) (Sizes.t m i)
      (PhaseCellBand.width p u) a n).card
    let solveTarget := boundaryRecoveryTarget p (target+1)
    let stage := initialSchurTarget p u (boundaryTableBits p solveTarget 2 N) 2
    let q := executionPrecision p l stage 2
    ∀ (Fs : List (ZMod (Sizes.s m i) → GaussianInt))
      (hF : ∀ F ∈ Fs, ∀ k, ‖value q (F k)‖ ≤ (2 : ℝ)^2),
    let H := axis.cyclicLeftReplicaProblem stage 2 a n ha Fs hF
    let K := axis.cyclicRightReplicaProblem stage 2 a n hn Fs hF
    ∀ J L, CyclicSecondInteriorProfile H K J L p solveTarget N →
      ∀ D ∈ [H,K,J,L], D.p = p ∧ D.t = Sizes.t m i ∧ D.l = l ∧ D.u ≤ p ∧
        D.target ≤ (1032+8*ct)*p ∧ D.rhsExp ≤ (1032+8*ct)*p := by
  dsimp only
  intro Fs hF J L profile
  apply profile.numerical_bounds
  intro D hD
  obtain ⟨hp,ht,hl,hu',_,_,_,hw,_,_,_,_⟩ :=
    selectedCyclicReplicaProblems_profile ct h i axis target a n ha hn hu htarget Fs hF D hD
  have hwidth := (selectedCyclicReplicaSizing ct h i u target a n hu htarget axis.hband).2.2.2.1
  exact ⟨hp,ht,hl,hu' ▸ hu,hw ▸ hwidth⟩

end IntegerMultBounds.MathlibTM2.Cost
