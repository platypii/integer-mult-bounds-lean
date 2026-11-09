module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicNormalizationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicCorePublicationWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicComplexCore

/-! Reprice the actual numerical tail, retaining the recovery allowance verbatim.
This isolates the remaining selected-space comparison at the recovery boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P U : Type}

theorem selectedCyclicComplexCoreWorkspace_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (cq cw : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)),
      ∀ [NeZero (Sizes.s m i)] (H K J L : ReplicaHaloProblem (Sizes.s m i)),
      ∀ u l t a n target q w W N replicas complexCount radius core : ℕ,
      q ≤ cq*Sizes.p m → W ≤ cw*Sizes.p m → Sizes.p m ≤ W →
      a+n ≤ Sizes.s m i → radius+core ≤ n →
      q-Sizes.p m+inverseNormalizationShift (Sizes.p m)+(2*Sizes.p m+13) ≤ 2*q+8 →
      cyclicComplexCoreWorkspace (P := P) (A := A) (U := U) H K J L hR hQ
        (Sizes.p m) u l t a n target q w W N replicas complexCount radius core ≤
      cyclicPackedRecoveryWorkspace (P := P) (A := A) (U := U) H K J L hR hQ
        (Sizes.p m) u l t a n target q w N replicas+
        ((32*cq+1800)*replicas*(n+2)*(W+1)+
          1300*(replicas+complexCount)*(n+1)*(W+1))+3*Sizes.T m := by
  filter_upwards [selectedCyclicNormalizationWorkspace_le cq cw,
    selectedCyclicCorePublicationWorkspace_le cw] with m hnormal hpublication
  intro h i _ H K J L u l t a n target q w W N replicas complexCount radius core
    hq hW hpW hfit hcore hsize
  have hleft := hnormal h i q W a n replicas hq hW hpW hfit hsize
  have hright := hnormal h i q W 0 0 replicas hq hW hpW (by omega) hsize
  have hpub := hpublication h i radius core n W replicas complexCount hcore (by omega) hW
  have hmin : min n (Sizes.s m i-a) = n := min_eq_left (by omega)
  simp only [cyclicComplexCoreWorkspace,cyclicPackedNormalizationWorkspace,hmin,Nat.sub_self]
  nlinarith only [hleft,hright,hpub]

end IntegerMultBounds.MathlibTM2.Cost
