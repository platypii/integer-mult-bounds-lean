module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCyclicNormalizationWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedPackedCyclicWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellCyclicCorePublicationWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellExecutedCyclicComplexCore

/-! Reprice the actual numerical tail, retaining the recovery allowance verbatim.
This isolates the remaining selected-space comparison at the recovery boundary. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
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

private theorem normalizationPublicationTail_le (D cW replicas complexCount n W t p : ℕ)
    (ht : 1 ≤ t) (hp : 1 ≤ p) (hn : n ≤ t) (hW : W ≤ cW*p) (hcount : complexCount ≤ replicas) :
    D*replicas*(n+2)*(W+1)+1300*(replicas+complexCount)*(n+1)*(W+1) ≤
      (3*D+5200)*(cW+1)*replicas*t*p := by
  have hn₂ : n+2 ≤ 3*t := by omega
  have hn₁ : n+1 ≤ 2*t := by omega
  have hwidth : W+1 ≤ (cW+1)*p := by nlinarith only [hW,hp]
  have hleft : D*replicas*(n+2)*(W+1) ≤ D*replicas*(3*t)*((cW+1)*p) := by gcongr
  have hright : 1300*(replicas+complexCount)*(n+1)*(W+1) ≤
      1300*(2*replicas)*(2*t)*((cW+1)*p) := by gcongr; omega
  calc
    _ ≤ D*replicas*(3*t)*((cW+1)*p)+1300*(2*replicas)*(2*t)*((cW+1)*p) := Nat.add_le_add hleft hright
    _ = _ := by ring

noncomputable def cyclicComplexWorkspaceTrafficFactor (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce cW : ℕ) : ℕ :=
  let cw := 16*20+8*ct+8*ce+128
  packedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce+
    (3*(32*cw+1800)+5200)*(cW+1)

theorem selectedCyclicComplexCoreWorkspace_total_le (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (ct ce cb cW : ℕ) :
    let cw := 16*20+8*ct+8*ce+128
    ∀ᶠ m : ℕ in atTop, ∀ (_h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ (H K J L : ReplicaHaloProblem (Sizes.s m i)) (u target a n replicas complexCount W radius core : ℕ),
      let p := Sizes.p m
      let s := Sizes.s m i
      let t := Sizes.t m i
      let l := haloInverseRingLog s t
      let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
      let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
      let q := executionPrecision p l stage 2
      let w := executionWidth p l stage 2
      (∀ D ∈ [H,K,J,L], D.p = p ∧ D.t = t ∧ D.l = l ∧ D.u ≤ p ∧
        D.target ≤ ct*p ∧ D.rhsExp ≤ ce*p) →
      H.SameLayout J → K.SameLayout L → H.Fs.length = replicas → K.Fs.length = replicas →
      w ≤ cw*p → PhaseCellBand.width p u ≤ cb*p → u ≤ p → PhaseCellBand.width p u ≤ s →
      a+n ≤ s → radius+core ≤ n → W ≤ cW*p → p ≤ W → complexCount ≤ replicas →
      q-p+inverseNormalizationShift p+(2*p+13) ≤ 2*q+8 →
      cyclicComplexCoreWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
        p u l t a n target q w W N replicas complexCount radius core ≤
        cyclicComplexWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce cW*replicas*t*p+39*Sizes.T m := by
  dsimp only
  let cw := 16*20+8*ct+8*ce+128
  filter_upwards [selectedCyclicPackedRecoveryWorkspace_le (A := A) (U := U) hR hQ ct ce cb,
    selectedCyclicComplexCoreWorkspace_le (P := Empty) (A := A) (U := U) hR hQ cw cW] with m hp ht
  intro h i _ H K J L u target a n replicas complexCount W radius core
  let p := Sizes.p m
  let s := Sizes.s m i
  let t := Sizes.t m i
  let l := haloInverseRingLog s t
  let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card
  let stage := initialSchurTarget p u (boundaryTableBits p target 2 N) 2
  let q := executionPrecision p l stage 2
  let w := executionWidth p l stage 2
  intro hprofile layoutH layoutK hcountH hcountK hw hbP hu hb hfit hcore hW hpW hcount hsize
  have hpacked := hp h i H K J L u target a n replicas hprofile layoutH layoutK hcountH hcountK
    hw hbP hu hb (by omega) (by omega)
  have hqW : q ≤ w := by dsimp only [q,w,executionPrecision,executionWidth]; omega
  have htail := ht h i H K J L u l t a n target q w W N replicas complexCount radius core
    (hqW.trans hw) hW hpW hfit hcore hsize
  have htpos : 1 ≤ t := by have := h.good.lt i; dsimp only [t]; omega
  have hppos : 1 ≤ p := by have := h.thirteen_le_p; dsimp only [p]; omega
  have hn : n ≤ t := (show n ≤ s by omega).trans (h.good.lt i).le
  have hlinear := normalizationPublicationTail_le (32*cw+1800) cW replicas complexCount n W t p
    htpos hppos hn hW hcount
  unfold cyclicComplexWorkspaceTrafficFactor
  change cyclicComplexCoreWorkspace (P := Empty) (A := A) (U := U) H K J L hR hQ
    p u l t a n target q w W N replicas complexCount radius core ≤
    (packedCyclicWorkspaceTrafficFactor (A := A) (U := U) hR hQ ct ce+
      (3*(32*cw+1800)+5200)*(cW+1))*replicas*t*p+39*Sizes.T m
  nlinarith only [hpacked,htail,hlinear]

end IntegerMultBounds.MathlibTM2.Cost
