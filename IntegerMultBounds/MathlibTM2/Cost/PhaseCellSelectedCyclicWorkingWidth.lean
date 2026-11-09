module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedInteriorInitialization
public import IntegerMultBounds.NLogN.PhaseCellCyclicPrincipalGeometry
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedUncachedCoupling

/-! Keep the joint cyclic boundary count in both pieces' precision. The
existing arbitrary-row-count sizing theorem covers this count directly. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.NLogN.PhaseCellMatrix

theorem selectedCyclicWorkingWidth_le (ct : ℕ) {n : ℕ} (h : Sizes.Big n)
    (i : Fin (Sizes.d n)) [NeZero (Sizes.s n i)] (u target a span : ℕ)
    (htarget : target ≤ ct*Sizes.p n)
    (hband : PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i) :
    let p := Sizes.p n
    let s := Sizes.s n i
    let t := Sizes.t n i
    let l := haloInverseRingLog s t
    let N := (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a span).card
    let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
    executionWidth p l (initialSchurTarget p u bits 2) 2 ≤ (1032+8*ct)*p := by
  apply selectedInverseRowWorkingWidth_le ct h i u target _ htarget hband
  simpa only [ZMod.card] using Finset.card_le_univ
    (s := cyclicPrincipalBoundary (Sizes.s n i) (Sizes.t n i)
      (PhaseCellBand.width (Sizes.p n) u) a span)

/-- Both source masks and either residual piece retain joint-count precision
while reusing the endpoint-uniform uncached coupling polynomial. -/
theorem selectedCyclicCoupling_poly_le (ct : ℕ) :
    ∃ C : ℕ, ∀ n (h : Sizes.Big n) (i : Fin (Sizes.d n)), ∀ [NeZero (Sizes.s n i)],
      ∀ u target a span x y : ℕ, u ≤ Sizes.p n → target ≤ ct*Sizes.p n →
      PhaseCellBand.width (Sizes.p n) u ≤ Sizes.s n i → x ≤ Sizes.s n i → y ≤ Sizes.s n i →
      let p := Sizes.p n
      let s := Sizes.s n i
      let t := Sizes.t n i
      let l := haloInverseRingLog s t
      let band := PhaseCellBand.width p u
      let N := (cyclicPrincipalBoundary s t band a span).card
      let bits := boundaryTableBits p (boundaryRecoveryTarget p (target+1)) 2 N
      let q := executionPrecision p l (initialSchurTarget p u bits 2) 2
      let w := executionWidth p l (initialSchurTarget p u bits 2) 2
      ∀ boundary : Bool, borrowedCouplingPassCost boundary (2^15*p) q w s t u band x y ≤ C*t^5 := by
  obtain ⟨C,hfast⟩ := selectedBorrowedCouplingPass_poly_le (1032+8*ct)
  refine ⟨C,?_⟩
  intro n h i _ u target a span x y hu htarget hband hx hy
  dsimp only
  have hw := selectedCyclicWorkingWidth_le ct h i u target a span htarget hband
  have heq (p l target : ℕ) : executionWidth p l target 2 = 2*executionPrecision p l target 2+8 := by
    unfold executionWidth executionPrecision
    omega
  simp only [heq] at hw ⊢
  exact hfast n h i _ u _ x y hw hu hband hx hy

end IntegerMultBounds.MathlibTM2.Cost
