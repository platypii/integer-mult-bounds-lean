module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedScaledFactorWorkspace
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedCachedCyclicPassWorkspace
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellConstructedCyclicResidualBatch

/-! Isolate the actual cyclic factor page; its numerical factorization is absorbed. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult IntegerMultBounds.NLogN
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
  IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {U : Type}

noncomputable def closedCyclicFactorColumnsWorkspace (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  preparedCyclicColumnsWorkspace (P₀ := Empty) (Q := Q) (A := A) (U := U)
    (cyclicRecoveryMulPush (A := A) (U := U) hQ)
    (cyclicReplicaRingPush (A := A) (U := U) hR)
    (cyclicReplicaBatchPush (A := A) (U := U) hQ)
    (cyclicRecoveryMulPush (A := A) (U := U) hQ) p l s t u bits a n

noncomputable def closedCyclicFactorPageWorkspace (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l s t a n target : ℕ) [NeZero s] : ℕ :=
  let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
  let bits := boundaryTableBits p target 2 B.card
  preparedCyclicFactorPageWorkspace (P₀ := Empty) (Q := Q) (A := A) (U := U)
    (cyclicRecoveryMulPush (A := A) (U := U) hQ)
    (cyclicReplicaRingPush (A := A) (U := U) hR)
    (cyclicReplicaBatchPush (A := A) (U := U) hQ)
    (cyclicRecoveryMulPush (A := A) (U := U) hQ) p l s t u bits a n

theorem actualCyclicFactorWorkspace_eq_page_add (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (p u l s t a n target : ℕ) [NeZero s] :
    let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
    let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2
    actualCyclicFactorWorkspace (P₀ := Empty) (A := A) (U := U) hR hQ p u l s t a n target =
      closedCyclicFactorPageWorkspace (A := A) (U := U) hR hQ p u l s t a n target+
        scaledInitializedBoundaryFactorWorkspace (P := Empty) (A := A) (U := U)
          2 hQ p q (PhaseCellBand.width p u) B.card := by
  rfl

theorem selectedActualCyclicFactorWorkspace_le_page (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (cq cb : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ u l t a n target : ℕ,
      let p := Sizes.p m
      let s := Sizes.s m i
      let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
      let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2
      q ≤ cq*p → PhaseCellBand.width p u ≤ cb*p →
      actualCyclicFactorWorkspace (P₀ := Empty) (A := A) (U := U) hR hQ p u l s t a n target ≤
        closedCyclicFactorPageWorkspace (A := A) (U := U) hR hQ p u l s t a n target+Sizes.T m := by
  filter_upwards [selectedScaledInitializedBoundaryFactorWorkspace_le (A := A) (U := U) hQ cq cb 1] with m hs
  intro h i _ u l t a n target
  dsimp only
  intro hq hb
  have hcard : (cyclicPrincipalBoundary (Sizes.s m i) t (PhaseCellBand.width (Sizes.p m) u) a n).card ≤
      Sizes.s m i := by
    simpa only [ZMod.card] using
      (cyclicPrincipalBoundary (Sizes.s m i) t (PhaseCellBand.width (Sizes.p m) u) a n).card_le_univ
  have hnum := hs h i _ _ _ hq hb hcard
  simp only [one_mul] at hnum
  rw [actualCyclicFactorWorkspace_eq_page_add]
  exact Nat.add_le_add_left hnum _

theorem selectedActualCyclicFactorWorkspace_le_columns (hR : rpStates ≤ Q) (hQ : SS.states ≤ Q)
    (cq cb : ℕ) :
    ∀ᶠ m : ℕ in atTop, ∀ (h : Sizes.Big m) (i : Fin (Sizes.d m)) [NeZero (Sizes.s m i)],
      ∀ u l t a n target : ℕ,
      let p := Sizes.p m
      let s := Sizes.s m i
      let B := cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n
      let q := executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2 B.card) 2) 2
      q ≤ cq*p → PhaseCellBand.width p u ≤ cb*p →
      actualCyclicFactorWorkspace (P₀ := Empty) (A := A) (U := U) hR hQ p u l s t a n target ≤
        closedCyclicFactorColumnsWorkspace (A := A) (U := U) hR hQ p u l s t a n target+2*Sizes.T m := by
  filter_upwards [selectedActualCyclicFactorWorkspace_le_page (A := A) (U := U) hR hQ cq cb,
    selectedScaledFactorPageWorkspace_le cq cb] with m hs hp
  intro h i _ u l t a n target
  dsimp only
  intro hq hb
  have hcard : (cyclicPrincipalBoundary (Sizes.s m i) t (PhaseCellBand.width (Sizes.p m) u) a n).card ≤
      Sizes.s m i := by
    simpa only [ZMod.card] using
      (cyclicPrincipalBoundary (Sizes.s m i) t (PhaseCellBand.width (Sizes.p m) u) a n).card_le_univ
  have hfactor := hs h i u l t a n target hq hb
  have hpub := hp h i _ _ _ hq hb hcard
  have hpage : closedCyclicFactorPageWorkspace (A := A) (U := U) hR hQ
      (Sizes.p m) u l (Sizes.s m i) t a n target ≤
      closedCyclicFactorColumnsWorkspace (A := A) (U := U) hR hQ
        (Sizes.p m) u l (Sizes.s m i) t a n target+Sizes.T m := by
    unfold closedCyclicFactorPageWorkspace preparedCyclicFactorPageWorkspace closedCyclicFactorColumnsWorkspace
    exact Nat.add_le_add_left hpub _
  nlinarith only [hfactor,hpage]

end IntegerMultBounds.MathlibTM2.Cost
