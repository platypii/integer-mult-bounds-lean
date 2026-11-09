module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallCyclicFactorSeeds

/-! The ten ordinary masters are copied by the same structural header copier
as other callers. Their bill depends only on source lengths. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry
open IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Mult.ShortConv
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem masterHeaderCopiesCost_eq {T A : ℕ} (work : Fin 224 → Fin T) (source : Fin 10 → Fin T)
    (S : Stacks T A) (P N q l s t u band a n : ℕ)
    (hvalues : ∀ i, (S.R (source i)).length = masterHeaderValues P N q l s t u band a n i) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (masterHeaderCopies work source) =
      4*(P+N+q+l+s+t+u+band+a+n)+41 := by
  simp only [copyUnaryHeadersCost,masterHeaderCopies,List.map_ofFn,Function.comp_def,hvalues]
  simp [masterHeaderValues,List.ofFn_succ]
  ring

theorem cyclicFactorSeedCopyCost_le {T A s : ℕ} [NeZero s]
    (work : Fin 224 → Fin T) (source : Fin 10 → Fin T) (S : Stacks T A)
    (p l t u target a n Z : ℕ) (hZ : 1 ≤ Z)
    (hp : p ≤ Z) (hl : l ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z) (hu : u ≤ Z)
    (hb : PhaseCellBand.width p u ≤ Z) (ha : a ≤ Z) (hn : n ≤ Z)
    (hw : executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t
        (PhaseCellBand.width p u) a n).card) 2) 2 ≤ Z)
    (hvalues : ∀ i, (S.R (source i)).length = cyclicFactorMasterValues p l s t u target a n i) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (masterHeaderCopies work source) ≤ 140000*Z := by
  have hcopy := masterHeaderCopiesCost_eq work source S _ _ _ _ _ _ _ _ _ _ hvalues
  rw [hcopy]
  have hq : executionPrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t
        (PhaseCellBand.width p u) a n).card) 2) 2 ≤ Z := by
    unfold executionWidth executionPrecision at *
    omega
  have hstage : executionStagePrecision p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t
        (PhaseCellBand.width p u) a n).card) 2) 2 ≤ Z := by
    unfold executionWidth executionStagePrecision at *
    omega
  norm_num only [Nat.reducePow]
  omega

/-- Preserve the shared axis polynomial before summing setup calls. -/
theorem cyclicFactorSeedCopyCost_axis {T A s : ℕ} [NeZero s]
    (work : Fin 224 → Fin T) (source : Fin 10 → Fin T) (S : Stacks T A)
    (p l t u target a n cw : ℕ) (hst : s < t) (hp : 1 ≤ p) (hl : l ≤ 20*p)
    (hu : u ≤ p) (hb : PhaseCellBand.width p u ≤ s) (ha : a ≤ s) (hn : n ≤ s)
    (hw : executionWidth p l (initialSchurTarget p u (boundaryTableBits p target 2
      (cyclicPrincipalBoundary s t (PhaseCellBand.width p u) a n).card) 2) 2 ≤ cw*p)
    (hvalues : ∀ i, (S.R (source i)).length = cyclicFactorMasterValues p l s t u target a n i) :
    copyUnaryHeadersCost (fun k => (S.R k).length) (masterHeaderCopies work source) ≤
      (140000*(cw+21))*t*p := by
  let c := cw+21
  let Z := c*t*p
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hc : 21 ≤ c := by dsimp only [c]; omega
  have htZ : t ≤ Z :=
    (Nat.le_mul_of_pos_left t (by omega : 1 ≤ c)).trans (Nat.le_mul_of_pos_right _ hp)
  have hsZ : s ≤ Z := hst.le.trans htZ
  have hparam (x k : ℕ) (hx : x ≤ k*p) (hk : k ≤ c) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p (hk.trans (Nat.le_mul_of_pos_right c ht)))
  have hpZ : p ≤ Z := hparam p 1 (by simp) (by omega)
  have hcopy := cyclicFactorSeedCopyCost_le work source S p l t u target a n Z
    (ht.trans htZ) hpZ (hparam _ 20 hl (by omega)) hsZ htZ (hu.trans hpZ)
    (hb.trans hsZ) (ha.trans hsZ) (hn.trans hsZ)
    (hparam _ cw hw (by dsimp only [c]; omega)) hvalues
  calc
    _ ≤ 140000*Z := hcopy
    _ = _ := by dsimp only [Z,c]; ring

end IntegerMultBounds.MathlibTM2.Cost
