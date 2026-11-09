module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicCollectionWorkspaceBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicColumnEntryCostBound
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCollectRetireCyclicColumn

/-! Structural collection time from one derived uniform entry price. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
open IntegerMultBounds.NLogN.PhaseCellMatrix
open IntegerMultBounds.MathlibTM2.Fast.TableVM

theorem cyclicColumnEntryCostBound_poly {q V s rowCount Z : ℕ}
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hV : V ≤ Z) (hs : s ≤ Z) (hrows : rowCount ≤ Z) :
    cyclicColumnEntryCostBound q V s rowCount+9 ≤ 100000*Z^2 := by
  have hm : cyclicColumnEntryCostBound q V s rowCount ≤ cyclicColumnEntryCostBound Z Z Z Z := by
    unfold cyclicColumnEntryCostBound cyclicEntryReadCostBound tblC
    gcongr
  have hp : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  unfold cyclicColumnEntryCostBound cyclicEntryReadCostBound tblC at hm ⊢
  nlinarith only [hm,hp,hZ]

theorem collectCyclicColumnEntriesCost_le {s : ℕ} [NeZero s] (B : Finset (ZMod s))
    (q V a b start L : ℕ) (ha : a ≤ s) (hb : b ≤ s) (hfit : start+L ≤ B.card) :
    collectCyclicColumnEntriesCost B q V a b start L ≤
      L*(cyclicColumnEntryCostBound q V s B.card+9)+2*start+8 := by
  have hsum := Finset.sum_le_sum (s := Finset.range L) (f := fun j =>
    cyclicColumnEntryStepCost q V s a b (start+j) (bFoldAt s B (start+j)).val+3)
    (g := fun _ => cyclicColumnEntryCostBound q V s B.card+3) (by
      intro j hj
      have hj' := Finset.mem_range.mp hj
      exact Nat.add_le_add_right (cyclicColumnEntryStepCost_le q V s a b (start+j) _ B.card
        ha hb (by omega) (bFoldAt s B (start+j)).val_lt) 3)
  simp only [Finset.sum_const,Finset.card_range,smul_eq_mul] at hsum
  unfold collectCyclicColumnEntriesCost cyclicColumnEntryLoopCost
  nlinarith only [hsum]

/-- The clipped band has at most twice the bandwidth plus one entries;
all index-dependent controllers use the existing row-count envelope. -/
theorem preparedCyclicBandCollectionCost_le_uniform {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band a b n : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hn : n ≤ B.card) :
    preparedCyclicBandCollectionCost B q V band a b n ≤
      scaledBandControls24CostBound band B.card+
        (2*(24*band+1)+1)*(cyclicColumnEntryCostBound q V s B.card+9)+2*B.card+8 := by
  let W := 24*band+1
  let start := n-W
  let L := min B.card (n+W+1)-start
  have hstart : start ≤ B.card := by dsimp [start]; omega
  have hfit : start+L ≤ B.card := by dsimp [L,start]; omega
  have hlen : L ≤ 2*W+1 := by dsimp [L,start]; omega
  have hcollect := collectCyclicColumnEntriesCost_le B q V a b start L ha hb hfit
  have hcontrols := scaledBandControls24Cost_le n band B.card hn
  have hmul := Nat.mul_le_mul_right (cyclicColumnEntryCostBound q V s B.card+9) hlen
  unfold preparedCyclicBandCollectionCost
  change scaledBandControlsCost 24 n band B.card+
    collectCyclicColumnEntriesCost B q V a b start L ≤ _
  dsimp only [W] at hmul
  omega

theorem preparedCyclicBandCollectionCost_poly {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band a b n Z : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hn : n ≤ B.card)
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hV : V ≤ Z) (hs : s ≤ Z)
    (hrows : B.card ≤ Z) (hband : band ≤ Z) :
    preparedCyclicBandCollectionCost B q V band a b n ≤ 6000000*Z^3 := by
  have hentry := cyclicColumnEntryCostBound_poly hZ hq hV hs hrows
  have hcollect := preparedCyclicBandCollectionCost_le_uniform B q V band a b n ha hb hn
  have hlen : 2*(24*band+1)+1 ≤ 51*Z := by omega
  have hprod := Nat.mul_le_mul hlen hentry
  have hp : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have hone : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  unfold scaledBandControls24CostBound at hcollect
  nlinarith only [hcollect,hprod,hp,hone,hrows,hband]

theorem collectRetireCyclicColumnCost_poly {s : ℕ} [NeZero s]
    (B : Finset (ZMod s)) (q V band a b n Z : ℕ)
    (ha : a ≤ s) (hb : b ≤ s) (hn : n ≤ B.card)
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hV : V ≤ Z) (hs : s ≤ Z)
    (hrows : B.card ≤ Z) (hband : band ≤ Z) :
    collectRetireCyclicColumnCost B q V band a b n ≤ 6010000*Z^3 := by
  have hc := preparedCyclicBandCollectionCost_poly B q V band a b n Z
    ha hb hn hZ hq hV hs hrows hband
  have hm := Nat.mul_le_mul hs hq
  have hp : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have hp2 : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have hone : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  unfold collectRetireCyclicColumnCost retireCyclicColumnStreamsCost
  nlinarith only [hc,hm,hp,hp2,hone,hq,hs]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
