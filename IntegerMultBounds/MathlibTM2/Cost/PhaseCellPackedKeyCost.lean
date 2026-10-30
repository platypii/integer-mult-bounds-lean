module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellPackedPublicationCost
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellUncachedInteriorPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPackedHaloKeyLoop
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellHaloInteriorCost

/-! Reuse scalar batch arithmetic in each packed key. All header, origin and
publication control work is charged to a common polynomial envelope. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

/-- Dimensions used by the control part of one packed length key. -/
def packedHaloKeyDimensions (p l s t u target rhsExp a b V L : ℕ) : List ℕ :=
  let band := PhaseCellBand.width p u
  [V,b-a,L,(haloPackedOffsets s t band a b L).length,
    executionPrecision p l target rhsExp,executionWidth p l target rhsExp,
    2^15*p,executionStagePrecision p l target rhsExp+1,l,s,t,u,band,
    haloPhaseCount s t a b,(haloLengthGroup s t band a b L).length]

theorem packedHaloKeyCost_le_bound
    (p l s t u target rhsExp a b V L Z : ℕ) (hZ : 1 ≤ Z)
    (hd : ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloKeyCost p l s t u target rhsExp a b V L ≤
      sizedClosedBatchBound p l (haloPackedOffsets s t (PhaseCellBand.width p u) a b L).length
        L s t u target rhsExp+120000*Z^4 := by
  let q := executionPrecision p l target rhsExp
  let band := PhaseCellBand.width p u
  let stage := executionStagePrecision p l target rhsExp+1
  let base := (2*s+2*V+6*L+17*V+16)+
    installGroupHeadersCost (2^15*p) stage q l s t u band L+
    binaryHaloClassCost V s t band a b L+2
  have hbase : base ≤ 100000*Z^4 := by
    have hmono : base ≤ (2*Z+2*Z+6*Z+17*Z+16)+
        installGroupHeadersCost Z Z Z Z Z Z Z Z Z+
        (136*Z+137+(((36*Z+16)*tblC Z Z+Z*(8*Z+6)+6)+(62*Z+63)))+2 := by
      dsimp only [base,q,band,stage]
      unfold installGroupHeadersCost binaryHaloClassCost releasedHaloClassCost tblC
      gcongr <;> exact hd _ (by simp [packedHaloKeyDimensions])
    apply hmono.trans
    unfold installGroupHeadersCost tblC
    have h₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
    have h₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
    have h₄ : Z^3 ≤ Z^4 := Nat.pow_le_pow_right hZ (by decide)
    nlinarith only [hZ,h₂,h₃,h₄]
  have hpub := reusablePackedCellBatchPublishCost_le_bound p l target rhsExp V (b-a) L
    (haloPackedOffsets s t band a b L).length s t u Z hZ
    (hd _ (by simp [packedHaloKeyDimensions])) (hd _ (by simp [packedHaloKeyDimensions]))
    (hd _ (by simp [packedHaloKeyDimensions])) (hd _ (by simp [packedHaloKeyDimensions,band]))
    (hd _ (by simp [packedHaloKeyDimensions])) (hd _ (by simp [packedHaloKeyDimensions]))
  have hempty : 2*((2^15*p)+stage+q+l+s+t+u+band+2*L)+21 ≤ 1000*Z := by
    have hmono : 2*((2^15*p)+stage+q+l+s+t+u+band+2*L)+21 ≤
        2*(Z+Z+Z+Z+Z+Z+Z+Z+2*Z)+21 := by
      dsimp only [stage,q,band]
      gcongr <;> exact hd _ (by simp [packedHaloKeyDimensions])
    omega
  have hpow : Z ≤ Z^4 := Nat.le_self_pow (by decide) Z
  unfold packedHaloKeyCost
  dsimp only
  dsimp only [base,q,band,stage] at hbase hempty hpub
  split <;> nlinarith only [hbase,hempty,hpub,hpow]

/-- Lift the per-key comparison structurally over the actual key list. -/
theorem packedHaloKeyLoopCost_le_bound
    (p l s t u target rhsExp a b V Z : ℕ) (keys : List ℕ) (hZ : 1 ≤ Z)
    (hd : ∀ L ∈ keys, ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloKeyLoopCost p l s t u target rhsExp a b V keys ≤
      (keys.map (fun L => sizedClosedBatchBound p l
        (haloPackedOffsets s t (PhaseCellBand.width p u) a b L).length L s t u target rhsExp)).sum+
        keys.length*(120000*Z^4+3)+1 := by
  have hsum := List.sum_le_sum (l := keys) (fun L hL =>
    Nat.add_le_add_right (packedHaloKeyCost_le_bound p l s t u target rhsExp a b V L Z hZ (hd L hL)) 3)
  unfold packedHaloKeyLoopCost
  simpa only [Nat.add_assoc,List.sum_map_add,List.map_const',List.sum_replicate,smul_eq_mul] using Nat.add_le_add_right hsum 1

/-- Use the existing geometric identity for the total cell and coordinate
volume. Shared setup is paid for at most six candidate lengths. -/
theorem packedHaloKeyLoopCost_geometry_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b V Z : ℕ) (hZ : 1 ≤ Z)
    (hd : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloKeyLoopCost p l s t u target rhsExp a b V
        (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      ((haloLengthCandidates s t (PhaseCellBand.width p u) a b).map
        (fun L => sizedClosedBatchBound p l 0 L s t u target rhsExp)).sum+
      (haloInterior s t (PhaseCellBand.width p u) a b).card*batchCoordinateCost p l t u target rhsExp+
      (t-s+1)*batchCellCost p l t u target rhsExp+6*(120000*Z^4+3)+1 := by
  have hloop := packedHaloKeyLoopCost_le_bound p l s t u target rhsExp a b V Z
    (haloLengthKeys s t (PhaseCellBand.width p u) a b) hZ hd
  have hsum := haloLengthKeys_cost_le hst (PhaseCellBand.width p u) a b
    (fun L => sizedClosedBatchBound p l 0 L s t u target rhsExp)
    (batchCoordinateCost p l t u target rhsExp) (batchCellCost p l t u target rhsExp)
  have hkeys := Nat.mul_le_mul_right (120000*Z^4+3)
    (haloLengthKeys_length_le s t (PhaseCellBand.width p u) a b)
  simp only [haloPackedOffsets_length] at hloop
  have heq : (haloLengthKeys s t (PhaseCellBand.width p u) a b).map
      (fun L => sizedClosedBatchBound p l (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length
        L s t u target rhsExp) =
      (haloLengthKeys s t (PhaseCellBand.width p u) a b).map
        (fun L => sizedClosedBatchBound p l 0 L s t u target rhsExp+
          ((haloLengthGroup s t (PhaseCellBand.width p u) a b L).length*L)*batchCoordinateCost p l t u target rhsExp+
          (haloLengthGroup s t (PhaseCellBand.width p u) a b L).length*batchCellCost p l t u target rhsExp) := by
    apply List.map_congr_left
    intro L _
    exact sizedClosedBatchBound_eq p l _ L s t u target rhsExp
  rw [heq] at hloop
  omega

/-- The packed loop reuses the established interior arithmetic bound. Its
additional work is a polynomial control allowance independent of cell count. -/
theorem packedHaloKeyLoopCost_interior_le {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b V Z : ℕ) (hZ : 1 ≤ Z)
    (hd : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloKeyLoopCost p l s t u target rhsExp a b V
        (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      haloInteriorCostBound p l s t u target rhsExp a b+6*(120000*Z^4+3)+1 := by
  have hloop := packedHaloKeyLoopCost_geometry_le hst p l u target rhsExp a b V Z hZ hd
  have hsum := List.sum_le_sum (l := haloLengthCandidates s t (PhaseCellBand.width p u) a b)
    (fun L _ => show sizedClosedBatchBound p l 0 L s t u target rhsExp ≤
        haloClassSharedCost p l L s t u target rhsExp a b by
      dsimp only [haloClassSharedCost]
      omega)
  have hcell := Nat.mul_le_mul_left (t-s+1)
    (show batchCellCost p l t u target rhsExp ≤ haloClassCellCost p l t u target rhsExp by
      dsimp only [haloClassCellCost]
      omega)
  dsimp only [haloInteriorCostBound]
  omega

/-- Transfer the retained-family arithmetic estimate to the executed packed
loop, paying only a polynomial allowance for uncached weights and tape work. -/
theorem packedHaloKeyLoopCost_weights_poly {s t : ℕ} [NeZero s] (hst : s < t)
    (p l u target rhsExp a b V Z : ℕ) (hZ : 1 ≤ Z)
    (hP : 2^15*p ≤ Z) (hN : executionStagePrecision p l target rhsExp+1 ≤ Z)
    (hq : executionPrecision p l target rhsExp ≤ Z) (hl : l ≤ Z) (hu : u ≤ Z)
    (hw : executionWidth p l target rhsExp ≤ Z)
    (hV : weightWorkspaceWidth (2^15*p) (executionPrecision p l target rhsExp)
      (executionWidth p l target rhsExp) t u ≤ Z)
    (hkeys : ∀ L ∈ haloLengthCandidates s t (PhaseCellBand.width p u) a b, L ≤ Z)
    (hd : ∀ L ∈ haloLengthKeys s t (PhaseCellBand.width p u) a b,
      ∀ x ∈ packedHaloKeyDimensions p l s t u target rhsExp a b V L, x ≤ Z) :
    packedHaloKeyLoopCost p l s t u target rhsExp a b V
        (haloLengthKeys s t (PhaseCellBand.width p u) a b) ≤
      familyHaloInteriorGeometryCost p l s t u target rhsExp a b+11000000*t*Z^4 := by
  have hloop := packedHaloKeyLoopCost_interior_le hst p l u target rhsExp a b V Z hZ hd
  have hscalar := haloInteriorCostBound_weights_poly p l u target rhsExp a b Z hst hZ
    hP hN hq hl hu hw hV hkeys
  have ht : 1 ≤ t := by have := NeZero.pos s; omega
  have hpow : 1 ≤ Z^4 := one_le_pow₀ hZ
  have hscale : Z^4 ≤ t*Z^4 := Nat.le_mul_of_pos_left _ ht
  nlinarith only [hloop,hscalar,hpow,hscale]

end IntegerMultBounds.MathlibTM2.Cost
