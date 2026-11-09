module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicTableVolumeBound

/-! Computed Schur columns share one original-column and two residual reserves.
Collection and publication controls add only a cubic physical allowance. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellMatrix
  IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
variable {Q A : ℕ} {P₀ U : Type}

private theorem cyclicColumnEntryCostBound_poly {q V s N Z : ℕ}
    (hZ : 1 ≤ Z) (hq : q ≤ Z) (hV : V ≤ Z) (hs : s ≤ Z) (hN : N ≤ Z) :
    cyclicColumnEntryCostBound q V s N ≤ 10000*Z^2 := by
  have hmono : cyclicColumnEntryCostBound q V s N ≤ cyclicColumnEntryCostBound Z Z Z Z := by
    unfold cyclicColumnEntryCostBound cyclicEntryReadCostBound tblC
    gcongr
  have h₁ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have h₀ : 1 ≤ Z^2 := Nat.one_le_pow _ _ hZ
  unfold cyclicColumnEntryCostBound cyclicEntryReadCostBound tblC at hmono ⊢
  nlinarith only [hmono,h₁,h₀]

theorem preparedCyclicColumnsWorkspace_le_components
    (J R K rowPush p l s t u target a n Z : ℕ) [NeZero s]
    (hst : s < t) (ha : a ≤ s) (hn : n ≤ s) (hZ : 1 ≤ Z) (hs : s ≤ Z)
    (hq : executionPrecision p l (initialSchurTarget p u target 2) 2 ≤ Z)
    (hb : PhaseCellBand.width p u ≤ Z)
    (hV : publicationGeometryWidth t (PhaseCellBand.width p u) ≤ Z) :
    let q := executionPrecision p l (initialSchurTarget p u target 2) 2
    preparedCyclicColumnsWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J R K rowPush p l s t u target a n ≤
      originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u+
      2*interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
        J R K rowPush p l s t u (initialSchurTarget p u target 2) 2+5000000*Z^3 := by
  dsimp only
  let q := executionPrecision p l (initialSchurTarget p u target 2) 2
  let band := PhaseCellBand.width p u
  let N := (cyclicPrincipalBoundary s t band a n).card
  let V := publicationGeometryWidth t band
  let cap := cyclicTableEntryCostBound p l s t u target a n
  let table := cyclicTableUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J R K rowPush cap p l s t u target a n
  let base := originalColumnUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U) rowPush p q s t u+
    2*interiorResidualUniformWorkspace (P₀ := P₀) (Q := Q) (A := A) (U := U)
      J R K rowPush p l s t u (initialSchurTarget p u target 2) 2
  have hN : N ≤ Z := (show N ≤ s by simpa only [N,ZMod.card] using
    (cyclicPrincipalBoundary s t band a n).card_le_univ).trans hs
  have hcap : cap ≤ 10000*Z^2 := cyclicColumnEntryCostBound_poly hZ hq hV hs hN
  have htable := cyclicTableUniformWorkspace_le_components (P₀ := P₀) (Q := Q) (A := A) (U := U)
    J R K rowPush cap p l s t u target a n hst ha hn
  have htableBound : table ≤ base+60000*(s+1)*(q+1)+8*cap+100000*(N+s+band+1)*(V+q+1) := by
    simpa only [base,Nat.add_assoc] using htable
  have htail : 2*(4*N+4)+N*((2*(24*band+1)+1)*(2*q+8)+1)+1+
      60000*(s+1)*(q+1)+8*cap+100000*(N+s+band+1)*(V+q+1) ≤
      2*(4*Z+4)+Z*((2*(24*Z+1)+1)*(2*Z+8)+1)+1+
        60000*(Z+1)*(Z+1)+8*(10000*Z^2)+100000*(Z+Z+Z+1)*(Z+Z+1) := by
    gcongr
  have h₁ : Z ≤ Z^3 := Nat.le_self_pow (by decide) Z
  have h₂ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have h₀ : 1 ≤ Z^3 := Nat.one_le_pow _ _ hZ
  have hwidth : executionWidth p l (initialSchurTarget p u target 2) 2 = 2*q+8 := by
    dsimp only [q,executionWidth,executionPrecision]; omega
  unfold preparedCyclicColumnsWorkspace
  change 2*(4*N+4)+(N*((2*(24*band+1)+1)*_+1)+(table+1)) ≤ base+5000000*Z^3
  rw [hwidth]
  nlinarith only [htableBound,htail,h₀,h₁,h₂]

end IntegerMultBounds.MathlibTM2.Cost
