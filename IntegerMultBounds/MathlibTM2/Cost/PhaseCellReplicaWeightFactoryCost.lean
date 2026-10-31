module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellWeightSetupPolynomial
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellGeometryControlSizing
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellReplicaWeightFactoryBank

/-! Shared numerical page generation has polynomial selected setup cost.
Only the replica count contributes repeated native header work. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast.Main
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

theorem generateReplicaWeightPageCost_poly {N P s t u q L w B Z : ℕ}
    (hZ : 1 ≤ Z) (ht : 1 ≤ t) (hs : s ≤ t) (hB : B ≤ t)
    (hP : P ≤ Z) (hu : u ≤ Z) (hq : q ≤ Z) (hL : L ≤ Z) (hw : w ≤ Z)
    (hV : weightWorkspaceWidth P q w t u ≤ Z) :
    generateReplicaWeightPageCost N P s t u q L w B ≤ 1000031*t*Z^4+2*N := by
  have hc := sharedBatchWeightSetupCost_poly hZ ht hs hB hP hu hq hL hw hV
  have hBL := Nat.mul_le_mul hB hL
  have hBt : B ≤ t*Z := hB.trans (Nat.le_mul_of_pos_right _ hZ)
  have hLt : L ≤ t*Z := hL.trans (Nat.le_mul_of_pos_left _ ht)
  have hone : 1 ≤ t*Z := Nat.mul_le_mul ht hZ
  have hpow : Z ≤ Z^4 := by simpa only [pow_one] using (pow_le_pow_right' hZ (by decide : 1 ≤ 4))
  have hscale := Nat.mul_le_mul_left t hpow
  unfold generateReplicaWeightPageCost prepareReplicaFactoryDimensionsCost
  nlinarith only [hc,hBL,hBt,hLt,hone,hscale]

theorem selectedGenerateReplicaWeightPageCost_poly_le (cw cL : ℕ) :
    ∃ C : ℕ, ∀ (n : ℕ) (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (N B L q w u : ℕ),
      B ≤ Sizes.t n i → L ≤ cL*Sizes.p n → w ≤ cw*Sizes.p n → q ≤ w → u ≤ Sizes.p n →
      generateReplicaWeightPageCost N (2^15*Sizes.p n) (Sizes.s n i) (Sizes.t n i) u q L w B ≤
        C*Sizes.t n i*(Sizes.p n)^4+2*N := by
  let cZ := 2^15+3*cw+cL+426010
  refine ⟨1000031*cZ^4,?_⟩
  intro n h i N B L q w u hB hL hw hq hu
  let p := Sizes.p n
  let Z := cZ*p
  have hp : 1 ≤ p := by have := h.thirteen_le_p; omega
  have hZ : 1 ≤ Z := by dsimp only [Z,cZ]; nlinarith only [hp]
  have hparam (x c : ℕ) (hx : x ≤ c*p) (hc : c ≤ cZ) : x ≤ Z :=
    hx.trans (Nat.mul_le_mul_right p hc)
  have hPZ := hparam (2^15*p) (2^15) le_rfl (by dsimp only [cZ]; omega)
  have huZ := hparam u 1 (by simpa using hu) (by dsimp only [cZ]; omega)
  have hwZ := hparam w cw hw (by dsimp only [cZ]; omega)
  have hqZ := hq.trans hwZ
  have hLZ := hparam L cL hL (by dsimp only [cZ]; omega)
  have hV := selectedWeightWorkspaceWidth_le cw h i q w u hw hq hu
  have hVZ := hparam _ (2*cw+426009) hV (by dsimp only [cZ]; omega)
  have ht : 1 ≤ Sizes.t n i := by have := h.good.lt i; omega
  have hc := generateReplicaWeightPageCost_poly (N := N) hZ ht (h.good.lt i).le hB
    hPZ huZ hqZ hLZ hwZ hVZ
  convert hc using 1
  dsimp only [Z,p]
  ring

/-- The physical factory's stock certificate uses the same shared/replica split. -/
theorem generateReplicaWeightPageWorkspace_poly {Q A : ℕ} {U : Type}
    {N P s t u q L w B Z : ℕ}
    (hZ : 1 ≤ Z) (ht : 1 ≤ t) (hs : s ≤ t) (hB : B ≤ t)
    (hP : P ≤ Z) (hu : u ≤ Z) (hq : q ≤ Z) (hL : L ≤ Z) (hw : w ≤ Z)
    (hV : weightWorkspaceWidth P q w t u ≤ Z) :
    mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
      generateReplicaWeightPageCost N P s t u q L w B ≤
    mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*
      (1000031*t*Z^4)+2*mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U))*N := by
  have hc := Nat.mul_le_mul_left
    (mnProgPush (generateReplicaWeightPage (P₀ := Empty) (Q := Q) (A := A) (U := U)))
    (generateReplicaWeightPageCost_poly (N := N) hZ ht hs hB hP hu hq hL hw hV)
  calc
    _ ≤ _ := hc
    _ = _ := by ring

end IntegerMultBounds.MathlibTM2.Cost
