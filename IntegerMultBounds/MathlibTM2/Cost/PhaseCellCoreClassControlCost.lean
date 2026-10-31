module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPrepareCoreClass
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellSelectedNumericalSetup
public import IntegerMultBounds.NLogN.PhaseCellCoreLocalityGeometry

/-! Class preparation and retirement pay payload-linear counter work and one
replica-independent polynomial origin-generation bill. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open Filter IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.NLogN.PhaseCellMatrix
variable {A s : ℕ} [NeZero s]

theorem supplierBatchCountCost_eq (r : PackedNormalizedJob A s) :
    supplierBatchCountCost r = 4*r.inputPayload.length+9*r.Fs.length+4 := by
  rw [PackedNormalizedJob.inputPayload_length]
  unfold supplierBatchCountCost
  ring

theorem coreClassTimeBill_eq (r : PackedNormalizedJob A s) (origins N cost : ℕ) :
    (origins+supplierBatchCountCost r)+(N*(cost+5)+4)+(2*(N+r.inputPayload.length)+5) =
      origins+N*(cost+7)+6*r.inputPayload.length+9*r.Fs.length+13 := by
  rw [supplierBatchCountCost_eq]
  ring

theorem coreClassStockBill_eq (r : PackedNormalizedJob A s) (origins reserve : ℕ) :
    (3*origins+2*supplierBatchCountCost r)+reserve =
      3*origins+reserve+8*r.inputPayload.length+18*r.Fs.length+8 := by
  rw [supplierBatchCountCost_eq]
  ring

theorem preparedCoreOriginsCost_poly {V s width radius L R : ℕ} (hw : 0 < width)
    (hR : 1 ≤ R) (hs : s ≤ R) (hV : V ≤ R) :
    preparedCoreOriginsCost V s width radius L ≤ 100000*R^3 := by
  have hcount : (s+width-1)/width ≤ R := by
    have hc := coreIndices_length_le s width hw
    simpa only [coreIndices,List.length_range] using hc.trans hs
  have hrows := (coreGatherIndices_length_le s width radius L hw).trans hs
  have hR2 : R ≤ R^2 := Nat.le_self_pow (by decide) R
  have hR3 : R^2 ≤ R^3 := Nat.pow_le_pow_right hR (by decide)
  have hR13 := hR2.trans hR3
  have hunit := hR.trans hR13
  have htable : tblC V V ≤ 1000*R^2 := by
    have hsq := Nat.pow_le_pow_left (show V+4 ≤ 5*R by omega) 2
    unfold tblC
    nlinarith only [hsq,hV,hR2]
  have hfactor := Nat.mul_le_mul (show 18*((s+width-1)/width)+9 ≤ 27*R by omega) htable
  have hrowCost := Nat.mul_le_mul hrows (show 8*V+6 ≤ 14*R by omega)
  unfold preparedCoreOriginsCost
  nlinarith only [hfactor,hrowCost,hV,hR2,hR3,hR13,hunit]

theorem selectedCoreOriginsCost_poly_le (cB : ℕ) :
    ∃ C : ℕ, ∀ n : ℕ, ∀ (_h : Sizes.Big n) (i : Fin (Sizes.d n)) (V width radius L : ℕ),
      0 < width → V ≤ cB*Sizes.p n →
      preparedCoreOriginsCost V (Sizes.s n i) width radius L ≤ C*Sizes.t n i^3 := by
  refine ⟨100000*(cB+1)^3,?_⟩
  intro n h i V width radius L hw hV
  let R := (cB+1)*Sizes.t n i
  have hp : 1 ≤ Sizes.p n := by have := h.thirteen_le_p; omega
  have hpt := selectedPrecision_le_axis h i
  have htR : Sizes.t n i ≤ R := Nat.le_mul_of_pos_left _ (by omega)
  have hsR := (h.good.lt i).le.trans htR
  have hVR : V ≤ R := hV.trans ((Nat.mul_le_mul_left cB hpt).trans
    (Nat.mul_le_mul_right (Sizes.t n i) (by omega : cB ≤ cB+1)))
  have hc := preparedCoreOriginsCost_poly (radius := radius) (L := L) hw ((hp.trans hpt).trans htR) hsR hVR
  exact hc.trans_eq (by dsimp only [R]; ring)

end IntegerMultBounds.MathlibTM2.Cost
