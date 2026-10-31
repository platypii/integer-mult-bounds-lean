module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCoreControlCostLedger
public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial

/-! Scalar control work is polynomial apart from the already priced inverse
header construction. Payload and replica charges remain outside this bound. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Mult
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement.SupplierSetupPlan
  IntegerMultBounds.NLogN.PhaseCellMatrix IntegerMultBounds.MathlibTM2.Fast.TableVM
variable {A s : ℕ} [NeZero s]

theorem inverseMasterCopyCost_eq (W : ℕ) (values : Fin 10 → ℕ) :
    inverseMasterCopyCost W values = 6*(∑ i, values i)+110*W+61 := by
  unfold inverseMasterCopyCost
  rw [←List.ofFn_eq_map]
  simp only [List.sum_ofFn,Finset.sum_add_distrib,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,smul_eq_mul,←Finset.mul_sum]
  omega

theorem supplierMasterCopyCost_eq (r : PackedNormalizedJob A s) :
    r.masterCopyCost = 4*(∑ i, r.factoryMasters i)+41 := by
  simp only [PackedNormalizedJob.masterCopyCost,List.sum_ofFn,Finset.sum_add_distrib,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul,←Finset.mul_sum]

/-- One envelope handles both scalar time and scalar stock. The expensive
header bill is supplied by the existing raw-header theorem. -/
theorem coreControlCosts_le_header (V R H : ℕ) (r : PackedNormalizedJob A s) (hR : 1 ≤ R)
    (hparams : ∀ x ∈ [r.p,r.u,r.l,r.targetOut,s,r.t,r.a,r.b,r.Bcore,r.V,r.W,V,r.radius,r.q], x ≤ R)
    (hheaders : inverseScalarAtoms r.p s r.t r.u r.a r.b*tblC r.Bcore 0+
      inverseMasterCopyCost r.Bcore r.factoryMasters ≤ H) :
    (coreControlTimeCost V r+42*r.inputSharedStock ≤ 1000*H+1000000000*R^2) ∧
    (coreControlStock V r+62*r.inputSharedStock ≤ 1000*H+1000000000*R^2) := by
  have hp := hparams r.p (by simp)
  have hu := hparams r.u (by simp)
  have hl := hparams r.l (by simp)
  have htarget := hparams r.targetOut (by simp)
  have hs := hparams s (by simp)
  have ht := hparams r.t (by simp)
  have ha := hparams r.a (by simp)
  have hb := hparams r.b (by simp)
  have hB := hparams r.Bcore (by simp)
  have hV := hparams r.V (by simp)
  have hW := hparams r.W (by simp)
  have hwidth := hparams V (by simp)
  have hradius := hparams r.radius (by simp)
  have hq := hparams r.q (by simp)
  have hR2 : R ≤ R^2 := Nat.le_self_pow (by decide) R
  have hunit : 1 ≤ R^2 := hR.trans hR2
  have hcopy : inverseMasterCopyCost r.Bcore r.factoryMasters ≤ H := by omega
  rw [inverseMasterCopyCost_eq] at hcopy
  have hmasters : (List.ofFn r.factoryMasters).sum ≤ H := by rw [List.sum_ofFn]; omega
  have hmasterCopy : r.masterCopyCost ≤ H := by rw [supplierMasterCopyCost_eq]; omega
  have hhalo : r.b-r.a ≤ R := (Nat.sub_le _ _).trans hb
  have hcore : coreLength s r.coreWidth r.k ≤ R :=
    (Nat.min_le_right _ _).trans ((Nat.sub_le _ _).trans hs)
  have hhaloWord : (r.b-r.a)*r.W ≤ R^2 := by
    simpa only [pow_two] using Nat.mul_le_mul hhalo hW
  have hprodA := Nat.mul_le_mul ha (show 4*r.V+10 ≤ 4*R+10 by omega)
  have hprodHalo := Nat.mul_le_mul hhalo (show 4*r.V+10 ≤ 4*R+10 by omega)
  have hgeometry : factoryGeometryCost r.a r.b r.V ≤ 100*R^2 := by
    unfold factoryGeometryCost
    nlinarith only [hprodA,hprodHalo,ha,hb,hhalo,hV,hR2,hunit]
  have hheader : r.headerSharedCost ≤ 40*R^2 := by
    unfold PackedNormalizedJob.headerSharedCost
    nlinarith only [hhaloWord,hW,hp,hR2,hunit]
  have hsum : coreLength s r.coreWidth r.k+r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b ≤ 9*R := by omega
  have hprod := Nat.mul_le_mul hsum (show 4*r.Bcore+10 ≤ 4*R+10 by omega)
  have hguard := Nat.mul_le_mul hradius (show 4*r.V+10 ≤ 4*R+10 by omega)
  have hinputTime : r.inputSharedTimeCost ≤ 2*H+1000*R^2 := by
    unfold PackedNormalizedJob.inputSharedTimeCost
    nlinarith only [hmasterCopy,hgeometry,hheader,hprod,hguard,hV,hB,hR2,hunit]
  have hinputStock : r.inputSharedStock ≤ 2*H+1000*R^2 := by
    unfold PackedNormalizedJob.inputSharedStock
    nlinarith only [hmasterCopy,hheader,ha,hb,hV,hB,hR2,hunit]
  have hsumParams : r.p+r.u+r.l+r.targetOut+s+r.t+r.a+r.b ≤ 8*R := by omega
  have hprodParams := Nat.mul_le_mul hsumParams (show 4*r.Bcore+10 ≤ 4*R+10 by omega)
  have hgenerate : generateSupplierMastersCost r ≤ H+1000*R^2 := by
    unfold generateSupplierMastersCost
    nlinarith only [hheaders,hprodParams,hB,hR2,hunit]
  have hgeometryWidth : supplierGeometryWidthCost r ≤ 200000*R := by
    unfold supplierGeometryWidthCost weightWidthCost
    norm_num only [Nat.reducePow]
    omega
  have hweight : weightWidthCost (2^15*r.p) r.q (2*r.q+8) r.t r.u ≤ 200000*R := by
    unfold supplierGeometryWidthCost at hgeometryWidth
    omega
  have htime : timeCost r ≤ H+300000*R^2 := by
    unfold timeCost
    nlinarith only [hgenerate,hgeometryWidth,hB,hR2,hunit]
  have hstock : stock r ≤ 3*H+4000000*R^2 := by
    unfold stock
    nlinarith only [hheaders,hweight,hB,hq,hR2,hunit]
  have hread : readSupplierEndpointsCost V r.a (r.b-r.a) ≤ 100*R := by
    unfold readSupplierEndpointsCost
    omega
  have hretire : retirementCost r ≤ 2*H+30*R := by
    unfold retirementCost
    omega
  constructor
  · unfold coreControlTimeCost
    nlinarith only [hread,htime,hinputTime,hretire,ha,hb,hinputStock,hR2,hunit]
  · unfold coreControlStock
    nlinarith only [hread,hstock,hinputStock,hR2,hunit]

end IntegerMultBounds.MathlibTM2.Cost
