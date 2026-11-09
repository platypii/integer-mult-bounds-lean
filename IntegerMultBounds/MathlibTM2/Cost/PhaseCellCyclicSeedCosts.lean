module

public import IntegerMultBounds.MathlibTM2.Cost.PhaseCellRawHeaderPolynomial
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellCyclicSeedLayout

/-! Price the actual per-origin master generator and retirement from ordinary
dimensions. The same header estimate pays time and peak workspace. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem cyclicSeedCosts_poly {B p u l target s t a n Z : ℕ} [NeZero s]
    (hZ : 1 ≤ Z) (hB : B ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z)
    (htarget : target ≤ Z) (hs : s ≤ Z) (ht : t ≤ Z) (hfit : a+n ≤ s)
    (hband : PhaseCellBand.width p u ≤ Z) :
    CyclicSeedLayout.timeCost B p u l target s t a n+
        (2*(List.ofFn (inverseMasterValues p u l target s t a (a+n))).sum+21) ≤
      (60000*32768^3+1000000)*Z^3 ∧
    CyclicSeedLayout.workspace B p u l target s t a n ≤
      (60000*32768^3+1000000)*Z^3 := by
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card ≤ Z :=
    (show (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card ≤ s by
      simpa using (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card_le_univ).trans hs
  have h₁ : Nat.size (8*p) ≤ 8*p := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₂ : Nat.size (haloBoundary s t (PhaseCellBand.width p u) a (a+n)).card ≤ Z :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans hN
  have h₃ : Nat.size (2*PhaseCellBand.width p u+1) ≤ 2*Z+1 :=
    (Nat.size_le.mpr Nat.lt_two_pow_self).trans (by omega)
  have hatoms : inverseScalarAtoms p s t u a (a+n) ≤ 200*Z := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have hv := inverseMasterValues_cuts_poly (a := a) (b := a+n) hZ hp hu hl htarget hs ht (by omega) hfit hband
  have hheader := inverseHeaderCosts_poly (inverseMasterValues p u l target s t a (a+n))
    (show 1 ≤ 32768*Z by omega) (hatoms.trans (by omega)) (hB.trans (by omega)) hv
  have hbase : inverseScalarAtoms p s t u a (a+n)*tblC B 0+
      inverseMasterCopyCost B (inverseMasterValues p u l target s t a (a+n)) ≤ 20000*(32768*Z)^3 := by
    omega
  have hsum := List.sum_le_length_nsmul
    (List.ofFn (inverseMasterValues p u l target s t a (a+n))) (32768*Z)
    (by intro x hx; obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hx; exact hv i)
  simp only [List.length_ofFn,smul_eq_mul] at hsum
  have hZ₂ : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have hZ₃ : Z^2 ≤ Z^3 := Nat.pow_le_pow_right hZ (by decide)
  have hqueue : (p+u+l+target+s+t+a+(a+n))*(4*B+10)+278*B+314 ≤ 1000*Z^2 := by
    have hm := Nat.mul_le_mul (show p+u+l+target+s+t+a+(a+n) ≤ 8*Z by omega)
      (show 4*B+10 ≤ 14*Z by omega)
    nlinarith only [hm,hB,hZ₂,hZ]
  constructor
  · unfold CyclicSeedLayout.timeCost generateInverseMastersCost
    nlinarith only [hqueue,hbase,hsum,hZ₂,hZ₃,hZ]
  · unfold CyclicSeedLayout.workspace
    nlinarith only [hbase,hB,hZ₂,hZ₃,hZ]

end IntegerMultBounds.MathlibTM2.Cost
