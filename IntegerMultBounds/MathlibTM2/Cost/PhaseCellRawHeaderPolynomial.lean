module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellSelectedFamilyInverseCaller
import Mathlib.Tactic.Linarith

/-! A structural polynomial bound for the raw caller's derived headers. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Cost
open IntegerMultBounds IntegerMultBounds.MathlibTM2.Fast.TableVM
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
  IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
  IntegerMultBounds.NLogN IntegerMultBounds.NLogN.PhaseCellDiscreteGeometry

theorem inverseExecutionExponent_poly {p l target N band Z : ℕ}
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hN : N ≤ Z) (hband : band ≤ Z) :
    inverseExecutionExponent p l target N band ≤ 100*Z := by
  have h₁ : Nat.size (8*p) ≤ 8*p := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₂ : Nat.size N ≤ N := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₃ : Nat.size (2*band+1) ≤ 2*band+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  unfold inverseExecutionExponent
  omega

theorem inverseCallerWordWidth_poly {p u l target s t Z : ℕ}
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (hband : PhaseCellBand.width p u ≤ Z) :
    inverseCallerWordWidth p u l target s t ≤ 100000*Z^2 := by
  have hE := inverseExecutionExponent_poly hZ hp hl htarget hs hband
  have hroom : inversePrecisionRoom p l target s (PhaseCellBand.width p u) ≤ 67000*Z := by
    unfold inversePrecisionRoom
    norm_num only [Nat.reducePow]
    omega
  have hsquare := Nat.pow_le_pow_left (show t+1 ≤ 2*Z by omega) 2
  have hZpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  have hwork : inverseCallerWorkspace p u l target s t ≤ 100000*Z^2 := by
    unfold inverseCallerWorkspace
    nlinarith only [hp,hu,hband,hroom,hsquare,hZpow,hZ]
  exact (Nat.size_le.mpr Nat.lt_two_pow_self).trans hwork

theorem inverseMasterValues_cuts_poly {p u l target s t a b Z : ℕ} [NeZero s]
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ Z) :
    ∀ i, inverseMasterValues p u l target s t a b i ≤ 32768*Z := by
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ Z :=
    (show (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s by
      simpa using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hs
  have hE := inverseExecutionExponent_poly hZ hp hl htarget hN hband
  intro i
  fin_cases i <;> simp [inverseMasterValues] <;> omega

theorem inverseMasterValues_poly {p u l target s t Z : ℕ} [NeZero s]
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (hband : PhaseCellBand.width p u ≤ Z) :
    ∀ i, inverseMasterValues p u l target s t 0 s i ≤ 32768*Z := by
  exact inverseMasterValues_cuts_poly hZ hp hu hl htarget hs ht (Nat.zero_le s) le_rfl hband

theorem inverseHeaderCosts_poly {atoms W H : ℕ} (values : Fin 10 → ℕ)
    (hH : 1 ≤ H) (ha : atoms ≤ H) (hW : W ≤ H) (hv : ∀ i, values i ≤ H) :
    atoms*tblC W 0+inverseMasterCopyCost W values+inverseReleaseCost W values ≤ 20000*H^3 := by
  have hcopy := List.sum_le_length_nsmul
    ((List.finRange 10).map (fun i => 6*values i+11*W+6)) (23*H) (by
      intro x hx
      obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
      have := hv i
      omega)
  have hvalues := List.sum_le_length_nsmul ((List.finRange 10).map values) H (by
    intro x hx
    obtain ⟨i,_,rfl⟩ := List.mem_map.mp hx
    exact hv i)
  simp only [List.length_map,List.length_finRange,smul_eq_mul] at hcopy hvalues
  have htable : tblC W 0 ≤ 800*H^2 := by
    have hsquare := Nat.pow_le_pow_left (show W+4 ≤ 5*H by omega) 2
    unfold tblC
    nlinarith only [hsquare]
  have hprod := Nat.mul_le_mul (show atoms+17 ≤ 18*H by omega) htable
  have hpow : H ≤ H^3 := Nat.le_self_pow (by decide) H
  unfold inverseMasterCopyCost inverseReleaseCost
  nlinarith only [hcopy,hvalues,hprod,hpow,hH]

theorem inverseCallerHeaders_cuts_poly {p u l target s t a b Z : ℕ} [NeZero s]
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (ha : a ≤ s) (hb : b ≤ s) (hband : PhaseCellBand.width p u ≤ Z) :
    let W := inverseCallerWordWidth p u l target s t
    inverseScalarAtoms p s t u a b*tblC W 0+
      inverseMasterCopyCost W (inverseMasterValues p u l target s t a b)+
      inverseReleaseCost W (inverseMasterValues p u l target s t a b) ≤
        20000*(100000*Z^2)^3 := by
  dsimp only
  have hN : (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ Z :=
    (show (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤ s by
      simpa using (haloBoundary s t (PhaseCellBand.width p u) a b).card_le_univ).trans hs
  have h₁ : Nat.size (8*p) ≤ 8*p := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₂ : Nat.size (haloBoundary s t (PhaseCellBand.width p u) a b).card ≤
      (haloBoundary s t (PhaseCellBand.width p u) a b).card := Nat.size_le.mpr Nat.lt_two_pow_self
  have h₃ : Nat.size (2*PhaseCellBand.width p u+1) ≤ 2*PhaseCellBand.width p u+1 :=
    Nat.size_le.mpr Nat.lt_two_pow_self
  have hatoms : inverseScalarAtoms p s t u a b ≤ 200*Z := by
    dsimp only [inverseScalarAtoms,inversePrecisionAtoms]
    omega
  have hpow : Z ≤ Z^2 := Nat.le_self_pow (by decide) Z
  apply inverseHeaderCosts_poly _ (by nlinarith only [hZ,hpow])
    (hatoms.trans (by nlinarith only [hpow]))
    (inverseCallerWordWidth_poly hZ hp hu hl htarget hs ht hband)
  intro i
  exact (inverseMasterValues_cuts_poly hZ hp hu hl htarget hs ht ha hb hband i).trans
    (by nlinarith only [hpow])

theorem inverseCallerHeaders_poly {p u l target s t Z : ℕ} [NeZero s]
    (hZ : 1 ≤ Z) (hp : p ≤ Z) (hu : u ≤ Z) (hl : l ≤ Z) (htarget : target ≤ Z)
    (hs : s ≤ Z) (ht : t ≤ Z) (hband : PhaseCellBand.width p u ≤ Z) :
    let W := inverseCallerWordWidth p u l target s t
    inverseScalarAtoms p s t u 0 s*tblC W 0+
      inverseMasterCopyCost W (inverseMasterValues p u l target s t 0 s)+
      inverseReleaseCost W (inverseMasterValues p u l target s t 0 s) ≤
        20000*(100000*Z^2)^3 := by
  exact inverseCallerHeaders_cuts_poly hZ hp hu hl htarget hs ht (Nat.zero_le s) le_rfl hband

end IntegerMultBounds.MathlibTM2.Cost
