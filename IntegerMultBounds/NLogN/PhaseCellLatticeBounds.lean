module

public import IntegerMultBounds.NLogN.PhaseCellLatticeArgs
public import IntegerMultBounds.NLogN.PhaseCellCouplingLift

/-! Polynomial bounds for the natural lattice argument. These depend on
ordinary dimensions and lifted coordinates, without finite-check certificates. -/

@[expose] public section
namespace IntegerMultBounds.NLogN.PhaseCellRationalArgs

theorem nearestNatural_mul_le (s t j : ℕ) :
    s*nearestNatural s t j ≤ 2*t*j+s := by
  have hh := Nat.div_mul_le_self (2*t*j+s) (2*s)
  dsimp only [nearestNatural]
  nlinarith only [hh]

theorem naturalDistance_le_add (a b : ℕ) : naturalDistance a b ≤ a+b := by
  unfold naturalDistance
  omega

theorem lattice_coordinate_bounds {N s t u j k : ℕ} (hN : 1 ≤ N)
    (hs : s ≤ N) (ht : t ≤ N) (hu : u ≤ N) (hj : j ≤ 4*N^2) (hk : k ≤ 4*N^2) :
    2*t*j+s ≤ 16*N^3 ∧ 2*t*k+s ≤ 16*N^3 ∧
    s*nearestNatural s t j ≤ 16*N^3 ∧ s*nearestNatural s t k ≤ 16*N^3 ∧
    latticeDistance s t j k^2 ≤ 1024*N^6 ∧ latticeDistance s t k k^2 ≤ 1024*N^6 ∧
    latticeNumerator s t u j k ≤ 1024*N^7 := by
  have hN3 : N ≤ N^3 := by
    have hh : 1 ≤ N^2 := one_le_pow₀ hN
    nlinarith only [Nat.mul_le_mul_left N hh]
  have htj : t*j ≤ 4*N^3 := by
    calc _ ≤ N*(4*N^2) := Nat.mul_le_mul ht hj
         _ = _ := by ring
  have htk : t*k ≤ 4*N^3 := by
    calc _ ≤ N*(4*N^2) := Nat.mul_le_mul ht hk
         _ = _ := by ring
  have hidxj : 2*t*j+s ≤ 16*N^3 := by nlinarith only [htj,hs,hN3]
  have hidxk : 2*t*k+s ≤ 16*N^3 := by nlinarith only [htk,hs,hN3]
  have hnj := (nearestNatural_mul_le s t j).trans hidxj
  have hnk := (nearestNatural_mul_le s t k).trans hidxk
  have hdj : latticeDistance s t j k ≤ 32*N^3 := by
    have hh := naturalDistance_le_add (t*k) (s*nearestNatural s t j)
    change latticeDistance s t j k ≤ t*k+s*nearestNatural s t j at hh
    omega
  have hdk : latticeDistance s t k k ≤ 32*N^3 := by
    have hh := naturalDistance_le_add (t*k) (s*nearestNatural s t k)
    change latticeDistance s t k k ≤ t*k+s*nearestNatural s t k at hh
    omega
  have hdj2 : latticeDistance s t j k^2 ≤ 1024*N^6 := by
    calc _ ≤ (32*N^3)^2 := Nat.pow_le_pow_left hdj 2
         _ = _ := by ring
  have hdk2 : latticeDistance s t k k^2 ≤ 1024*N^6 := by
    calc _ ≤ (32*N^3)^2 := Nat.pow_le_pow_left hdk 2
         _ = _ := by ring
  refine ⟨hidxj,hidxk,hnj,hnk,hdj2,hdk2,?_⟩
  calc
    _ ≤ u*latticeDistance s t j k^2 := Nat.mul_le_mul_left u (Nat.sub_le _ _)
    _ ≤ N*(1024*N^6) := Nat.mul_le_mul hu hdj2
    _ = _ := by ring

theorem lifted_coordinate_bound {N s band i d : ℕ} (negative : Bool) (hN : 1 ≤ N)
    (hs : s ≤ N) (hb : band ≤ N) (hi : i ≤ N) (hd : d ≤ band) :
    i+band*s+d ≤ 4*N^2 ∧ liftedSource s band i ≤ 4*N^2 ∧
      liftedTarget negative s band i d ≤ 4*N^2 := by
  have hprod : band*s ≤ N^2 := by simpa only [pow_two] using Nat.mul_le_mul hb hs
  have hN2 : N ≤ N^2 := by nlinarith only [Nat.mul_le_mul_left N hN]
  have hsum : i+band*s+band ≤ 4*N^2 := by omega
  refine ⟨by omega,?_,(liftedTarget_le negative hd).trans hsum⟩
  dsimp only [liftedSource]
  omega

end IntegerMultBounds.NLogN.PhaseCellRationalArgs
