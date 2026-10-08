import IntegerMultBounds.NLogN.MultidimD
import Mathlib.Data.ZMod.QuotientRing

/-! The `d`-fold Agarwal-Cooley reduction. Proved: for pairwise coprime lengths
`s i`, a cyclic convolution of length `∏ s i` transports along the Chinese
remainder isomorphism to the convolution on `∏ ZMod (s i)`, so the
`d`-dimensional transform computes it and, over a domain, determines it
uniquely; strictly increasing primes are pairwise coprime. No data layout,
sorting, or cost accounting is part of this file. -/

namespace IntegerMultBounds.NLogN

variable {R : Type*} [CommRing R] {d : ℕ} {s : Fin d → ℕ} [∀ i, NeZero (s i)]

instance : NeZero (∏ i, s i) :=
  NeZero.of_pos (Finset.prod_pos fun i _ => Nat.pos_of_ne_zero (NeZero.ne (s i)))

/-- Rearrange a length-`∏ s i` vector as a `d`-dimensional grid. -/
noncomputable def toGridD (hs : Pairwise (Function.onFun Nat.Coprime s)) (a : ZMod (∏ i, s i) → R) :
    ((i : Fin d) → ZMod (s i)) → R :=
  a ∘ (ZMod.prodEquivPi s hs).symm

/-- Read a `d`-dimensional grid back as a length-`∏ s i` vector. -/
noncomputable def ofGridD (hs : Pairwise (Function.onFun Nat.Coprime s)) (u : ((i : Fin d) → ZMod (s i)) → R) :
    ZMod (∏ i, s i) → R :=
  u ∘ ZMod.prodEquivPi s hs

omit [CommRing R] [∀ i, NeZero (s i)] in
@[simp] theorem ofGridD_toGridD (hs : Pairwise (Function.onFun Nat.Coprime s)) (a : ZMod (∏ i, s i) → R) :
    ofGridD hs (toGridD hs a) = a := by
  funext k
  simp [ofGridD, toGridD]

omit [CommRing R] [∀ i, NeZero (s i)] in
@[simp] theorem toGridD_ofGridD (hs : Pairwise (Function.onFun Nat.Coprime s))
    (u : ((i : Fin d) → ZMod (s i)) → R) : toGridD hs (ofGridD hs u) = u := by
  funext k
  simp [ofGridD, toGridD]

omit [CommRing R] [∀ i, NeZero (s i)] in
theorem toGridD_injective (hs : Pairwise (Function.onFun Nat.Coprime s)) :
    Function.Injective (toGridD (R := R) hs) := by
  intro a b h
  rw [← ofGridD_toGridD hs a, h, ofGridD_toGridD]

/-- Agarwal-Cooley: cyclic convolution becomes `d`-dimensional convolution. -/
theorem toGridD_cconv (hs : Pairwise (Function.onFun Nat.Coprime s)) (a b : ZMod (∏ i, s i) → R) :
    toGridD hs (cconv a b) = convG (toGridD hs a) (toGridD hs b) := by
  unfold toGridD
  rw [cconv_eq_convG]
  exact (convG_comp_symm (ZMod.prodEquivPi s hs).toAddEquiv a b).symm

theorem dftD_toGridD_cconv (hs : Pairwise (Function.onFun Nat.Coprime s)) {ζ : Fin d → R}
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (s i)) (a b : ZMod (∏ i, s i) → R) :
    dftD ζ (toGridD hs (cconv a b)) =
      fun k => dftD ζ (toGridD hs a) k * dftD ζ (toGridD hs b) k := by
  rw [toGridD_cconv, dftD_convG hζ]

theorem dftD_injective [IsDomain R] {ζ : Fin d → R}
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (s i)) (hS : ((∏ i, s i : ℕ) : R) ≠ 0) :
    Function.Injective (dftD (N := s) ζ) := by
  intro u v h
  have hu := dftD_dftD hζ u
  have hv := dftD_dftD hζ v
  rw [h, hv] at hu
  have hP : (∏ i, (s i : R)) ≠ 0 := by rwa [Nat.cast_prod] at hS
  funext k
  have := congrFun hu (-k)
  simp only [neg_neg] at this
  exact (mul_left_cancel₀ hP this).symm

/-- A vector whose grid transform is the pointwise product of the grid
transforms is the cyclic convolution. -/
theorem cconv_eq_of_dftD [IsDomain R] (hs : Pairwise (Function.onFun Nat.Coprime s)) {ζ : Fin d → R}
    (hζ : ∀ i, IsPrimitiveRoot (ζ i) (s i)) (hS : ((∏ i, s i : ℕ) : R) ≠ 0)
    (a b c : ZMod (∏ i, s i) → R)
    (hc : dftD ζ (toGridD hs c) = fun k => dftD ζ (toGridD hs a) k * dftD ζ (toGridD hs b) k) :
    c = cconv a b := by
  apply toGridD_injective hs
  apply dftD_injective hζ hS
  rw [hc, dftD_toGridD_cconv hs hζ]

/-- Strictly increasing primes are pairwise coprime. -/
theorem pairwise_coprime_of_primes_strictMono (t : Fin d → ℕ) (hp : ∀ i, (t i).Prime)
    (hmono : StrictMono t) : Pairwise (Function.onFun Nat.Coprime t) := by
  intro i j hij
  exact (Nat.coprime_primes (hp i) (hp j)).2 fun h => hij (hmono.injective h)

end IntegerMultBounds.NLogN
