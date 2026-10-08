import IntegerMultBounds.NLogN.DFT

/-! The two-dimensional reduction of cyclic convolution. Proved: convolution on
any finite additive group transports along additive isomorphisms, so by the
Chinese remainder theorem a length `m * n` cyclic convolution with coprime
`m, n` is a convolution on `ZMod m × ZMod n`; the two-dimensional transform
factors as row transforms followed by column transforms and satisfies the
convolution theorem. No cost accounting or algorithm is part of this file. -/

namespace IntegerMultBounds.NLogN

variable {R : Type*} [CommRing R]

/-- Convolution on an arbitrary finite additive group. -/
def convG {G : Type*} [AddCommGroup G] [Fintype G] (a b : G → R) : G → R :=
  fun k => ∑ i : G, a i * b (k - i)

/-- Convolution transports along any additive isomorphism. -/
theorem convG_comp_symm {G H : Type*} [AddCommGroup G] [Fintype G]
    [AddCommGroup H] [Fintype H] (e : G ≃+ H) (a b : G → R) :
    convG (a ∘ e.symm) (b ∘ e.symm) = convG a b ∘ e.symm := by
  funext k
  simp only [convG, Function.comp]
  refine Fintype.sum_equiv e.symm.toEquiv (fun i => a (e.symm i) * b (e.symm (k - i)))
    (fun i => a i * b (e.symm k - i)) fun i => ?_
  simp [map_sub]

theorem cconv_eq_convG {N : ℕ} [NeZero N] (a b : ZMod N → R) : cconv a b = convG a b := rfl

variable {m n : ℕ} [NeZero m] [NeZero n]

/-- Two-dimensional cyclic convolution. -/
def cconv2 (a b : ZMod m × ZMod n → R) : ZMod m × ZMod n → R :=
  fun k => ∑ i : ZMod m × ZMod n, a i * b (k - i)

theorem cconv2_eq_convG (a b : ZMod m × ZMod n → R) : cconv2 a b = convG a b := rfl

/-- Two-dimensional transform with separate roots for the two axes. -/
def dft2 (ζ₁ ζ₂ : R) (a : ZMod m × ZMod n → R) : ZMod m × ZMod n → R :=
  fun k => ∑ j : ZMod m × ZMod n, ζ₁ ^ (j.1 * k.1).val * ζ₂ ^ (j.2 * k.2).val * a j

/-- A two-dimensional transform is `m` column transforms followed by `n` row transforms. -/
theorem dft2_eq_rows_cols (ζ₁ ζ₂ : R) (a : ZMod m × ZMod n → R) :
    dft2 ζ₁ ζ₂ a = fun k => dft ζ₁ (fun i => dft ζ₂ (fun j => a (i, j)) k.2) k.1 := by
  funext k
  simp only [dft2, dft, Fintype.sum_prod_type, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  ring

/-- Convolution theorem in two dimensions. -/
theorem dft2_cconv2 {ζ₁ ζ₂ : R}
    (hζ₁ : IsPrimitiveRoot ζ₁ m) (hζ₂ : IsPrimitiveRoot ζ₂ n) (a b : ZMod m × ZMod n → R) :
    dft2 ζ₁ ζ₂ (cconv2 a b) = fun k => dft2 ζ₁ ζ₂ a k * dft2 ζ₁ ζ₂ b k := by
  funext k
  simp only [dft2, cconv2]
  rw [Finset.sum_mul_sum]
  simp only [Finset.mul_sum]
  conv_lhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Equiv.sum_comp (Equiv.addLeft i)]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Equiv.coe_addLeft, add_sub_cancel_left, Prod.fst_add, Prod.snd_add, add_mul,
    pow_val_add hζ₁, pow_val_add hζ₂]
  ring

/-- Reindex a length `m * n` vector by the Chinese remainder isomorphism. -/
def toGrid (hmn : Nat.Coprime m n) (a : ZMod (m * n) → R) :
    ZMod m × ZMod n → R :=
  a ∘ (ZMod.chineseRemainder hmn).symm

/-- A coprime-length cyclic convolution is a two-dimensional cyclic convolution. -/
theorem toGrid_cconv (hmn : Nat.Coprime m n) (a b : ZMod (m * n) → R) :
    toGrid hmn (cconv a b) = cconv2 (toGrid hmn a) (toGrid hmn b) := by
  have : NeZero (m * n) := ⟨Nat.mul_ne_zero (NeZero.ne m) (NeZero.ne n)⟩
  rw [toGrid, toGrid, toGrid, cconv_eq_convG, cconv2_eq_convG]
  exact (convG_comp_symm (ZMod.chineseRemainder hmn).toAddEquiv a b).symm

theorem dft2_toGrid_cconv (hmn : Nat.Coprime m n) {ζ₁ ζ₂ : R}
    (hζ₁ : IsPrimitiveRoot ζ₁ m) (hζ₂ : IsPrimitiveRoot ζ₂ n) (a b : ZMod (m * n) → R) :
    dft2 ζ₁ ζ₂ (toGrid hmn (cconv a b)) =
      fun k => dft2 ζ₁ ζ₂ (toGrid hmn a) k * dft2 ζ₁ ζ₂ (toGrid hmn b) k := by
  rw [toGrid_cconv hmn, dft2_cconv2 hζ₁ hζ₂]

end IntegerMultBounds.NLogN
