import IntegerMultBounds.Machine.Hoare
import IntegerMultBounds.NLogN.Approx
import IntegerMultBounds.NLogN.FixedOps
import Mathlib.Data.Nat.Size

/-! The statement of the paper's signed ring product
(`lem:signed-ring-product`, §6), on the literal machine model and in the
paper's formats. The header is `Γ(p)Γ(r)Γ(w)` with the self-delimiting code
`Γ(v) = 0^(b_v - 1) bin_(b_v)(v)` (eq. `integer-descriptor-code`, §2). A
polynomial of `ℛ_r` is a record of `r` coefficients in coefficient order,
each the real then the imaginary numerator as a signed `w`-bit
two's-complement word, most significant bit first (the component format of
`prop:simultaneous-layer`). The output is `Q_p(fg/r)` in the same format,
with `Q_p` truncation toward zero (`NLogN.rhoC`) and `fg` the product modulo
`y^r + 1` (`NLogN.negacyclicMul`).

Only definitions are made here: `SignedRingProduct M Cw T` says the program
`M` meets the lemma with time bound `T r p`; `paperTarget` is the paper's
bound `O(r p log (r p))`, and `polylogTarget k` allows an extra factor
`(log log (r p))^k`, which the packed-product margin of the cost table absorbs
(`Machine.PackedMultiplierPolylogBudget`). -/

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-! ### Binary words, most significant bit first -/

/-- The `n` low bits of `v`, most significant first. -/
def msbBits : ℕ → ℕ → List Bool
  | 0, _ => []
  | n + 1, v => (v / 2 ^ n % 2 = 1) :: msbBits n v

@[simp] theorem length_msbBits (n v : ℕ) : (msbBits n v).length = n := by
  induction n <;> simp [msbBits, *]

theorem binaryValue_msbBits : ∀ n v : ℕ, binaryValue (msbBits n v) = v % 2 ^ n
  | 0, v => by simp [msbBits, binaryValue, Nat.mod_one]
  | n + 1, v => by
    rw [msbBits, binaryValue, length_msbBits, binaryValue_msbBits n v, pow_succ, Nat.mod_mul]
    rcases Nat.mod_two_eq_zero_or_one (v / 2 ^ n) with h | h <;> simp [h] <;> ring

/-! ### The self-delimiting code -/

/-- `Γ(v) = 0^(b_v - 1) bin_(b_v)(v)` with `b_v = ⌊log₂ v⌋ + 1`. -/
def gamma (v : ℕ) : List Bool := List.replicate (Nat.size v - 1) false ++ msbBits (Nat.size v) v

theorem length_gamma {v : ℕ} (hv : 1 ≤ v) : (gamma v).length = 2 * Nat.size v - 1 := by
  have := Nat.size_pos.mpr hv
  simp [gamma]; omega

/-- Read one code: count leading zeros, then that many more bits after the first one. -/
def gammaRead (bs : List Bool) : Option (ℕ × List Bool) :=
  let z := (bs.takeWhile (· = false)).length
  let rest := bs.drop z
  if rest.length < z + 1 then none
  else some (binaryValue (rest.take (z + 1)), rest.drop (z + 1))

/-- The header of the signed ring product. -/
def header (p r w : ℕ) : List Bool := gamma p ++ gamma r ++ gamma w

/-! ### The component format -/

/-- A signed integer as a `w`-bit two's-complement word, most significant bit first. -/
def compWord (w : ℕ) (z : ℤ) : List Bool := msbBits w (z % 2 ^ w).toNat

/-- The signed value of a two's-complement word written most significant bit first. -/
def compValue (bs : List Bool) : ℤ :=
  (binaryValue bs : ℤ) - if bs.headD false then 2 ^ bs.length else 0

/-- A polynomial record: for each coefficient, the real then the imaginary numerator. -/
def record {r : ℕ} (w : ℕ) (re im : Fin r → ℤ) : List Bool :=
  (List.finRange r).flatMap fun j => compWord w (re j) ++ compWord w (im j)

/-- The grid polynomial with numerators `re`, `im` at `p` fractional bits. -/
noncomputable def gridPoly {r : ℕ} (p : ℕ) (re im : Fin r → ℤ) : Fin r → ℂ :=
  fun j => ⟨(re j : ℝ) / 2 ^ p, (im j : ℝ) / 2 ^ p⟩

/-- Disk grid numerators: every coefficient has modulus at most one. -/
def DiskGrid {r : ℕ} (p : ℕ) (re im : Fin r → ℤ) : Prop := ∀ j, re j ^ 2 + im j ^ 2 ≤ (2 : ℤ) ^ (2 * p)

/-- The numerators of `Q_p(fg/r)`. -/
noncomputable def productRe {r : ℕ} (p : ℕ) (f g : Fin r → ℂ) (j : Fin r) : ℤ :=
  rho0 (2 ^ p * (negacyclicMul f g j / r).re)

noncomputable def productIm {r : ℕ} (p : ℕ) (f g : Fin r → ℂ) (j : Fin r) : ℤ :=
  rho0 (2 ^ p * (negacyclicMul f g j / r).im)

theorem gridPoly_product {r : ℕ} (p : ℕ) (f g : Fin r → ℂ) :
    gridPoly p (productRe p f g) (productIm p f g) = fun j => rhoC p (negacyclicMul f g j / r) := rfl

/-! ### Tapes -/

/-- A word from cell zero, blank elsewhere. -/
def wordAt {a : ℕ} (bs : List Bool) : ℤ → Fin (a + 4) := wordTape (bs.map bitSymbol)

/-- The banks before and after: header on tape 0, operands on tapes 1 and 2, the output on
tape 3, every other tape blank, every head at cell zero. -/
def bank {t a : ℕ} (hdr f g out : List Bool) : Tapes t a :=
  ⟨fun _ => 0, fun i => if i.val = 0 then wordAt hdr else if i.val = 1 then wordAt f
    else if i.val = 2 then wordAt g else if i.val = 3 then wordAt out else fun _ => blank⟩

/-- `M` meets the signed ring product lemma for width constant `Cw` within `T r p` steps. -/
def Meets {t q a : ℕ} (M : Program t q a) (Cw : ℕ) (T : ℕ → ℕ → ℕ) : Prop :=
  ∀ (p ℓ w : ℕ) (fr fi gr gi : Fin (2 ^ ℓ) → ℤ),
    1 ≤ ℓ → 2 ≤ p → 2 ^ ℓ < 2 ^ p → p + 2 ≤ w → w ≤ Cw * p →
    DiskGrid p fr fi → DiskGrid p gr gi →
    HoareTime M (· = bank (header p (2 ^ ℓ) w) (record w fr fi) (record w gr gi) [])
      (· = bank (header p (2 ^ ℓ) w) (record w fr fi) (record w gr gi)
        (record w (productRe p (gridPoly p fr fi) (gridPoly p gr gi))
          (productIm p (gridPoly p fr fi) (gridPoly p gr gi))))
      (T (2 ^ ℓ) p)

/-- The paper's statement: a fixed machine within `O(r p log (r p))` steps. -/
def paperTarget : Prop :=
  ∀ Cw : ℕ, 2 ≤ Cw → ∃ (t q a : ℕ) (M : Program t q a) (C : ℕ), 4 ≤ t ∧
    Meets M Cw fun r p => C * (r * p) * (Nat.log 2 (r * p) + 1)

/-- The statement with an extra `(log log (r p))^k` factor. -/
def polylogTarget (k : ℕ) : Prop :=
  ∀ Cw : ℕ, 2 ≤ Cw → ∃ (t q a : ℕ) (M : Program t q a) (C : ℕ), 4 ≤ t ∧
    Meets M Cw fun r p => C * (r * p) * (Nat.log 2 (r * p) + 1) * (Nat.log 2 (Nat.log 2 (r * p) + 1) + 1) ^ k

end IntegerMultBounds.Spec.SignedRingProduct
