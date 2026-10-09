import Mathlib.Algebra.Polynomial.Div
import Mathlib.Tactic

/-! The twisted transform behind Schönhage–Strassen, over any commutative
ring, in the form a tape executes it: lists of length `2^k` whose halves stay
contiguous. One forward layer maps `a = a₀ ++ a₁` modulo `X^(2K) - ζ²` to the
two residues `a₀ + ζ a₁` modulo `X^K - ζ` and `a₀ - ζ a₁` modulo `X^K + ζ`;
the roots are powers `ψ^e` of one element with `ψ^H = -1`, so in
`ℤ/(2^N + 1)` every multiplication is a shift. The inverse layer recombines
without dividing by two. Proved: inverse of the pointwise product of two
forward transforms is `2^k` times the product modulo `X^(2^k) - ψ^e`
(`inv_fwd_mul`); no division by two and no primitive-root hypothesis beyond
`ψ^H = -1` is used. -/

namespace IntegerMultBounds.Schoenhage

open Polynomial

variable {R : Type*} [CommRing R]

/-- A coefficient list, least significant first, as a polynomial. -/
noncomputable def poly : List R → R[X]
  | [] => 0
  | c :: cs => C c + X * poly cs

@[simp] theorem poly_nil : poly ([] : List R) = 0 := rfl

@[simp] theorem poly_cons (c : R) (cs : List R) : poly (c :: cs) = C c + X * poly cs := rfl

theorem poly_append (l₁ l₂ : List R) : poly (l₁ ++ l₂) = poly l₁ + X ^ l₁.length * poly l₂ := by
  induction l₁ with
  | nil => simp
  | cons c cs ih => simp [ih, pow_succ]; ring

theorem poly_map_mul (z : R) (l : List R) : poly (l.map (z * ·)) = C z * poly l := by
  induction l with
  | nil => simp
  | cons c cs ih => simp [ih, C_mul]; ring

theorem poly_zipWith_add : ∀ (l₁ l₂ : List R), l₁.length = l₂.length →
    poly (List.zipWith (· + ·) l₁ l₂) = poly l₁ + poly l₂
  | [], [], _ => by simp
  | c :: cs, d :: ds, h => by
    simp only [List.zipWith_cons_cons, poly_cons, List.length_cons, add_left_inj] at h ⊢
    rw [poly_zipWith_add cs ds h, C_add]; ring

theorem poly_zipWith_sub : ∀ (l₁ l₂ : List R), l₁.length = l₂.length →
    poly (List.zipWith (· - ·) l₁ l₂) = poly l₁ - poly l₂
  | [], [], _ => by simp
  | c :: cs, d :: ds, h => by
    simp only [List.zipWith_cons_cons, poly_cons, List.length_cons, add_left_inj] at h ⊢
    rw [poly_zipWith_sub cs ds h, C_sub]; ring

section Transform

variable (ψ : R) (H : ℕ)

/-- Butterfly sums `u + z v`. -/
def bsum (z : R) (u v : List R) : List R := List.zipWith (· + ·) u (v.map (z * ·))

/-- Butterfly differences `u - z v`. -/
def bdiff (z : R) (u v : List R) : List R := List.zipWith (· - ·) u (v.map (z * ·))

/-- The forward transform of a length `2^k` list modulo `X^(2^k) - ψ^e`. -/
def fwd : ℕ → ℕ → List R → List R
  | 0, _, a => a
  | k + 1, e, a =>
    fwd k (e / 2) (bsum (ψ ^ (e / 2)) (a.take (2 ^ k)) (a.drop (2 ^ k))) ++
      fwd k (e / 2 + H) (bdiff (ψ ^ (e / 2)) (a.take (2 ^ k)) (a.drop (2 ^ k)))

/-- The unscaled inverse transform; `ψ ^ (2H - e/2)` inverts `ψ ^ (e/2)`. -/
def inv : ℕ → ℕ → List R → List R
  | 0, _, c => c
  | k + 1, e, c =>
    let P := inv k (e / 2) (c.take (2 ^ k))
    let Q := inv k (e / 2 + H) (c.drop (2 ^ k))
    List.zipWith (· + ·) P Q ++ (List.zipWith (· - ·) P Q).map (ψ ^ (2 * H - e / 2) * ·)

theorem length_bsum (z : R) (u v : List R) (h : u.length = v.length) :
    (bsum z u v).length = u.length := by simp [bsum, h]

theorem length_bdiff (z : R) (u v : List R) (h : u.length = v.length) :
    (bdiff z u v).length = u.length := by simp [bdiff, h]

theorem length_fwd : ∀ (k e : ℕ) (a : List R), a.length = 2 ^ k → (fwd ψ H k e a).length = 2 ^ k
  | 0, _, a, h => h
  | k + 1, e, a, h => by
    have h0 : (a.take (2 ^ k)).length = 2 ^ k := by simp only [List.length_take, h, pow_succ]; omega
    have h1 : (a.drop (2 ^ k)).length = 2 ^ k := by simp only [List.length_drop, h, pow_succ]; omega
    simp only [fwd, List.length_append]
    rw [length_fwd k _ _ (by rw [length_bsum _ _ _ (h0.trans h1.symm), h0]),
      length_fwd k _ _ (by rw [length_bdiff _ _ _ (h0.trans h1.symm), h0])]
    ring

theorem length_inv : ∀ (k e : ℕ) (c : List R), c.length = 2 ^ k → (inv ψ H k e c).length = 2 ^ k
  | 0, _, c, h => h
  | k + 1, e, c, h => by
    have h0 : (c.take (2 ^ k)).length = 2 ^ k := by simp only [List.length_take, h, pow_succ]; omega
    have h1 : (c.drop (2 ^ k)).length = 2 ^ k := by simp only [List.length_drop, h, pow_succ]; omega
    simp only [inv, List.length_append, List.length_map, List.length_zipWith,
      length_inv k _ _ h0, length_inv k _ _ h1, min_self]
    ring

theorem zipWith_mul_append (u₁ u₂ v₁ v₂ : List R) (h : u₁.length = v₁.length) :
    List.zipWith (· * ·) (u₁ ++ u₂) (v₁ ++ v₂) =
      List.zipWith (· * ·) u₁ v₁ ++ List.zipWith (· * ·) u₂ v₂ :=
  List.zipWith_append h

/-- The convolution theorem of the twisted transform: transforming two lists,
multiplying pointwise and inverting gives `2^k` times their product modulo
`X^(2^k) - ψ^e`, as a list of length `2^k`. -/
theorem inv_fwd_mul (hψ : ψ ^ H = -1) :
    ∀ (k e : ℕ), 2 ^ k ∣ e → e < 2 * H → 2 ^ k ∣ 2 * H → ∀ (a b : List R),
      a.length = 2 ^ k → b.length = 2 ^ k →
      X ^ (2 ^ k) - C (ψ ^ e) ∣
        poly (inv ψ H k e (List.zipWith (· * ·) (fwd ψ H k e a) (fwd ψ H k e b))) -
          C ((2 : R) ^ k) * (poly a * poly b)
  | 0, e, _, _, _, a, b, ha, hb => by
    match a, b, ha, hb with
    | [x], [y], _, _ => exact ⟨0, by simp [fwd, inv, C_mul]⟩
  | k + 1, e, hdiv, he, hH, a, b, ha, hb => by
    set K := 2 ^ k with hK
    have hK2 : 2 ^ (k + 1) = 2 * K := by rw [pow_succ]; ring
    obtain ⟨f, rfl⟩ : 2 ∣ e := (dvd_pow_self 2 (Nat.succ_ne_zero k)).trans hdiv
    have he2 : 2 * f / 2 = f := by omega
    set ζ := ψ ^ f with hζ
    -- splitting the inputs
    have ha0 : (a.take K).length = K := by simp only [List.length_take, ha, hK2]; omega
    have ha1 : (a.drop K).length = K := by simp only [List.length_drop, ha, hK2]; omega
    have hb0 : (b.take K).length = K := by simp only [List.length_take, hb, hK2]; omega
    have hb1 : (b.drop K).length = K := by simp only [List.length_drop, hb, hK2]; omega
    have hpa : poly a = poly (a.take K) + X ^ K * poly (a.drop K) := by
      conv_lhs => rw [← List.take_append_drop K a]
      rw [poly_append, ha0]
    have hpb : poly b = poly (b.take K) + X ^ K * poly (b.drop K) := by
      conv_lhs => rw [← List.take_append_drop K b]
      rw [poly_append, hb0]
    -- divisibility side conditions for the children
    have hdivK : K ∣ f := by
      rw [hK2] at hdiv; exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hdiv
    have hHK : K ∣ H := by
      rw [hK2] at hH; exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) hH
    have hf : f < 2 * H := by omega
    -- the second child's root is `-ζ`
    have hneg : ψ ^ (f + H) = -ζ := by rw [pow_add, hψ, hζ]; ring
    have hinv : ψ ^ (2 * H - f) * ζ = 1 := by
      rw [hζ, ← pow_add, show 2 * H - f + f = 2 * H by omega, pow_mul', hψ]; ring
    -- children lists
    set u := bsum ζ (a.take K) (a.drop K)
    set v := bdiff ζ (a.take K) (a.drop K)
    set u' := bsum ζ (b.take K) (b.drop K)
    set v' := bdiff ζ (b.take K) (b.drop K)
    have hu : u.length = K := by rw [length_bsum _ _ _ (ha0.trans ha1.symm), ha0]
    have hv : v.length = K := by rw [length_bdiff _ _ _ (ha0.trans ha1.symm), ha0]
    have hu' : u'.length = K := by rw [length_bsum _ _ _ (hb0.trans hb1.symm), hb0]
    have hv' : v'.length = K := by rw [length_bdiff _ _ _ (hb0.trans hb1.symm), hb0]
    have hpu : poly u = poly (a.take K) + C ζ * poly (a.drop K) := by
      simp only [u, bsum]
      rw [poly_zipWith_add _ _ (by rw [List.length_map, ha0, ha1]), poly_map_mul]
    have hpv : poly v = poly (a.take K) - C ζ * poly (a.drop K) := by
      simp only [v, bdiff]
      rw [poly_zipWith_sub _ _ (by rw [List.length_map, ha0, ha1]), poly_map_mul]
    have hpu' : poly u' = poly (b.take K) + C ζ * poly (b.drop K) := by
      simp only [u', bsum]
      rw [poly_zipWith_add _ _ (by rw [List.length_map, hb0, hb1]), poly_map_mul]
    have hpv' : poly v' = poly (b.take K) - C ζ * poly (b.drop K) := by
      simp only [v', bdiff]
      rw [poly_zipWith_sub _ _ (by rw [List.length_map, hb0, hb1]), poly_map_mul]
    -- unfold one layer
    have hfu := length_fwd ψ H k f u hu
    have hfv := length_fwd ψ H k (f + H) v hv
    have hfu' := length_fwd ψ H k f u' hu'
    have hfv' := length_fwd ψ H k (f + H) v' hv'
    have hprod : List.zipWith (· * ·) (fwd ψ H (k + 1) (2 * f) a) (fwd ψ H (k + 1) (2 * f) b) =
        List.zipWith (· * ·) (fwd ψ H k f u) (fwd ψ H k f u') ++
          List.zipWith (· * ·) (fwd ψ H k (f + H) v) (fwd ψ H k (f + H) v') := by
      simp only [fwd, he2]
      exact zipWith_mul_append _ _ _ _ (hfu.trans hfu'.symm)
    have hlen1 : (List.zipWith (· * ·) (fwd ψ H k f u) (fwd ψ H k f u')).length = K := by
      simp [hfu, hfu', hK]
    set W₁ := List.zipWith (· * ·) (fwd ψ H k f u) (fwd ψ H k f u')
    set W₂ := List.zipWith (· * ·) (fwd ψ H k (f + H) v) (fwd ψ H k (f + H) v')
    have htake : (W₁ ++ W₂).take K = W₁ := List.take_left' hlen1
    have hdrop : (W₁ ++ W₂).drop K = W₂ := List.drop_left' hlen1
    -- induction hypotheses
    obtain ⟨α, hα⟩ := inv_fwd_mul hψ k f hdivK (by omega) (hHK.mul_left 2) u u' hu hu'
    obtain ⟨β, hβ⟩ := inv_fwd_mul hψ k (f + H) (dvd_add hdivK hHK)
      (by omega) (hHK.mul_left 2) v v' hv hv'
    rw [hneg] at hβ
    set P := inv ψ H k f W₁
    set Q := inv ψ H k (f + H) W₂
    have hP : P.length = K := length_inv ψ H k f W₁ hlen1
    have hQ : Q.length = K := length_inv ψ H k (f + H) W₂ (by simp [W₂, hfv, hfv'])
    have hout : inv ψ H (k + 1) (2 * f) (W₁ ++ W₂) =
        List.zipWith (· + ·) P Q ++ (List.zipWith (· - ·) P Q).map (ψ ^ (2 * H - f) * ·) := by
      simp only [inv, he2, ← hK, htake, hdrop, P, Q]
    rw [hprod, hout, poly_append, poly_map_mul, poly_zipWith_add _ _ (hP.trans hQ.symm),
      poly_zipWith_sub _ _ (hP.trans hQ.symm)]
    simp only [List.length_zipWith, hP, hQ, min_self]
    have hζ2 : ψ ^ (2 * f) = ζ ^ 2 := by rw [hζ, ← pow_mul, mul_comm]
    rw [hK2, pow_mul', hζ2]
    set z' := ψ ^ (2 * H - f)
    have hz : z' * ζ = 1 := hinv
    refine ⟨C z' * α - C z' * β - 2 ^ (k + 1) * poly (a.drop K) * poly (b.drop K), ?_⟩
    have hCz : C z' * C ζ = 1 := by rw [← C_mul, hz, C_1]
    rw [hpa, hpb]
    rw [hpu, hpu'] at hα
    rw [hpv, hpv'] at hβ
    simp only [← hζ] at hα hβ
    simp only [map_pow, C_neg, map_ofNat] at hα hβ ⊢
    simp only [← hK] at hα hβ
    linear_combination (1 + C z' * X ^ K) * hα + (1 - C z' * X ^ K) * hβ +
      (-(α * (X ^ K - C ζ)) - β * (X ^ K + C ζ) + 2 ^ (k + 1) * X ^ K *
        (poly (a.take K) * poly (b.drop K) + poly (a.drop K) * poly (b.take K))) * hCz
end Transform

end IntegerMultBounds.Schoenhage
