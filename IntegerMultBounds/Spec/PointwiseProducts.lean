import IntegerMultBounds.Spec.SignedRingProductFacts

/-! The pointwise-product step of the synthetic convolution
(`prop:synthetic-convolution`, §6), stated in the paper's formats: the slice
of the transform layer that calls `lem:signed-ring-product`. Both forward
transforms leave arrays of `M = ∏ tᵢ` contiguous polynomial records in their
common retained order; the step multiplies corresponding records and returns
`Q_p(fᵢ gᵢ / r)` for each, in the same order and component format. The
header is the transform header `Γ(p)Γ(d)Γ(r)Γ(K)Γ(w)∏Γ(tᵢ)` of
`lem:synthetic-transform-cost`.

`MeetsPointwise M Cw T` says the program does this within `T` steps;
`pointwisePaperTarget` is the paper's `O(T p log (r p))` with `T = r M`, and
`pointwisePolylogTarget k` allows an extra `(log log (r p))^k`. The header
reads back as its parameters (`transformHeader_read`). -/

namespace IntegerMultBounds.Spec.SignedRingProduct

open Machine NLogN

/-- A polynomial record by its real and imaginary numerators. -/
abbrev Rec (r : ℕ) := (Fin r → ℤ) × (Fin r → ℤ)

/-- The transform header `Γ(p)Γ(d)Γ(r)Γ(K)Γ(w)∏Γ(tᵢ)`. -/
def transformHeader (p d r K w : ℕ) (ts : List ℕ) : List Bool :=
  gamma p ++ gamma d ++ gamma r ++ gamma K ++ gamma w ++ ts.flatMap gamma

/-- Contiguous records in order. -/
def array {r : ℕ} (w : ℕ) (fs : List (Rec r)) : List Bool := fs.flatMap fun f => record w f.1 f.2

/-- The record `Q_p(f g / r)`. -/
noncomputable def prodRec {r : ℕ} (p : ℕ) (f g : Rec r) : Rec r :=
  (productRe p (gridPoly p f.1 f.2) (gridPoly p g.1 g.2), productIm p (gridPoly p f.1 f.2) (gridPoly p g.1 g.2))

/-- Valid axis lengths: `d - 1` of them, each `2^(ℓ-1)` or `2^ℓ`. -/
def AxisLengths (d ℓ : ℕ) (ts : List ℕ) : Prop := ts.length = d - 1 ∧ ∀ t ∈ ts, t = 2 ^ (ℓ - 1) ∨ t = 2 ^ ℓ

/-- `M` meets the pointwise-product step for width constant `Cw` within `T (r M) p r` steps. -/
def MeetsPointwise {t q a : ℕ} (M : Program t q a) (Cw : ℕ) (T : ℕ → ℕ → ℕ → ℕ) : Prop :=
  ∀ (p d ℓ K w : ℕ) (ts : List ℕ) (fs gs : List (Rec (2 ^ ℓ))),
    1 ≤ ℓ → 2 ≤ p → 2 ^ ℓ < 2 ^ p → 2 ≤ d → 1 ≤ K → p + 2 ≤ w → w ≤ Cw * p → AxisLengths d ℓ ts →
    fs.length = ts.prod → gs.length = ts.prod →
    (∀ f ∈ fs, DiskGrid p f.1 f.2) → (∀ g ∈ gs, DiskGrid p g.1 g.2) →
    HoareTime M (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs) [])
      (· = bank (transformHeader p d (2 ^ ℓ) K w ts) (array w fs) (array w gs)
        (array w (List.zipWith (prodRec p) fs gs)))
      (T (2 ^ ℓ * ts.prod) p (2 ^ ℓ))

/-- The paper's bound `O(T p log (r p))`. -/
def pointwisePaperTarget : Prop :=
  ∀ Cw : ℕ, 2 ≤ Cw → ∃ (t q a : ℕ) (M : Program t q a) (C : ℕ), 4 ≤ t ∧
    MeetsPointwise M Cw fun T p r => C * (T * p) * (Nat.log 2 (r * p) + 1)

/-- The bound with an extra `(log log (r p))^k` factor. -/
def pointwisePolylogTarget (k : ℕ) : Prop :=
  ∀ Cw : ℕ, 2 ≤ Cw → ∃ (t q a : ℕ) (M : Program t q a) (C : ℕ), 4 ≤ t ∧
    MeetsPointwise M Cw fun T p r =>
      C * (T * p) * (Nat.log 2 (r * p) + 1) * (Nat.log 2 (Nat.log 2 (r * p) + 1) + 1) ^ k

/-! ### Reading the header back -/

/-- Read `n` codes in order. -/
def gammaReadN : ℕ → List Bool → Option (List ℕ × List Bool)
  | 0, bs => some ([], bs)
  | n + 1, bs => (gammaRead bs).bind fun x => (gammaReadN n x.2).map fun y => (x.1 :: y.1, y.2)

theorem gammaReadN_flatMap : ∀ (vs : List ℕ), (∀ v ∈ vs, 1 ≤ v) → ∀ rest : List Bool,
    gammaReadN vs.length (vs.flatMap gamma ++ rest) = some (vs, rest)
  | [], _, rest => rfl
  | v :: vs, h, rest => by
    simp only [List.length_cons, gammaReadN, List.flatMap_cons, List.append_assoc]
    rw [gammaRead_gamma (h v (by simp)), Option.bind_some,
      gammaReadN_flatMap vs (fun u hu => h u (by simp [hu])) rest]
    rfl

/-- The transform header reads back as `p, d, r, K, w` and the axis lengths. -/
theorem transformHeader_read {p d r K w : ℕ} {ts : List ℕ} (hp : 1 ≤ p) (hd : 1 ≤ d) (hr : 1 ≤ r)
    (hK : 1 ≤ K) (hw : 1 ≤ w) (hts : ∀ t ∈ ts, 1 ≤ t) :
    gammaReadN (5 + ts.length) (transformHeader p d r K w ts) = some ([p, d, r, K, w] ++ ts, []) := by
  have e : transformHeader p d r K w ts = ([p, d, r, K, w] ++ ts).flatMap gamma ++ [] := by
    simp [transformHeader, List.flatMap_append]
  have l : 5 + ts.length = ([p, d, r, K, w] ++ ts).length := by simp; omega
  rw [e, l]
  exact gammaReadN_flatMap _ (fun v hv => by
    simp only [List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with (rfl | rfl | rfl | rfl | rfl) | hv
    all_goals first | assumption | exact hts v hv) []

/-- An array of `M` records has `2 r w M` bits. -/
theorem length_array {r : ℕ} (w : ℕ) (fs : List (Rec r)) : (array w fs).length = 2 * r * w * fs.length := by
  induction fs with
  | nil => simp [array]
  | cons f fs ih =>
    simp only [array, List.flatMap_cons, List.length_append, length_record] at ih ⊢
    rw [ih]; simp; ring

end IntegerMultBounds.Spec.SignedRingProduct
