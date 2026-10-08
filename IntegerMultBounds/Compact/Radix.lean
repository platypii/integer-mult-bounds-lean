import Mathlib.Tactic

/-! Packed integer addresses, with signed offsets and explicit no-carry bounds.
The least significant digit is first. These lemmas quantify over all list
lengths and values; they are not bounded exhaustive checks. -/

namespace IntegerMultBounds.Compact.Radix

def pack (B : ℤ) : List ℤ → ℤ
  | [] => 0
  | d :: ds => d + B * pack B ds

def Bounded (B : ℤ) (ds : List ℤ) : Prop := ∀ d ∈ ds, 0 ≤ d ∧ d < B

def digits (B : ℤ) : ℕ → ℤ → List ℤ
  | 0, _ => []
  | n + 1, x => x % B :: digits B n (x / B)

theorem digits_length (B : ℤ) (n : ℕ) (x : ℤ) : (digits B n x).length = n := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih => simp [digits, ih]

theorem bounded_cons (B d : ℤ) (ds : List ℤ) :
    Bounded B (d :: ds) ↔ (0 ≤ d ∧ d < B) ∧ Bounded B ds := by
  simp [Bounded]

theorem pack_bounds (B : ℤ) (hB : 0 < B) (ds : List ℤ) (h : Bounded B ds) :
    0 ≤ pack B ds ∧ pack B ds < B ^ ds.length := by
  induction ds with
  | nil => simp [pack]
  | cons d ds ih =>
    obtain ⟨hd, hds⟩ := (bounded_cons B d ds).mp h
    obtain ⟨hlo, hhi⟩ := ih hds
    simp only [pack, List.length_cons, pow_succ]
    constructor
    · exact add_nonneg hd.1 (mul_nonneg hB.le hlo)
    · nlinarith

theorem pack_append (B : ℤ) (xs ys : List ℤ) :
    pack B (xs ++ ys) = pack B xs + B ^ xs.length * pack B ys := by
  induction xs with
  | nil => simp [pack]
  | cons x xs ih => simp only [List.cons_append, pack, List.length_cons, pow_succ, ih]; ring

theorem digits_pack (B : ℤ) (hB : 0 < B) (ds : List ℤ) (h : Bounded B ds) :
    digits B ds.length (pack B ds) = ds := by
  induction ds with
  | nil => rfl
  | cons d ds ih =>
    obtain ⟨hd, hds⟩ := (bounded_cons B d ds).mp h
    simp only [List.length_cons, digits, pack]
    rw [Int.add_mul_emod_self_left, Int.emod_eq_of_lt hd.1 hd.2,
      Int.add_mul_ediv_left _ _ (ne_of_gt hB), Int.ediv_eq_zero_of_lt hd.1 hd.2,
      zero_add, ih hds]

theorem digits_bounded (B : ℤ) (hB : 0 < B) (n : ℕ) (x : ℤ) :
    Bounded B (digits B n x) := by
  induction n generalizing x with
  | zero => simp [digits, Bounded]
  | succ n ih =>
    rw [digits, bounded_cons]
    exact ⟨⟨Int.emod_nonneg _ (ne_of_gt hB), Int.emod_lt_of_pos _ hB⟩, ih _⟩

theorem pack_digits (B : ℤ) (hB : 0 < B) (n : ℕ) (x : ℤ)
    (hx : 0 ≤ x ∧ x < B ^ n) : pack B (digits B n x) = x := by
  induction n generalizing x with
  | zero => simp only [pow_zero] at hx; simp [digits, pack]; omega
  | succ n ih =>
    have hdiv : 0 ≤ x / B ∧ x / B < B ^ n := by
      constructor
      · exact Int.ediv_nonneg hx.1 hB.le
      · apply (Int.ediv_lt_iff_lt_mul hB).mpr
        simpa [pow_succ] using hx.2
    simp only [digits, pack, ih _ hdiv]
    exact Int.emod_add_mul_ediv x B

theorem pack_injective (B : ℤ) (hB : 0 < B) (xs ys : List ℤ)
    (hx : Bounded B xs) (hy : Bounded B ys) (hlen : xs.length = ys.length)
    (hpack : pack B xs = pack B ys) : xs = ys := by
  rw [← digits_pack B hB xs hx, hpack, hlen, digits_pack B hB ys hy]

theorem pack_add (B : ℤ) (xs ys : List ℤ) (hlen : xs.length = ys.length) :
    pack B (List.zipWith (· + ·) xs ys) = pack B xs + pack B ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all [pack]
  | cons x xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons y ys =>
      simp only [List.zipWith_cons_cons, pack]
      rw [ih ys (by simpa using hlen)]
      ring

/-- A modular rotation by a packed *signed* displacement is coordinatewise
addition whenever every resulting digit remains in range. -/
theorem rotate_no_carry (B : ℤ) (hB : 0 < B) (xs offsets : List ℤ)
    (hlen : xs.length = offsets.length)
    (hout : Bounded B (List.zipWith (· + ·) xs offsets)) :
    (pack B xs + pack B offsets) % B ^ xs.length =
      pack B (List.zipWith (· + ·) xs offsets) := by
  have hb := pack_bounds B hB _ hout
  have hlength : (List.zipWith (· + ·) xs offsets).length = xs.length := by
    simp [hlen]
  rw [hlength] at hb
  rw [← pack_add B xs offsets hlen]
  exact Int.emod_eq_of_lt hb.1 hb.2

/-- Changing a packed middle segment leaves both lower and upper spectators
unchanged when its replacement fits in that segment. -/
theorem rotate_with_spectators (lowBase middleBase highBase lo mid hi offset : ℤ)
    (hloBase : 0 < lowBase) (hmidBase : 0 < middleBase) (_hhiBase : 0 < highBase)
    (hlo : 0 ≤ lo ∧ lo < lowBase) (hhi : 0 ≤ hi ∧ hi < highBase)
    (hmid : 0 ≤ mid + offset ∧ mid + offset < middleBase) :
    (lo + lowBase * (mid + middleBase * hi) + lowBase * offset) %
        (lowBase * middleBase * highBase) =
      lo + lowBase * ((mid + offset) + middleBase * hi) := by
  have heq : lo + lowBase * (mid + middleBase * hi) + lowBase * offset =
      lo + lowBase * ((mid + offset) + middleBase * hi) := by ring
  rw [heq]
  apply Int.emod_eq_of_lt
  · exact add_nonneg hlo.1 (mul_nonneg hloBase.le
      (add_nonneg hmid.1 (mul_nonneg hmidBase.le hhi.1)))
  · have hm : (mid + offset) + middleBase * hi < middleBase * highBase := by
      nlinarith
    nlinarith

end IntegerMultBounds.Compact.Radix
