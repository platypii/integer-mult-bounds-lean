import IntegerMultBounds.Schoenhage.Transform
import Mathlib.Data.ZMod.Basic
import Mathlib.Algebra.Polynomial.Eval.Defs

/-! One level of Schönhage–Strassen multiplication modulo `2^n + 1`, with
`n = 2^k M`: cut each operand into `2^k` pieces of `M` bits (the top piece
takes the possible bit `2^n`), transform them in `ℤ/(2^N + 1)` with
`ψ = 2^(N / 2^k)`, multiply pointwise, invert, divide by `2^k` (a
multiplication by `2^(2N - k)`), lift each coefficient to its signed
representative and evaluate at `2^M`. Proved (`level_correct`): whenever
`2^k ∣ N` and `2M + k + 1 ≤ N`, the result is congruent to `x y` modulo
`2^n + 1`. The pointwise products are left abstract in the ring, so the
recursion may compute them by any correct means. -/

namespace IntegerMultBounds.Schoenhage

open Polynomial

section Coeff

variable {R S : Type*} [CommRing R] [CommRing S]

theorem coeff_poly : ∀ (l : List R) (i : ℕ), (poly l).coeff i = l.getD i 0
  | [], i => by simp
  | c :: cs, 0 => by simp
  | c :: cs, i + 1 => by simp [coeff_poly cs i]

theorem degree_poly_lt (l : List R) : (poly l).degree < l.length :=
  (degree_lt_iff_coeff_zero _ _).2 fun m hm => by
    rw [coeff_poly]; simp [List.getElem?_eq_none hm]

theorem poly_injective {l₁ l₂ : List R} (h : l₁.length = l₂.length) (hp : poly l₁ = poly l₂) :
    l₁ = l₂ := by
  apply List.ext_getElem h
  intro i h₁ h₂
  have := congrArg (fun p => Polynomial.coeff p i) hp
  simpa [coeff_poly, List.getElem?_eq_getElem h₁, List.getElem?_eq_getElem h₂] using this

theorem poly_map (f : R →+* S) : ∀ l : List R, poly (l.map f) = (poly l).map f
  | [] => by simp
  | c :: cs => by simp [poly_map f cs]

theorem poly_range_map (f : ℕ → R) :
    ∀ K, poly ((List.range K).map f) = ∑ i ∈ Finset.range K, C (f i) * X ^ i
  | 0 => by simp
  | K + 1 => by
    rw [List.range_succ, List.map_append, poly_append, poly_range_map f K, Finset.sum_range_succ]
    simp

theorem eq_zero_of_monic_dvd [Nontrivial R] {p q : R[X]} (hq : q.Monic) (h : q ∣ p)
    (hd : p.degree < q.degree) : p = 0 := by
  obtain ⟨r, rfl⟩ := h
  by_contra hne
  have hr : r ≠ 0 := by rintro rfl; simp at hne
  rw [mul_comm, hq.degree_mul] at hd
  have hqd : q.degree ≠ ⊥ := by
    intro hb; rw [degree_eq_bot] at hb; exact hq.ne_zero hb
  obtain ⟨d, hd'⟩ := WithBot.ne_bot_iff_exists.mp hqd
  rw [← hd'] at hd
  obtain ⟨e, he⟩ := WithBot.ne_bot_iff_exists.mp (degree_eq_bot.not.mpr hr)
  rw [← he] at hd
  norm_cast at hd
  omega

/-- Two lists of length `K` congruent modulo `X^K + 1` are equal. -/
theorem eq_of_dvd_X_pow_add_one [Nontrivial R] {K : ℕ} (hK : 0 < K) {l₁ l₂ : List R}
    (h₁ : l₁.length = K) (h₂ : l₂.length = K) (h : X ^ K + 1 ∣ poly l₁ - poly l₂) : l₁ = l₂ := by
  have hm : (X ^ K + 1 : R[X]).Monic := by
    simpa using monic_X_pow_add_C (1 : R) hK.ne'
  have hdeg : (X ^ K + 1 : R[X]).degree = K := by
    simpa using degree_X_pow_add_C (R := R) hK (1 : R)
  refine poly_injective (h₁.trans h₂.symm) (sub_eq_zero.mp (eq_zero_of_monic_dvd hm h ?_))
  rw [hdeg]
  refine (degree_sub_le _ _).trans_lt (max_lt ?_ ?_)
  · simpa [h₁] using degree_poly_lt l₁
  · simpa [h₂] using degree_poly_lt l₂

end Coeff

section Negacyclic

/-- The negacyclic product of two integer lists of length `K`, read off the
ordinary product: coefficient `l` minus coefficient `l + K`. -/
noncomputable def negaList (K : ℕ) (a b : List ℤ) : List ℤ :=
  (List.range K).map fun l => (poly a * poly b).coeff l - (poly a * poly b).coeff (l + K)

theorem length_negaList (K : ℕ) (a b : List ℤ) : (negaList K a b).length = K := by
  simp [negaList]

theorem negaList_dvd {K : ℕ} (a b : List ℤ) (ha : a.length = K) (hb : b.length = K) :
    X ^ K + 1 ∣ poly (negaList K a b) - poly a * poly b := by
  rcases Nat.eq_zero_or_pos K with rfl | hK
  · rw [List.length_eq_zero_iff.mp ha]
    simp [negaList]
  set P := poly a * poly b
  have hnat : ∀ l : List ℤ, l.length = K → (poly l).natDegree < K := fun l hl => by
    by_cases h0 : poly l = 0
    · rw [h0]; simpa using hK
    · exact (natDegree_lt_iff_degree_lt h0).2 (hl ▸ degree_poly_lt l)
  have hP : P.natDegree < K + K :=
    (natDegree_mul_le).trans_lt (Nat.add_lt_add (hnat a ha) (hnat b hb))
  have hsum : P = ∑ i ∈ Finset.range K, C (P.coeff i) * X ^ i +
      ∑ i ∈ Finset.range K, C (P.coeff (K + i)) * X ^ (K + i) := by
    conv_lhs => rw [as_sum_range' P (K + K) hP]
    rw [Finset.sum_range_add]
    simp only [← C_mul_X_pow_eq_monomial]
  refine ⟨-∑ i ∈ Finset.range K, C (P.coeff (i + K)) * X ^ i, ?_⟩
  have key : poly (negaList K a b) - (∑ i ∈ Finset.range K, C (P.coeff i) * X ^ i +
      ∑ i ∈ Finset.range K, C (P.coeff (K + i)) * X ^ (K + i)) =
      (X ^ K + 1) * -∑ i ∈ Finset.range K, C (P.coeff (i + K)) * X ^ i := by
    rw [negaList, poly_range_map]
    simp only [← Finset.sum_add_distrib, ← Finset.sum_sub_distrib, Finset.mul_sum, mul_neg,
      ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [add_comm K i, C_sub]
    ring
  rwa [← hsum] at key

theorem getD_bounds {a : List ℤ} {B : ℤ} (hB : 0 ≤ B) (h : ∀ x ∈ a, 0 ≤ x ∧ x ≤ B) (i : ℕ) :
    0 ≤ a.getD i 0 ∧ a.getD i 0 ≤ B := by
  by_cases hi : i < a.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
    exact ⟨le_rfl, hB⟩

/-- Every coefficient of the product of two lists of length `K` with entries in
`[0, B]` lies in `[0, K B²]`. -/
theorem coeff_mul_bounds {K : ℕ} {B : ℤ} (hB : 0 ≤ B) (a b : List ℤ) (ha : a.length = K)
    (ha0 : ∀ x ∈ a, 0 ≤ x ∧ x ≤ B) (hb0 : ∀ x ∈ b, 0 ≤ x ∧ x ≤ B) (m : ℕ) :
    0 ≤ (poly a * poly b).coeff m ∧ (poly a * poly b).coeff m ≤ K * B ^ 2 := by
  rw [coeff_mul, Finset.Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  simp only [coeff_poly]
  constructor
  · exact Finset.sum_nonneg fun i _ =>
      mul_nonneg (getD_bounds hB ha0 i).1 (getD_bounds hB hb0 _).1
  · calc ∑ i ∈ Finset.range m.succ, a.getD i 0 * b.getD (m - i) 0
        ≤ ∑ i ∈ Finset.range m.succ, if i < K then B ^ 2 else 0 := by
          refine Finset.sum_le_sum fun i _ => ?_
          split_ifs with hi
          · rw [sq]
            exact mul_le_mul (getD_bounds hB ha0 i).2 (getD_bounds hB hb0 _).2
              (getD_bounds hB hb0 _).1 hB
          · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)]
            simp
      _ = ∑ i ∈ Finset.range m.succ with i < K, B ^ 2 := (Finset.sum_filter _ _).symm
      _ ≤ ∑ i ∈ Finset.range K, B ^ 2 :=
          Finset.sum_le_sum_of_subset_of_nonneg
            (fun i hi => by simp at hi ⊢; omega) (fun _ _ _ => sq_nonneg B)
      _ = K * B ^ 2 := by simp

theorem negaList_bounds {K : ℕ} {B : ℤ} (hB : 0 ≤ B) (a b : List ℤ) (ha : a.length = K)
    (ha0 : ∀ x ∈ a, 0 ≤ x ∧ x ≤ B) (hb0 : ∀ x ∈ b, 0 ≤ x ∧ x ≤ B) :
    ∀ c ∈ negaList K a b, |c| ≤ K * B ^ 2 := by
  intro c hc
  simp only [negaList, List.mem_map, List.mem_range] at hc
  obtain ⟨l, -, rfl⟩ := hc
  have h1 := coeff_mul_bounds hB a b ha ha0 hb0 l
  have h2 := coeff_mul_bounds hB a b ha ha0 hb0 (l + K)
  rw [abs_le]; constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]

end Negacyclic

section Pieces

/-- `K` pieces of `M` bits, least significant first; the top piece keeps all
remaining high bits. -/
def pieces (M : ℕ) : ℕ → ℕ → List ℕ
  | 0, _ => []
  | 1, x => [x]
  | K + 2, x => x % 2 ^ M :: pieces M (K + 1) (x / 2 ^ M)

theorem length_pieces (M : ℕ) : ∀ K x, (pieces M K x).length = K
  | 0, _ => rfl
  | 1, _ => rfl
  | K + 2, x => by simp [pieces, length_pieces M (K + 1)]

theorem eval_pieces (M : ℕ) : ∀ K x, 0 < K →
    (poly ((pieces M K x).map (Nat.cast : ℕ → ℤ))).eval (2 ^ M) = x
  | 0, _, h => absurd h (lt_irrefl 0)
  | 1, x, _ => by simp [pieces]
  | K + 2, x, _ => by
    simp only [pieces, List.map_cons, poly_cons, eval_add, eval_C, eval_mul, eval_X]
    rw [eval_pieces M (K + 1) _ (Nat.succ_pos _)]
    have := Nat.mod_add_div x (2 ^ M)
    push_cast
    exact_mod_cast this

theorem pieces_le (M : ℕ) : ∀ K x, x ≤ 2 ^ (M * K) → ∀ p ∈ pieces M K x, p ≤ 2 ^ M
  | 0, _, _ => by simp [pieces]
  | 1, x, h => by simpa [pieces] using h
  | K + 2, x, h => by
    intro p hp
    simp only [pieces, List.mem_cons] at hp
    rcases hp with rfl | hp
    · exact (Nat.mod_lt _ (by positivity)).le
    · refine pieces_le M (K + 1) _ ?_ p hp
      rw [Nat.div_le_iff_le_mul_add_pred (by positivity)]
      calc x ≤ 2 ^ (M * (K + 2)) := h
        _ = 2 ^ M * 2 ^ (M * (K + 1)) := by rw [← pow_add]; ring_nf
        _ ≤ _ := by rw [mul_comm]; omega

end Pieces

section Ring

/-- The signed representative of a residue modulo `2^N + 1`. -/
def lift (N : ℕ) (r : ZMod (2 ^ N + 1)) : ℤ :=
  if 2 * r.val < 2 ^ N + 1 then r.val else (r.val : ℤ) - (2 ^ N + 1)

theorem lift_intCast (N : ℕ) (c : ℤ) (h : 2 * |c| < 2 ^ N + 1) :
    lift N (c : ZMod (2 ^ N + 1)) = c := by
  have hv := ZMod.val_intCast (n := 2 ^ N + 1) c
  push_cast at hv
  have hF : (0 : ℤ) < 2 ^ N + 1 := by positivity
  unfold lift
  rcases le_or_gt 0 c with hc | hc
  · rw [abs_of_nonneg hc] at h
    rw [Int.emod_eq_of_lt hc (by linarith)] at hv
    have : 2 * (c : ZMod (2 ^ N + 1)).val < 2 ^ N + 1 := by
      have : ((2 * (c : ZMod (2 ^ N + 1)).val : ℕ) : ℤ) < 2 ^ N + 1 := by push_cast; omega
      exact_mod_cast this
    simp only [this, ↓reduceIte]; omega
  · rw [abs_of_neg hc] at h
    have he : c % (2 ^ N + 1) = c + (2 ^ N + 1) := by
      rw [← Int.add_emod_right, Int.emod_eq_of_lt (by omega) (by omega)]
    rw [he] at hv
    have : ¬ 2 * (c : ZMod (2 ^ N + 1)).val < 2 ^ N + 1 := by
      intro hlt
      have : ((2 * (c : ZMod (2 ^ N + 1)).val : ℕ) : ℤ) < 2 ^ N + 1 := by exact_mod_cast hlt
      push_cast at this; omega
    simp only [this, ↓reduceIte]; omega

theorem two_pow_N (N : ℕ) : (2 : ZMod (2 ^ N + 1)) ^ N = -1 := by
  have : ((2 ^ N + 1 : ℕ) : ZMod (2 ^ N + 1)) = 0 := ZMod.natCast_self _
  push_cast at this
  linear_combination this

theorem two_pow_two_N (N : ℕ) : (2 : ZMod (2 ^ N + 1)) ^ (2 * N) = 1 := by
  rw [pow_mul', two_pow_N]; norm_num

/-- The transform computes `2^k` times the negacyclic product. -/
theorem transform_negaList {k N : ℕ} (hkN : 2 ^ k ∣ N) (a b : List ℕ)
    (ha : a.length = 2 ^ k) (hb : b.length = 2 ^ k) :
    let ψ : ZMod (2 ^ N + 1) := 2 ^ (N / 2 ^ k)
    inv ψ (2 ^ k) k (2 ^ k) (List.zipWith (· * ·) (fwd ψ (2 ^ k) k (2 ^ k) (a.map (↑)))
        (fwd ψ (2 ^ k) k (2 ^ k) (b.map (↑)))) =
      (negaList (2 ^ k) (a.map (↑)) (b.map (↑))).map fun c : ℤ => (2 : ZMod (2 ^ N + 1)) ^ k * c := by
  intro ψ
  have : Fact (1 < 2 ^ N + 1) := ⟨by have := Nat.one_le_two_pow (n := N); omega⟩
  have hψ : ψ ^ 2 ^ k = -1 := by
    rw [← pow_mul, Nat.div_mul_cancel hkN, two_pow_N]
  have hK : 0 < 2 ^ k := by positivity
  have h := inv_fwd_mul ψ (2 ^ k) hψ k (2 ^ k) dvd_rfl (by omega) (dvd_mul_left _ _)
    (a.map (↑)) (b.map (↑)) (by simp [ha]) (by simp [hb])
  rw [hψ, C_neg, C_1, sub_neg_eq_add] at h
  have hZ := Polynomial.map_dvd (Int.castRingHom (ZMod (2 ^ N + 1)))
    (negaList_dvd (K := 2 ^ k) (a.map (↑)) (b.map (↑)) (by simp [ha]) (by simp [hb]))
  simp only [Polynomial.map_sub, Polynomial.map_mul, Polynomial.map_add, Polynomial.map_pow,
    map_X, Polynomial.map_one, ← poly_map, List.map_map, Function.comp_def, eq_intCast,
    Int.cast_natCast] at hZ
  apply eq_of_dvd_X_pow_add_one hK
  · rw [length_inv]; simp [List.length_zipWith, length_fwd, ha, hb]
  · simp [length_negaList]
  · have hmap : (negaList (2 ^ k) (a.map (↑)) (b.map (↑))).map
        (fun c : ℤ => (2 : ZMod (2 ^ N + 1)) ^ k * c) =
        ((negaList (2 ^ k) (a.map (↑)) (b.map (↑))).map
          (Int.castRingHom (ZMod (2 ^ N + 1)))).map ((2 : ZMod (2 ^ N + 1)) ^ k * ·) := by
      rw [List.map_map]; rfl
    rw [hmap, poly_map_mul]
    have := dvd_sub h (dvd_mul_of_dvd_right hZ (C ((2 : ZMod (2 ^ N + 1)) ^ k)))
    convert this using 1
    ring

/-- One level of Schönhage–Strassen: the lifted, descaled inverse transform of
the pointwise product, evaluated at `2^M`, is `x y` modulo `2^(2^k M) + 1`. -/
theorem level_correct {k M N : ℕ} (hkN : 2 ^ k ∣ N) (hN : 2 * M + k + 1 ≤ N) (x y : ℕ)
    (hx : x ≤ 2 ^ (M * 2 ^ k)) (hy : y ≤ 2 ^ (M * 2 ^ k)) :
    let ψ : ZMod (2 ^ N + 1) := 2 ^ (N / 2 ^ k)
    let w := inv ψ (2 ^ k) k (2 ^ k)
      (List.zipWith (· * ·) (fwd ψ (2 ^ k) k (2 ^ k) ((pieces M (2 ^ k) x).map (↑)))
        (fwd ψ (2 ^ k) k (2 ^ k) ((pieces M (2 ^ k) y).map (↑))))
    let c := w.map fun r => lift N ((2 : ZMod (2 ^ N + 1)) ^ (2 * N - k) * r)
    (poly c).eval (2 ^ M) ≡ (x : ℤ) * y [ZMOD 2 ^ (M * 2 ^ k) + 1] := by
  intro ψ w c
  have hK : 0 < 2 ^ k := by positivity
  have hkle : k ≤ N := by
    have := Nat.le_of_dvd (by omega) hkN
    exact (Nat.lt_two_pow_self).le.trans this
  set a := (pieces M (2 ^ k) x).map (Nat.cast : ℕ → ℤ)
  set b := (pieces M (2 ^ k) y).map (Nat.cast : ℕ → ℤ)
  have hw : w = (negaList (2 ^ k) a b).map fun c : ℤ => (2 : ZMod (2 ^ N + 1)) ^ k * c := by
    have := transform_negaList hkN (pieces M (2 ^ k) x) (pieces M (2 ^ k) y)
      (length_pieces _ _ _) (length_pieces _ _ _)
    convert this using 3
  have hbound : ∀ z ∈ a, 0 ≤ z ∧ z ≤ (2 : ℤ) ^ M := by
    intro z hz
    simp only [a, List.mem_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨by positivity, by exact_mod_cast pieces_le M _ x (by simpa [mul_comm] using hx) p hp⟩
  have hbound' : ∀ z ∈ b, 0 ≤ z ∧ z ≤ (2 : ℤ) ^ M := by
    intro z hz
    simp only [b, List.mem_map] at hz
    obtain ⟨p, hp, rfl⟩ := hz
    exact ⟨by positivity, by exact_mod_cast pieces_le M _ y (by simpa [mul_comm] using hy) p hp⟩
  have hc : c = negaList (2 ^ k) a b := by
    simp only [c, hw, List.map_map]
    conv_rhs => rw [← List.map_id (negaList (2 ^ k) a b)]
    refine List.map_congr_left fun z hz => ?_
    simp only [Function.comp_apply, id]
    rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel (by omega), two_pow_two_N, one_mul]
    apply lift_intCast
    have := negaList_bounds (by positivity) a b (by simp [a, length_pieces]) hbound hbound' z hz
    calc 2 * |z| ≤ 2 * (2 ^ k * (2 ^ M) ^ 2) := by push_cast at this ⊢; linarith
      _ = 2 ^ (2 * M + k + 1) := by ring
      _ ≤ 2 ^ N := pow_le_pow_right₀ (by norm_num) hN
      _ < 2 ^ N + 1 := by linarith
  rw [hc, Int.modEq_iff_dvd]
  have hd := eval_dvd (x := (2 : ℤ) ^ M) (negaList_dvd (K := 2 ^ k) a b
    (by simp [a, length_pieces]) (by simp [b, length_pieces]))
  simp only [eval_add, eval_pow, eval_X, eval_one, eval_sub, eval_mul, a, b,
    eval_pieces M _ _ hK] at hd
  rw [← pow_mul] at hd
  rw [← dvd_neg, neg_sub]
  exact hd

end Ring

end IntegerMultBounds.Schoenhage
