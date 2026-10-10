import IntegerMultBounds.Schoenhage.Recomb

/-! Exact arithmetic for packed negacyclic products. Evaluation at `X` turns
the negacyclic product modulo `y^r + 1` into the product modulo `X^r + 1`
(`ev_ncMul`). With `X = 2^W` and `N = W r`, signed coefficients below
`2^(W-1)` in absolute value are recovered from a residue modulo `2^N + 1` by
adding the offset word of `2^(W-1)` digits and cutting into `W`-bit pieces
(`decode_pieces`); offset digits `d - c` are packed by a plain shifted sum
and one subtraction of the offset word (`encode_res`). -/

namespace IntegerMultBounds.Schoenhage

open Finset

/-- `Σ uⱼ Xʲ`. -/
def ev (X : ℤ) : List ℤ → ℤ
  | [] => 0
  | u :: us => u + X * ev X us

/-- Coefficient `k` of the negacyclic product modulo `y^r + 1`. -/
def ncCoef (r : ℕ) (u v : List ℤ) (k : ℕ) : ℤ :=
  ∑ i ∈ Finset.range r, ∑ j ∈ Finset.range r,
    (if i + j = k then u.getD i 0 * v.getD j 0
     else if i + j = k + r then -(u.getD i 0 * v.getD j 0) else 0)

/-- The negacyclic product modulo `y^r + 1`. -/
def ncMul (r : ℕ) (u v : List ℤ) : List ℤ := (List.range r).map (ncCoef r u v)

@[simp] theorem length_ncMul (r : ℕ) (u v : List ℤ) : (ncMul r u v).length = r := by simp [ncMul]

/-! ### Evaluation -/

theorem ev_eq_sum (X : ℤ) : ∀ u : List ℤ, ev X u = ∑ i ∈ range u.length, u.getD i 0 * X ^ i
  | [] => by simp [ev]
  | a :: us => by
    rw [ev, ev_eq_sum X us, List.length_cons, sum_range_succ', mul_sum]
    simp only [List.getD_cons_succ, List.getD_cons_zero, pow_zero, mul_one, pow_succ]
    rw [add_comm]; congr 1; apply sum_congr rfl; intro i _; ring

theorem ev_add (X : ℤ) : ∀ u v : List ℤ, u.length = v.length →
    ev X (List.zipWith (· + ·) u v) = ev X u + ev X v
  | [], [], _ => by simp [ev]
  | a :: u, b :: v, h => by
    simp only [List.zipWith_cons_cons, ev, ev_add X u v (by simpa using h)]; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem ev_sub (X : ℤ) : ∀ u v : List ℤ, u.length = v.length →
    ev X (List.zipWith (· - ·) u v) = ev X u - ev X v
  | [], [], _ => by simp [ev]
  | a :: u, b :: v, h => by
    simp only [List.zipWith_cons_cons, ev, ev_sub X u v (by simpa using h)]; ring
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

/-- One product term against its negacyclic placement. -/
theorem nc_term (X p : ℤ) {r i j : ℕ} (hi : i < r) (hj : j < r) :
    (X ^ r + 1) ∣ p * X ^ (i + j) -
      ∑ k ∈ range r, (if i + j = k then p else if i + j = k + r then -p else 0) * X ^ k := by
  by_cases h : i + j < r
  · rw [sum_eq_single (i + j)]
    · simp
    · intro k _ hk
      have h1 : ¬ i + j = k := fun e => hk e.symm
      have h2 : ¬ i + j = k + r := by omega
      simp [h1, h2]
    · intro hm; exact absurd (mem_range.mpr h) hm
  · rw [sum_eq_single (i + j - r)]
    · have h1 : ¬ i + j = i + j - r := by omega
      have h2 : i + j = i + j - r + r := by omega
      rw [if_neg h1, if_pos h2]
      refine ⟨p * X ^ (i + j - r), ?_⟩
      have : X ^ (i + j) = X ^ (i + j - r) * X ^ r := by rw [← pow_add]; congr 1
      rw [this]; ring
    · intro k hk hne
      have hk' := mem_range.mp hk
      have h1 : ¬ i + j = k := by omega
      have h2 : ¬ i + j = k + r := by omega
      simp [h1, h2]
    · intro hm; exact absurd (mem_range.mpr (by omega)) hm

theorem ev_ncMul (X : ℤ) (r : ℕ) (u v : List ℤ) (hu : u.length = r) (hv : v.length = r) :
    ev X u * ev X v ≡ ev X (ncMul r u v) [ZMOD X ^ r + 1] := by
  rw [Int.modEq_iff_dvd]
  have hn : ev X (ncMul r u v) = ∑ k ∈ range r, ncCoef r u v k * X ^ k := by
    rw [ev_eq_sum, length_ncMul]
    apply sum_congr rfl; intro k hk
    simp only [ncMul, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range (mem_range.mp hk),
      Option.map_some, Option.getD_some]
  have hp : ev X u * ev X v = ∑ i ∈ range r, ∑ j ∈ range r, u.getD i 0 * v.getD j 0 * X ^ (i + j) := by
    rw [ev_eq_sum, ev_eq_sum, hu, hv, sum_mul_sum]
    apply sum_congr rfl; intro i _; apply sum_congr rfl; intro j _; rw [pow_add]; ring
  have hs : ∑ k ∈ range r, ncCoef r u v k * X ^ k = ∑ i ∈ range r, ∑ j ∈ range r, ∑ k ∈ range r,
      (if i + j = k then u.getD i 0 * v.getD j 0
        else if i + j = k + r then -(u.getD i 0 * v.getD j 0) else 0) * X ^ k := by
    simp only [ncCoef, sum_mul]
    rw [sum_comm]; apply sum_congr rfl; intro i _; rw [sum_comm]
  rw [hn, hs, hp, ← dvd_neg, neg_sub, ← sum_sub_distrib]
  apply dvd_sum; intro i hi
  rw [← sum_sub_distrib]
  apply dvd_sum; intro j hj
  exact nc_term X _ (mem_range.mp hi) (mem_range.mp hj)

/-! ### Coefficient bounds -/

theorem getD_abs_le {u : List ℤ} {U : ℤ} (hu : ∀ x ∈ u, |x| ≤ U) (hU : 0 ≤ U) (i : ℕ) :
    |u.getD i 0| ≤ U := by
  rw [List.getD_eq_getElem?_getD]
  rcases h : u[i]? with _ | x
  · simpa using hU
  · exact hu x (List.mem_of_getElem? h)

theorem ncCoef_abs (r : ℕ) (u v : List ℤ) (U V : ℤ) (hu : ∀ x ∈ u, |x| ≤ U) (hv : ∀ y ∈ v, |y| ≤ V)
    (hU : 0 ≤ U) (hV : 0 ≤ V) (k : ℕ) : |ncCoef r u v k| ≤ r * (U * V) := by
  have hpq : ∀ i j, |u.getD i 0 * v.getD j 0| ≤ U * V := fun i j => by
    rw [abs_mul]; exact mul_le_mul (getD_abs_le hu hU i) (getD_abs_le hv hV j) (abs_nonneg _) hU
  have inner : ∀ i ∈ range r, |∑ j ∈ range r,
      (if i + j = k then u.getD i 0 * v.getD j 0
       else if i + j = k + r then -(u.getD i 0 * v.getD j 0) else 0)| ≤ U * V := by
    intro i hi
    have hi' := mem_range.mp hi
    set j0 := if i ≤ k then k - i else k + r - i
    set f : ℕ → ℤ := fun j => if i + j = k then u.getD i 0 * v.getD j 0
       else if i + j = k + r then -(u.getD i 0 * v.getD j 0) else 0
    have hf : ∀ j ∈ range r, f j = if j = j0 then f j0 else 0 := by
      intro j hj
      have hj' := mem_range.mp hj
      by_cases e : j = j0
      · simp [e]
      · have h1 : ¬ i + j = k := by intro x; apply e; simp only [j0]; split_ifs <;> omega
        have h2 : ¬ i + j = k + r := by intro x; apply e; simp only [j0]; split_ifs <;> omega
        simp [f, e, h1, h2]
    change |∑ j ∈ range r, f j| ≤ U * V
    rw [sum_congr rfl hf, sum_ite_eq']
    have hz : |(0 : ℤ)| ≤ U * V := by simpa using mul_nonneg hU hV
    split_ifs
    · simp only [f]
      split_ifs
      · exact hpq _ _
      · rw [abs_neg]; exact hpq _ _
      · exact hz
    · exact hz
  unfold ncCoef
  calc _ ≤ ∑ i ∈ range r, |∑ j ∈ range r,
        (if i + j = k then u.getD i 0 * v.getD j 0
         else if i + j = k + r then -(u.getD i 0 * v.getD j 0) else 0)| := abs_sum_le_sum_abs _ _
    _ ≤ ∑ _i ∈ range r, U * V := sum_le_sum inner
    _ = r * (U * V) := by simp

/-! ### Digits -/

theorem ev_offset (W : ℕ) (h : List ℤ) :
    ev (2 ^ W) h + ev (2 ^ W) (List.replicate h.length (2 ^ (W - 1))) = ev (2 ^ W) (h.map (· + 2 ^ (W - 1))) := by
  induction h with
  | nil => simp [ev]
  | cons a h ih =>
    simp only [List.length_cons, List.replicate_succ, List.map_cons, ev, ← ih]; ring

theorem ev_natCast (W : ℕ) : ∀ ds : List ℕ, ev (2 ^ W) (ds.map (↑)) = (wsum W ds : ℤ)
  | [] => by simp [ev, wsum]
  | d :: ds => by simp only [List.map_cons, ev, wsum, ev_natCast W ds]; push_cast; ring

theorem wsum_lt_pow (W : ℕ) : ∀ ds : List ℕ, (∀ d ∈ ds, d < 2 ^ W) → wsum W ds < 2 ^ (W * ds.length)
  | [], _ => by simp [wsum]
  | d :: ds, h => by
    have ih := wsum_lt_pow W ds (fun x hx => h x (by simp [hx]))
    have hd := h d (by simp)
    simp only [wsum, List.length_cons]
    have e : 2 ^ (W * (ds.length + 1)) = 2 ^ W * 2 ^ (W * ds.length) := by
      rw [← pow_add]; congr 1; ring
    have := Nat.mul_le_mul_left (2 ^ W) (Nat.succ_le_of_lt ih)
    rw [e]; rw [Nat.mul_succ] at this; omega

theorem pieces_wsum (W : ℕ) : ∀ ds : List ℕ, ds ≠ [] → (∀ d ∈ ds, d < 2 ^ W) →
    pieces W ds.length (wsum W ds) = ds
  | [], hne, _ => absurd rfl hne
  | [d], _, _ => by simp [pieces, wsum]
  | d :: e :: rest, _, h => by
    have hd := h d (by simp)
    have ih := pieces_wsum W (e :: rest) (by simp) (fun x hx => h x (by simp [hx]))
    have hp : 0 < 2 ^ W := Nat.two_pow_pos W
    simp only [List.length_cons] at ih ⊢
    simp only [pieces]
    rw [show wsum W (d :: e :: rest) = d + 2 ^ W * wsum W (e :: rest) from rfl,
      Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt hd, Nat.add_mul_div_left _ _ hp,
      Nat.div_eq_of_lt hd, zero_add, ih]

/-- The digit word of `h`: each coefficient plus `2^(W-1)`. -/
theorem digits_lt {W : ℕ} (hW : 1 ≤ W) {h : List ℤ} (hh : ∀ x ∈ h, -2 ^ (W - 1) ≤ x ∧ x < 2 ^ (W - 1)) :
    ∀ d ∈ h.map (fun x => (x + 2 ^ (W - 1)).toNat), d < 2 ^ W := by
  intro d hd
  simp only [List.mem_map] at hd
  obtain ⟨x, hx, rfl⟩ := hd
  have := hh x hx
  have e : (2 : ℤ) ^ W = 2 * 2 ^ (W - 1) := by rw [← pow_succ']; congr 1; omega
  have : x + 2 ^ (W - 1) < 2 ^ W := by rw [e]; linarith
  exact (Int.toNat_lt (by linarith)).mpr (by exact_mod_cast this)

theorem ev_digits {W : ℕ} {h : List ℤ} (hh : ∀ x ∈ h, -2 ^ (W - 1) ≤ x ∧ x < 2 ^ (W - 1)) :
    (wsum W (h.map fun x => (x + 2 ^ (W - 1)).toNat) : ℤ) =
      ev (2 ^ W) h + wsum W (List.replicate h.length (2 ^ (W - 1))) := by
  rw [← ev_natCast, ← ev_natCast, List.map_replicate, Nat.cast_pow, Nat.cast_ofNat, ev_offset]
  congr 1
  rw [List.map_map]
  apply List.map_congr_left; intro x hx
  have := hh x hx
  simp only [Function.comp_apply]
  exact Int.toNat_of_nonneg (by linarith)

theorem decode_digits {W r N : ℕ} (hW : 1 ≤ W) (hN : N = W * r) {h : List ℤ} (hl : h.length = r)
    (hh : ∀ x ∈ h, -2 ^ (W - 1) ≤ x ∧ x < 2 ^ (W - 1)) {V : ℕ}
    (hV : (V : ℤ) ≡ ev (2 ^ W) h [ZMOD (Fm N : ℤ)]) :
    (V + wsum W (List.replicate r (2 ^ (W - 1)))) % Fm N =
      wsum W (h.map fun x => (x + 2 ^ (W - 1)).toNat) := by
  set D := h.map fun x => (x + 2 ^ (W - 1)).toNat
  set O := wsum W (List.replicate r (2 ^ (W - 1)))
  have hlt : wsum W D < Fm N := by
    have := wsum_lt_pow W D (digits_lt hW hh)
    rw [List.length_map, hl, ← hN] at this
    unfold Fm; omega
  have he := ev_digits (W := W) hh
  rw [hl] at he
  have hm : ((V + O : ℕ) : ℤ) ≡ (wsum W D : ℤ) [ZMOD (Fm N : ℤ)] := by
    rw [he]; push_cast; exact hV.add_right _
  have hm' : ((V + O : ℕ) : ℤ) % (Fm N : ℤ) = (wsum W D : ℤ) % (Fm N : ℤ) := hm
  have : (((V + O) % Fm N : ℕ) : ℤ) = ((wsum W D : ℕ) : ℤ) := by
    rw [Int.natCast_mod, hm', ← Int.natCast_mod, Nat.mod_eq_of_lt hlt]
  exact_mod_cast this

theorem decode_pieces {W r N : ℕ} (hW : 1 ≤ W) (hr : 1 ≤ r) (hN : N = W * r) {h : List ℤ} (hl : h.length = r)
    (hh : ∀ x ∈ h, -2 ^ (W - 1) ≤ x ∧ x < 2 ^ (W - 1)) {V : ℕ}
    (hV : (V : ℤ) ≡ ev (2 ^ W) h [ZMOD (Fm N : ℤ)]) :
    pieces W r ((V + wsum W (List.replicate r (2 ^ (W - 1)))) % Fm N) =
      h.map fun x => (x + 2 ^ (W - 1)).toNat := by
  rw [decode_digits hW hN hl hh hV]
  have := pieces_wsum W (h.map fun x => (x + 2 ^ (W - 1)).toNat)
    (by intro e; have := congrArg List.length e; simp [hl] at this; omega) (digits_lt hW hh)
  rwa [List.length_map, hl] at this

/-! ### Packing offset digits -/

theorem ev_encode (W c : ℕ) : ∀ ds : List ℕ,
    ev (2 ^ W) (ds.map fun d : ℕ => (d : ℤ) - c) = wsum W ds - wsum W (List.replicate ds.length c)
  | [] => by simp [ev, wsum]
  | d :: ds => by
    simp only [List.map_cons, ev, List.length_cons, List.replicate_succ, wsum, ev_encode W c ds]
    push_cast; ring

theorem encode_res (W N c : ℕ) (ds : List ℕ) (hb : wsum W (List.replicate ds.length c) < 2 ^ N + 1) :
    (((wsum W ds + Fm N - wsum W (List.replicate ds.length c)) % Fm N : ℕ) : ℤ) ≡
      ev (2 ^ W) (ds.map fun d : ℕ => (d : ℤ) - c) [ZMOD (Fm N : ℤ)] := by
  rw [ev_encode]
  set a := wsum W ds
  set b := wsum W (List.replicate ds.length c)
  have hb' : b ≤ a + Fm N := by unfold Fm; omega
  rw [Int.natCast_mod]
  refine (Int.mod_modEq _ _).trans ?_
  rw [Nat.cast_sub hb', Int.modEq_iff_dvd]
  push_cast
  exact ⟨-1, by ring⟩

end IntegerMultBounds.Schoenhage
