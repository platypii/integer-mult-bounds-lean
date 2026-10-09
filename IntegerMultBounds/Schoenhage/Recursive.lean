import IntegerMultBounds.Schoenhage.IterCorrect
import IntegerMultBounds.Schoenhage.Schedule

/-! The whole Schönhage–Strassen recursion as the tapes compute it, on
natural-number residues. A level with ring size `N` (modulus `2^N + 1`) uses
`k = kOf N`, `K = 2^k`, pieces of `M = pieceOf N` bits and the next ring size
`N' = nextN N`: each operand is cut into pieces and transformed layer by layer
(`xs`), the `K` pointwise products are computed recursively, inverted layer by
layer, divided by `2^k` as a multiplication by `-2^(N'-k)` (`descale`), lifted
to signed representatives (`liftN`) and evaluated at `2^M` modulo `2^N + 1`
(`recomb`). Below `N0` the product is taken directly. Proved: `ssMul N x y`
is `x y mod 2^N + 1` for residues whenever `2^(kOf N) ∣ N` (`ssMul_correct`),
with the value bounds and lengths of every intermediate list. -/

namespace IntegerMultBounds.Schoenhage

open Schedule Polynomial

/-- Division by `2^k` modulo `2^N + 1`: multiplication by `2^(2N - k) = -2^(N - k)`. -/
def descale (N k w : ℕ) : ℕ := (Fm N - 2 ^ (N - k) * w % Fm N) % Fm N

/-- The signed representative of a residue modulo `2^N + 1`. -/
def liftN (N c : ℕ) : ℤ := if 2 * c < Fm N then c else (c : ℤ) - Fm N

/-- Evaluation of the signed coefficients at `2^M`, modulo `2^N + 1`. -/
noncomputable def recomb (N M : ℕ) (cs : List ℤ) : ℕ := (((poly cs).eval (2 ^ M : ℤ)) % (Fm N : ℤ)).toNat

/-- The transformed pieces of an operand. -/
def xs (N x : ℕ) : List ℕ :=
  fwdIter (nextN N) (kOf N) (2 ^ kOf N / 2) [nextN N / 2] (pieces (pieceOf N) (2 ^ kOf N) x)

/-- The up-sweep of a level from the `K` pointwise products. -/
noncomputable def levelOut (N : ℕ) (prods : List ℕ) : ℕ :=
  recomb N (pieceOf N)
    ((invIter (nextN N) (kOf N) (kOf N) prods).map fun w => liftN (nextN N) (descale (nextN N) (kOf N) w))

/-- Schönhage–Strassen multiplication modulo `2^N + 1`. -/
noncomputable def ssMul (N x y : ℕ) : ℕ :=
  if N < N0 then x * y % Fm N
  else levelOut N (List.zipWith (ssMul (nextN N)) (xs N x) (xs N y))
termination_by N
decreasing_by exact (next_facts (by omega)).2.2.2

theorem ssMul_eq (N x y : ℕ) : ssMul N x y = if N < N0 then x * y % Fm N
    else levelOut N (List.zipWith (ssMul (nextN N)) (xs N x) (xs N y)) := by
  rw [ssMul]

/-! ### Bounds and lengths -/

theorem recomb_lt (N M : ℕ) (cs : List ℤ) : recomb N M cs < Fm N := by
  unfold recomb
  have hF : (0 : ℤ) < Fm N := by exact_mod_cast Fm_pos N
  have h1 := Int.emod_nonneg ((poly cs).eval (2 ^ M : ℤ)) hF.ne'
  have h2 := Int.emod_lt_of_pos ((poly cs).eval (2 ^ M : ℤ)) hF
  omega

theorem ssMul_lt (N x y : ℕ) : ssMul N x y < Fm N := by
  rw [ssMul_eq]; split_ifs
  · exact Nat.mod_lt _ (Fm_pos N)
  · exact recomb_lt _ _ _

theorem descale_lt (N k w : ℕ) : descale N k w < Fm N := Nat.mod_lt _ (Fm_pos N)

theorem xs_length (N x : ℕ) : (xs N x).length = 2 ^ kOf N := by
  unfold xs
  rw [fwdIter_length _ _ _ _ _ rfl (by simp [length_pieces]), length_pieces]

theorem pieces_lt {N x : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) :
    ∀ p ∈ pieces (pieceOf N) (2 ^ kOf N) x, p < Fm (nextN N) := by
  intro p hp
  have hs := split_exact hk
  have hle : x ≤ 2 ^ (pieceOf N * 2 ^ kOf N) := by
    rw [mul_comm, ← hs]; unfold Fm at hx; omega
  have h1 := pieces_le _ _ x hle p hp
  have h2 := (next_facts hN).2.1
  have h3 : 2 ^ pieceOf N ≤ 2 ^ nextN N := Nat.pow_le_pow_right (by norm_num) (by omega)
  unfold Fm; omega

theorem xs_lt {N x : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N) :
    ∀ u ∈ xs N x, u < Fm (nextN N) :=
  fwdIter_lt _ _ _ _ _ (pieces_lt hN hk hx)

theorem prods_lt (N : ℕ) (U V : List ℕ) : ∀ p ∈ List.zipWith (ssMul (nextN N)) U V, p < Fm (nextN N) := by
  intro p hp
  obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
  simp only [List.getElem_zipWith]
  exact ssMul_lt _ _ _

theorem prods_length (N x y : ℕ) :
    (List.zipWith (ssMul (nextN N)) (xs N x) (xs N y)).length = 2 ^ kOf N := by
  simp [xs_length]

theorem invIter_out_lt (N : ℕ) (P : List ℕ) (hP : ∀ p ∈ P, p < Fm (nextN N)) :
    ∀ w ∈ invIter (nextN N) (kOf N) (kOf N) P, w < Fm (nextN N) :=
  invIter_lt _ _ _ _ hP

/-! ### Correctness -/

theorem liftN_eq (N w : ℕ) (hw : w < Fm N) : liftN N w = lift N (w : ZMod (2 ^ N + 1)) := by
  have hv : (w : ZMod (2 ^ N + 1)).val = w := ZMod.val_natCast_of_lt (by unfold Fm at hw; exact hw)
  unfold liftN lift; rw [hv]; unfold Fm; rfl

theorem descale_cast {N k : ℕ} (hk : k ≤ N) (w : ℕ) :
    ((descale N k w : ℕ) : ZMod (2 ^ N + 1)) = (2 : ZMod (2 ^ N + 1)) ^ (2 * N - k) * w := by
  unfold descale
  rw [cast_mod_Fm, Nat.cast_sub (Nat.mod_lt _ (Fm_pos N)).le, cast_mod_Fm, cast_Fm]
  push_cast
  rw [show 2 * N - k = N + (N - k) by omega, pow_add, two_pow_N]
  ring

theorem map_zipWith_cast (F : ℕ) (U V : List ℕ) :
    (List.zipWith (fun u v => u * v % F) U V).map (Nat.cast : ℕ → ZMod F) =
      List.zipWith (· * ·) (U.map (↑)) (V.map (↑)) := by
  induction U generalizing V with
  | nil => simp
  | cons u U ih =>
    cases V with
    | nil => simp
    | cons v V => simp [ih, ZMod.natCast_mod]

/-- One level is correct given correct pointwise products. -/
theorem levelOut_correct {N x y : ℕ} (hN : N0 ≤ N) (hk : 2 ^ kOf N ∣ N) (hx : x < Fm N)
    (hy : y < Fm N) :
    levelOut N (List.zipWith (fun u v => u * v % Fm (nextN N)) (xs N x) (xs N y)) = x * y % Fm N := by
  set k := kOf N
  set M := pieceOf N
  set N' := nextN N
  obtain ⟨-, hM, -, -⟩ := next_facts hN
  have hkN' : 2 ^ k ∣ N' := dvd_next N
  have hs : N = 2 ^ k * M := split_exact hk
  have hkle : k ≤ N' := by
    have : k < 2 ^ k := Nat.lt_two_pow_self
    have := Nat.le_of_dvd (by have := (next_facts hN).2.1; omega) hkN'
    omega
  have hxle : x ≤ 2 ^ (M * 2 ^ k) := by rw [mul_comm, ← hs]; unfold Fm at hx; omega
  have hyle : y ≤ 2 ^ (M * 2 ^ k) := by rw [mul_comm, ← hs]; unfold Fm at hy; omega
  have hlc := level_correct hkN' (by omega) x y hxle hyle
  simp only at hlc
  -- the forward transforms
  have hfx : (xs N x).map (Nat.cast : ℕ → ZMod (2 ^ N' + 1)) =
      fwd ((2 : ZMod (2 ^ N' + 1)) ^ (N' / 2 ^ k)) (2 ^ k) k (2 ^ k) ((pieces M (2 ^ k) x).map (↑)) := by
    unfold xs; rw [fwdIter_eq_fwd hkN' _ (length_pieces _ _ _)]
  have hfy : (xs N y).map (Nat.cast : ℕ → ZMod (2 ^ N' + 1)) =
      fwd ((2 : ZMod (2 ^ N' + 1)) ^ (N' / 2 ^ k)) (2 ^ k) k (2 ^ k) ((pieces M (2 ^ k) y).map (↑)) := by
    unfold xs; rw [fwdIter_eq_fwd hkN' _ (length_pieces _ _ _)]
  set P := List.zipWith (fun u v => u * v % Fm N') (xs N x) (xs N y)
  have hPl : P.length = 2 ^ k := by simp [P, xs_length, k]
  have hPlt : ∀ p ∈ P, p < Fm N' := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.mp hp
    simp only [P, List.getElem_zipWith]; exact Nat.mod_lt _ (Fm_pos _)
  have hPc : P.map (Nat.cast : ℕ → ZMod (2 ^ N' + 1)) =
      List.zipWith (· * ·) ((xs N x).map (↑)) ((xs N y).map (↑)) := by
    simp only [P]; unfold Fm; exact map_zipWith_cast _ _ _
  have hinv := invIter_eq_inv hkN' P hPl hPlt
  rw [hPc, hfx, hfy] at hinv
  -- the coefficients
  have hcoef : (invIter N' k k P).map (fun w => liftN N' (descale N' k w)) =
      (inv ((2 : ZMod (2 ^ N' + 1)) ^ (N' / 2 ^ k)) (2 ^ k) k (2 ^ k)
        (List.zipWith (· * ·)
          (fwd ((2 : ZMod (2 ^ N' + 1)) ^ (N' / 2 ^ k)) (2 ^ k) k (2 ^ k) ((pieces M (2 ^ k) x).map (↑)))
          (fwd ((2 : ZMod (2 ^ N' + 1)) ^ (N' / 2 ^ k)) (2 ^ k) k (2 ^ k)
            ((pieces M (2 ^ k) y).map (↑))))).map
        (fun r => lift N' ((2 : ZMod (2 ^ N' + 1)) ^ (2 * N' - k) * r)) := by
    rw [← hinv, List.map_map]
    refine List.map_congr_left fun w hw => ?_
    have hwl := invIter_lt _ _ _ _ hPlt w hw
    simp only [Function.comp_apply]
    rw [liftN_eq _ _ (descale_lt _ _ _), descale_cast hkle]
  unfold levelOut recomb
  rw [hcoef]
  have hF : (Fm N : ℤ) = 2 ^ (M * 2 ^ k) + 1 := by unfold Fm; rw [hs, mul_comm]; push_cast; ring
  rw [hF, Int.ModEq.eq hlc, ← hF]
  have : ((x : ℤ) * y) % (Fm N : ℤ) = ((x * y % Fm N : ℕ) : ℤ) := by push_cast; rfl
  rw [this]; exact Int.toNat_natCast _

/-- Schönhage–Strassen multiplication is multiplication modulo `2^N + 1`. -/
theorem ssMul_correct : ∀ N x y, 2 ^ kOf N ∣ N → x < Fm N → y < Fm N → ssMul N x y = x * y % Fm N := by
  intro N
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    intro x y hk hx hy
    rw [ssMul_eq]
    split_ifs with hN
    · rfl
    · rw [not_lt] at hN
      have hlt := (next_facts hN).2.2.2
      have hk' := (dvd_chain hN).2.2
      have hP : List.zipWith (ssMul (nextN N)) (xs N x) (xs N y) =
          List.zipWith (fun u v => u * v % Fm (nextN N)) (xs N x) (xs N y) := by
        apply List.zipWith_congr
        rw [List.forall₂_iff_get]
        refine ⟨by simp [xs_length], fun i hi1 hi2 => ?_⟩
        exact ih _ hlt _ _ hk' (xs_lt hN hk hx _ (List.getElem_mem hi1))
          (xs_lt hN hk hy _ (List.getElem_mem hi2))
      rw [hP]
      exact levelOut_correct hN hk hx hy

end IntegerMultBounds.Schoenhage
