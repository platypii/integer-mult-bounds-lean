import IntegerMultBounds.Resampling.OffDiagSum
import IntegerMultBounds.NLogN.NeumannHalved

/-! The Neumann evaluation of `J̃'` on fixed-point words. An iterate is a list of
`2s` signed words (real and imaginary numerators, in coordinate order); one step
extends it cyclically by `m` records at both ends, runs the off-diagonal window
sums of the Gaussian line machine with stride one, truncates each accumulator to
the word width, negates it and adds the start vector. Every word stays exact:
the iterates of the word recursion are the numerators of the rounded Horner
iterates of `resampJNumH`, because those stay in the unit disk and on the grid. -/

namespace IntegerMultBounds.Resampling.NeumannWords

open IntegerMultBounds.NLogN (rho0 rhoC rdV normExp offDiagTermNum offDiagNum hornerNeumannR)
open IntegerMultBounds.Machine.GaussianLine (accR accI outWords)
open IntegerMultBounds.Machine.TwosComplement (signed addMod negWord signed_addMod signed_negWord
  signed_emod signed_bounds addMod_length negWord_length value_append)
open IntegerMultBounds.Counter (value)

section Words

/-- Two integers in the same window of width `N` that agree modulo `N` are equal. -/
theorem eq_of_emod_window {a b N : ℤ} (hN : 0 < N) (ha1 : -N ≤ 2 * a) (ha2 : 2 * a < N)
    (hb1 : -N ≤ 2 * b) (hb2 : 2 * b < N) (h : a % N = b % N) : a = b := by
  obtain ⟨c, hc⟩ : N ∣ a - b := Int.ModEq.dvd h.symm
  rcases lt_trichotomy c 0 with hc0 | hc0 | hc0
  · have : N * c ≤ -N := by nlinarith
    omega
  · subst hc0; omega
  · have : N ≤ N * c := by nlinarith
    omega

/-- Truncating a word keeps its signed value when the value fits the shorter width. -/
theorem signed_take (bs : List Bool) (w : ℕ) (hw : 1 ≤ w) (hwl : w ≤ bs.length)
    (h1 : -(2 : ℤ) ^ (w - 1) ≤ signed bs) (h2 : signed bs < 2 ^ (w - 1)) :
    signed (bs.take w) = signed bs := by
  have hlen : (bs.take w).length = w := by simp; omega
  have hne : bs.take w ≠ [] := by intro h; rw [h] at hlen; simp at hlen; omega
  obtain ⟨l1, l2⟩ := signed_bounds _ hne
  rw [hlen] at l1 l2
  have hv : (value bs : ℤ) = value (bs.take w) + 2 ^ w * value (bs.drop w) := by
    conv_lhs => rw [← List.take_append_drop w bs]
    rw [value_append, hlen]; push_cast; ring
  have hm1 : signed (bs.take w) % 2 ^ w = (value (bs.take w) : ℤ) := by
    have := signed_emod (bs.take w); rwa [hlen] at this
  have hdvd : (2 : ℤ) ^ w ∣ 2 ^ bs.length := pow_dvd_pow 2 hwl
  have hm2 : signed bs % 2 ^ w = (value (bs.take w) : ℤ) := by
    rw [← Int.emod_emod_of_dvd _ hdvd, signed_emod, hv, Int.add_mul_emod_self_left]
    exact Int.emod_eq_of_lt (by positivity) (by have := Counter.value_lt (bs.take w); rw [hlen] at this; exact_mod_cast this)
  have hp : (2 : ℤ) ^ w = 2 * 2 ^ (w - 1) := by rw [← pow_succ']; congr 1; omega
  refine eq_of_emod_window (N := 2 ^ w) (by positivity) ?_ ?_ ?_ ?_ (hm1.trans hm2.symm) <;>
    rw [hp] <;> linarith

end Words

section Recursion

/-- The input record of extended position `q`: `(q - m) mod s`. -/
def cycIdx (s m q : ℕ) : ℕ := (((q : ℤ) - m) % s).toNat

/-- The cyclic extension of an iterate by `m` records at both ends (and one more
record on the right), as `2 (s + 2m + 1)` words. -/
def ext (s m : ℕ) (ys : List (List Bool)) : List (List Bool) :=
  (List.range (2 * (s + 2 * m + 1))).map fun i => ys.getD (2 * cycIdx s m (i / 2) + i % 2) []

theorem ext_length (s m : ℕ) (ys : List (List Bool)) : (ext s m ys).length = 2 * (s + 2 * m + 1) := by
  simp [ext]

theorem ext_getD (s m : ℕ) (ys : List (List Bool)) (i : ℕ) (hi : i < 2 * (s + 2 * m + 1)) :
    (ext s m ys).getD i [] = ys.getD (2 * cycIdx s m (i / 2) + i % 2) [] := by
  simp [ext, List.getD_eq_getElem?_getD, hi]

theorem ext_even (s m : ℕ) (ys : List (List Bool)) (q : ℕ) (hq : q < s + 2 * m) :
    (ext s m ys).getD (2 * q) [] = ys.getD (2 * cycIdx s m q) [] := by
  rw [ext_getD _ _ _ _ (by omega), show 2 * q / 2 = q by omega, show 2 * q % 2 = 0 by omega, add_zero]

theorem ext_odd (s m : ℕ) (ys : List (List Bool)) (q : ℕ) (hq : q < s + 2 * m) :
    (ext s m ys).getD (2 * q + 1) [] = ys.getD (2 * cycIdx s m q + 1) [] := by
  rw [ext_getD _ _ _ _ (by omega), show (2 * q + 1) / 2 = q by omega, show (2 * q + 1) % 2 = 1 by omega]

theorem cycIdx_lt (s m q : ℕ) (hs : 0 < s) : cycIdx s m q < s := by
  unfold cycIdx
  have h1 := Int.emod_nonneg ((q : ℤ) - m) (by omega : (s : ℤ) ≠ 0)
  have h2 := Int.emod_lt_of_pos ((q : ℤ) - m) (by omega : (0 : ℤ) < s)
  omega

theorem getD_mem' (ws : List (List Bool)) (i : ℕ) (hi : i < ws.length) : ws.getD i [] ∈ ws := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
  exact List.getElem_mem hi

theorem ext_mem (s m : ℕ) (ys : List (List Bool)) (hs : 0 < s) (hyl : ys.length = 2 * s) :
    ∀ x ∈ ext s m ys, x ∈ ys := by
  intro x hx
  simp only [ext, List.mem_map, List.mem_range] at hx
  obtain ⟨i, _, rfl⟩ := hx
  have := cycIdx_lt s m (i / 2) hs
  exact getD_mem' _ _ (by have := Nat.mod_lt i (by omega : 0 < 2); omega)

/-- One subtraction step: `v0 - trunc_w e`, word by word. -/
def nextWords (v0 es : List (List Bool)) (w : ℕ) : List (List Bool) :=
  (List.range v0.length).map fun i => addMod (negWord ((es.getD i []).take w)) (v0.getD i [])

theorem nextWords_length (v0 es : List (List Bool)) (w : ℕ) : (nextWords v0 es w).length = v0.length := by
  simp [nextWords]

theorem nextWords_getD (v0 es : List (List Bool)) (w i : ℕ) (hi : i < v0.length) :
    (nextWords v0 es w).getD i [] = addMod (negWord ((es.getD i []).take w)) (v0.getD i []) := by
  simp [nextWords, List.getD_eq_getElem?_getD, hi]

/-- The word iterates of the Neumann evaluation with weight words `wt`. -/
def iter (wt v0 : List (List Bool)) (s m p w W : ℕ) : ℕ → List (List Bool)
  | 0 => v0
  | K + 1 => nextWords v0 (outWords wt (ext s m (iter wt v0 s m p w W K)) s s m p w W s) w

theorem outWords_length (wt us : List (List Bool)) (s t m p w W n : ℕ) :
    (outWords wt us s t m p w W n).length = 2 * n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [outWords, ih]; ring

theorem outWords_even (wt us : List (List Bool)) (s t m p w W n k : ℕ) (hk : k < n) :
    (outWords wt us s t m p w W n).getD (2 * k) [] = accR wt us s t m p w W k (2 * m + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [outWords, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge k n with h | h
    · rw [List.getElem?_append_left (by rw [outWords_length]; omega), ← List.getD_eq_getElem?_getD, ih h]
    · have : k = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [outWords_length]), outWords_length]
      simp

theorem outWords_odd (wt us : List (List Bool)) (s t m p w W n k : ℕ) (hk : k < n) :
    (outWords wt us s t m p w W n).getD (2 * k + 1) [] = accI wt us s t m p w W k (2 * m + 1) := by
  induction n with
  | zero => omega
  | succ n ih =>
    rw [outWords, List.getD_eq_getElem?_getD]
    rcases Nat.lt_or_ge k n with h | h
    · rw [List.getElem?_append_left (by rw [outWords_length]; omega), ← List.getD_eq_getElem?_getD, ih h]
    · have : k = n := by omega
      subst this
      rw [List.getElem?_append_right (by rw [outWords_length]; omega), outWords_length,
        show 2 * k + 1 - 2 * k = 1 by omega]
      simp

/-- The vector of numerators held by `2s` words. -/
noncomputable def vec (s p : ℕ) (ys : List (List Bool)) : ZMod s → ℂ := fun ℓ =>
  ⟨(signed (ys.getD (2 * ℓ.val) []) : ℝ) / 2 ^ p, (signed (ys.getD (2 * ℓ.val + 1) []) : ℝ) / 2 ^ p⟩

theorem rho0_int (n : ℤ) : rho0 (n : ℝ) = n := by
  unfold rho0; split_ifs <;> simp

/-- Grid values are fixed by the rounding. -/
theorem rhoC_grid (p : ℕ) (a b : ℤ) :
    rhoC p ⟨(a : ℝ) / 2 ^ p, (b : ℝ) / 2 ^ p⟩ = ⟨(a : ℝ) / 2 ^ p, (b : ℝ) / 2 ^ p⟩ := by
  have hp : (2 : ℝ) ^ p ≠ 0 := by positivity
  unfold rhoC
  simp only
  rw [mul_div_cancel₀ _ hp, mul_div_cancel₀ _ hp, rho0_int, rho0_int]

end Recursion

section Entry

/-- One entry of the subtraction step is exact when the accumulator is below
`2^(p+1)` and the difference below `2^p` in magnitude. -/
theorem sub_entry (a v : List Bool) (p w : ℕ) (hv : v.length = w) (ha : w ≤ a.length)
    (hw : p + 3 ≤ w) (hab : |signed a| ≤ 2 ^ (p + 1)) (hvb : |signed v - signed a| ≤ 2 ^ p) :
    signed (addMod (negWord (a.take w)) v) = signed v - signed a ∧
      (addMod (negWord (a.take w)) v).length = w := by
  have hP : (2 : ℤ) ^ (p + 1) * 2 ≤ 2 ^ (w - 1) := by
    rw [← pow_succ]; exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hP0 : (2 : ℤ) ^ p * 2 = 2 ^ (p + 1) := by rw [← pow_succ]
  have hpos : (0 : ℤ) < 2 ^ p := by positivity
  have hab' := abs_le.mp hab
  have hvb' := abs_le.mp hvb
  have htl : (a.take w).length = w := by simp; omega
  have hne : a.take w ≠ [] := by intro h; rw [h] at htl; simp at htl; omega
  have ht := signed_take a w (by omega) ha (by linarith) (by linarith)
  have hn := signed_negWord (a.take w) hne (by rw [ht, htl]; linarith)
  have hnl : (negWord (a.take w)).length = w := by rw [negWord_length, htl]
  have hvne : v ≠ [] := by intro h; rw [h] at hv; simp at hv; omega
  refine ⟨?_, by rw [addMod_length _ _ (by omega), hv]⟩
  rw [signed_addMod _ _ (by omega) hvne (by rw [hn, ht, hv]; linarith) (by rw [hn, ht, hv]; linarith), hn, ht]
  ring

end Entry

section Main

variable (wt v0 : List (List Bool)) (s m p w W : ℕ) [NeZero s] (ef : ZMod s → ℤ → ℝ)
  (hwt' : ∀ k j, k < s → j < 2 * m + 1 →
    signed (wt.getD (k * (2 * m + 1) + j) []) =
      if -(m : ℤ) + j = 0 then 0
      else rho0 (2 ^ p * ef (k : ZMod s) (-(m : ℤ) + j)))
  (hw : p + 3 ≤ w) (hwW : w ≤ W) (hW : ((2 * m + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
  (hwt : ∀ x ∈ wt, x.length = w) (hwb : ∀ x ∈ wt, |signed x| ≤ 2 ^ p)
  (hwtl : wt.length = s * (2 * m + 1))
  (hv0 : v0.length = 2 * s) (hv0w : ∀ x ∈ v0, x.length = w) (hs : 0 < s)
  (hball : ∀ K, ‖hornerNeumannR (rdV p) (offDiagNum m (OffDiagSum.offTermW p ef)) (vec s p v0) K‖ ≤ 1)

/-- Words of a vector in the unit disk have numerators of magnitude at most `2^p`. -/
theorem num_bound (ys : List (List Bool)) (h : ‖vec s p ys‖ ≤ 1)
    (i : ℕ) (hi : i < 2 * s) : |signed (ys.getD i [])| ≤ 2 ^ p := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  set ℓ : ZMod s := ((i / 2 : ℕ) : ZMod s)
  have hℓ : ℓ.val = i / 2 := ZMod.val_natCast_of_lt (by omega)
  have hz := (norm_le_pi_norm (vec s p ys) ℓ).trans h
  have key : |(signed (ys.getD i []) : ℝ) / 2 ^ p| ≤ 1 := by
    rcases Nat.mod_two_eq_zero_or_one i with h2 | h2
    · have hi' : i = 2 * ℓ.val := by omega
      rw [hi']
      exact (Complex.abs_re_le_norm _).trans hz
    · have hi' : i = 2 * ℓ.val + 1 := by omega
      rw [hi']
      exact (Complex.abs_im_le_norm _).trans hz
  rw [abs_div, abs_of_pos hp, div_le_one hp] at key
  exact_mod_cast key

include hball in
theorem num_bound_iter (K : ℕ) (ys : List (List Bool)) (hyl : ys.length = 2 * s)
    (hK : hornerNeumannR (rdV p) (offDiagNum m (OffDiagSum.offTermW p ef)) (vec s p v0) K = vec s p ys) :
    ∀ x ∈ ys, |signed x| ≤ 2 ^ p := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := num_bound s p ys (hK ▸ hball K) i (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

theorem val_intCast_toNat (j : ℤ) (hs : 0 < s) : (j : ZMod s).val = (j % s).toNat := by
  have h := ZMod.val_intCast (n := s) j
  have h1 := Int.emod_nonneg j (by omega : (s : ℤ) ≠ 0)
  omega

include hwt' hw hwW hW hwt hwb hwtl hv0 hv0w hs hball in
/-- The word iterates hold the numerators of the rounded Horner iterates. -/
theorem iter_spec (K : ℕ) :
    (iter wt v0 s m p w W K).length = 2 * s ∧ (∀ x ∈ iter wt v0 s m p w W K, x.length = w) ∧
      hornerNeumannR (rdV p) (offDiagNum m (OffDiagSum.offTermW p ef)) (vec s p v0) K =
        vec s p (iter wt v0 s m p w W K) := by
  have hp : (0 : ℝ) < 2 ^ p := by positivity
  induction K with
  | zero => exact ⟨hv0, hv0w, rfl⟩
  | succ K ih =>
    obtain ⟨hyl, hyw, hyv⟩ := ih
    set ys := iter wt v0 s m p w W K with hys
    set ar : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat) [])
    set ai : ℤ → ℤ := fun j => signed (ys.getD (2 * (j % s).toNat + 1) [])
    have hu : ∀ j : ℤ, vec s p ys (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩ := by
      intro j; simp only [vec, val_intCast_toNat s j hs, ar, ai]
    have hre : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q) []) = ar ((q : ℤ) - m) := by
      intro q hq; rw [ext_even _ _ _ _ hq]; rfl
    have him : ∀ q, q < s + 2 * m → signed ((ext s m ys).getD (2 * q + 1) []) = ai ((q : ℤ) - m) := by
      intro q hq; rw [ext_odd _ _ _ _ hq]; rfl
    have hext : ∀ x ∈ ext s m ys, x ∈ ys := ext_mem s m ys hs hyl
    have hyb := num_bound_iter (v0 := v0) (s := s) (m := m) (p := p) (ef := ef) hball K ys hyl hyv
    have hacc := fun k (hk : k < s) => IntegerMultBounds.Resampling.OffDiagSum.accumulators_eq wt
      (ext s m ys) s m p w W ef (vec s p ys) ar ai hu hwt' hre him (by omega) hwW hW hwt
      (fun x hx => hyw x (hext x hx)) hwb (fun x hx => hyb x (hext x hx)) hwtl
      (by rw [ext_length]) hs k hk
    -- the next Horner iterate, entry by entry
    have hstep : ∀ ℓ : ZMod s,
        hornerNeumannR (rdV p) (offDiagNum m (OffDiagSum.offTermW p ef)) (vec s p v0) (K + 1) ℓ =
          ⟨((signed (v0.getD (2 * ℓ.val) []) -
              signed (accR wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℤ) : ℝ) / 2 ^ p,
           ((signed (v0.getD (2 * ℓ.val + 1) []) -
              signed (accI wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℤ) : ℝ) / 2 ^ p⟩ := by
      intro ℓ
      have hk := ZMod.val_lt ℓ
      have h := hacc ℓ.val hk
      rw [ZMod.natCast_zmod_val] at h
      show rdV p (vec s p v0 - offDiagNum m (OffDiagSum.offTermW p ef) (hornerNeumannR (rdV p) (offDiagNum m (OffDiagSum.offTermW p ef)) (vec s p v0) K)) ℓ = _
      rw [hyv]
      simp only [rdV, Pi.sub_apply]
      rw [h]
      have e : vec s p v0 ℓ - ⟨(signed (accR wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℝ) / 2 ^ p,
          (signed (accI wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℝ) / 2 ^ p⟩ =
          ⟨((signed (v0.getD (2 * ℓ.val) []) -
              signed (accR wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℤ) : ℝ) / 2 ^ p,
           ((signed (v0.getD (2 * ℓ.val + 1) []) -
              signed (accI wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1)) : ℤ) : ℝ) / 2 ^ p⟩ := by
        apply Complex.ext <;> simp only [vec, Complex.sub_re, Complex.sub_im] <;> push_cast <;> ring
      rw [e, rhoC_grid]
    have hb1 := hball (K + 1)
    have hb0 := hball 0
    have hv0b := num_bound s p v0 hb0
    refine ⟨by rw [iter, nextWords_length, hv0], ?_, ?_⟩
    · intro x hx
      rw [iter] at hx
      simp only [nextWords, List.mem_map, List.mem_range] at hx
      obtain ⟨i, hi, rfl⟩ := hx
      rw [addMod_length _ _ (by rw [negWord_length, hv0w _ (getD_mem' _ _ hi)]; simp)]
      exact hv0w _ (getD_mem' _ _ hi)
    · funext ℓ
      have hk := ZMod.val_lt ℓ
      have hz := (norm_le_pi_norm _ ℓ).trans hb1
      rw [hstep ℓ] at hz ⊢
      have hdr : |signed (v0.getD (2 * ℓ.val) []) -
          signed (accR wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1))| ≤ 2 ^ p := by
        have := (Complex.abs_re_le_norm _).trans hz
        simp only at this
        rw [abs_div, abs_of_pos hp, div_le_one hp] at this
        exact_mod_cast this
      have hdi : |signed (v0.getD (2 * ℓ.val + 1) []) -
          signed (accI wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1))| ≤ 2 ^ p := by
        have := (Complex.abs_im_le_norm _).trans hz
        simp only at this
        rw [abs_div, abs_of_pos hp, div_le_one hp] at this
        exact_mod_cast this
      have hvr := hv0b (2 * ℓ.val) (by omega)
      have hvi := hv0b (2 * ℓ.val + 1) (by omega)
      have hpow : (2 : ℤ) ^ (p + 1) = 2 ^ p + 2 ^ p := by ring
      have har : |signed (accR wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1))| ≤ 2 ^ (p + 1) := by
        rw [abs_le] at hdr hvr ⊢; constructor <;> linarith
      have hai : |signed (accI wt (ext s m ys) s s m p w W ℓ.val (2 * m + 1))| ≤ 2 ^ (p + 1) := by
        rw [abs_le] at hdi hvi ⊢; constructor <;> linarith
      have er := sub_entry _ _ p w (hv0w _ (getD_mem' _ _ (by omega)))
        (by rw [IntegerMultBounds.Machine.GaussianLine.accR_length _ _ _ _ _ _ _ _ _ hwW]; exact hwW) hw har hdr
      have ei := sub_entry _ _ p w (hv0w _ (getD_mem' _ _ (by omega)))
        (by rw [IntegerMultBounds.Machine.GaussianLine.accI_length _ _ _ _ _ _ _ _ _ hwW]; exact hwW) hw hai hdi
      simp only [vec]
      rw [iter, ← hys, nextWords_getD _ _ _ _ (by omega), nextWords_getD _ _ _ _ (by omega),
        outWords_even _ _ _ _ _ _ _ _ _ _ hk, outWords_odd _ _ _ _ _ _ _ _ _ _ hk, er.1, ei.1]

end Main

section Corollary

open IntegerMultBounds.NLogN (resampJNumH hornerNeumannR_err_unit opNorm_offDiagCLM_le_unit
  offDiagNum_err_unit_sqrt room_of_le sqrtWindow sqrtWindow_bound sqrtWindow_le norm_rdV_sub_le
  norm_rdV_le offDiagCLM)

variable {s t : ℕ} [NeZero s] [NeZero t] {α : ℝ}

/-- With the square-root window, `p` word iterates from the halved input give
`J̃' v` exactly: `resampJNumH p (⌊√p⌋+1) s t α v = vec (iter p)`. -/
theorem resampJNumH_eq_iter (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    {p w W : ℕ} (hp : 13 ≤ p) (wt v0 : List (List Bool))
    (hwt' : ∀ k j, k < s → j < 2 * sqrtWindow p + 1 →
      signed (wt.getD (k * (2 * sqrtWindow p + 1) + j) []) =
        if -(sqrtWindow p : ℤ) + j = 0 then 0
        else rho0 (2 ^ p * Real.exp (normExp s t α (k : ZMod s).val (-(sqrtWindow p : ℤ) + j))))
    (hw : p + 3 ≤ w) (hwW : w ≤ W)
    (hW : ((2 * sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hwt : ∀ x ∈ wt, x.length = w) (hwb : ∀ x ∈ wt, |signed x| ≤ 2 ^ p)
    (hwtl : wt.length = s * (2 * sqrtWindow p + 1))
    (hv0 : v0.length = 2 * s) (hv0w : ∀ x ∈ v0, x.length = w)
    (v : ZMod s → ℂ) (hv : ‖v‖ ≤ 1) (hv0v : vec s p v0 = rdV p ((1 / 2 : ℂ) • v)) :
    resampJNumH p (sqrtWindow p) s t α v = vec s p (iter wt v0 s (sqrtWindow p) p w W p) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hhalf : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hv0b : ‖vec s p v0‖ ≤ 1 / 2 := by rw [hv0v]; exact (norm_rdV_le p _).trans hhalf
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 → 2 ^ p * ‖offDiagNum (sqrtWindow p) (offDiagTermNum p s t α) y -
      offDiagCLM s t α y‖ ≤ 6 * (2 * (sqrtWindow p : ℝ)) + 6 :=
    fun y hy => offDiagNum_err_unit_sqrt hst hα hθ (sqrtWindow_bound p) y hy
  have hroom : 25 * (6 * (2 * (sqrtWindow p : ℝ)) + 6) ≤ 2 ^ p := room_of_le (sqrtWindow_le p (by omega)) hp
  have hball : ∀ K, ‖hornerNeumannR (rdV p) (offDiagNum (sqrtWindow p)
      (OffDiagSum.offTermW p (fun ℓ h => Real.exp (normExp s t α ℓ.val h)))) (vec s p v0) K‖ ≤ 1 := fun K =>
    (hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b K).1
  have h := (iter_spec wt v0 s (sqrtWindow p) p w W (fun ℓ h => Real.exp (normExp s t α ℓ.val h)) hwt' hw hwW hW hwt hwb hwtl hv0 hv0w hs
    hball p).2.2
  unfold resampJNumH
  rw [← hv0v]
  exact h

end Corollary

end IntegerMultBounds.Resampling.NeumannWords
