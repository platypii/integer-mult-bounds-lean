import IntegerMultBounds.Resampling.B0Tape
import IntegerMultBounds.NLogN.NeumannHalved
import IntegerMultBounds.Resampling.TabledMaps

/-! The words written by the `B̃₀` tape machine are the numerators of the
manuscript's clamp-free `B̃₀ = D̃' J̃' C`: the selected words represent
`C w`, a window-radius-zero step with weights `-2^(p-1)` halves them with the
rounding of `rdV`, the Neumann loop gives `J̃'` (`NeumannWords`), and a
window-radius-zero step with weights `-ρ(2^p d')` is `D̃'`. -/

namespace IntegerMultBounds.Resampling.B0Value

open IntegerMultBounds.Machine
open IntegerMultBounds.Machine.GaussianLine (outWords accR accI termR termI centre)
open IntegerMultBounds.Machine.TwosComplement (signed)
open IntegerMultBounds.Resampling.NeumannWords (ext nextWords vec cycIdx iter)
open IntegerMultBounds.Resampling.B0Words (vsel oneStep)
open IntegerMultBounds.NLogN (rho0 rhoC rdV rowIndexNat)

section OneStep

variable (wt zeros y : List (List Bool)) (s p w : ℕ)
  (hs : 0 < s) (hw : p + 3 ≤ w) (hwt : ∀ x ∈ wt, x.length = w) (hwtl : wt.length = s * (2 * 0 + 1))
  (hwtb : ∀ x ∈ wt, |signed x| ≤ 2 ^ p) (hyw : ∀ x ∈ y, x.length = w) (hyl : y.length = 2 * s)
  (hyb : ∀ x ∈ y, |signed x| ≤ 2 ^ p) (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s)

theorem ext_zero_get (k : ℕ) (hk : k < s) (r : ℕ) (hr : r < 2) :
    (ext s 0 y).getD (2 * k + r) [] = y.getD (2 * k + r) [] := by
  rw [NeumannWords.ext_getD _ _ _ _ (by omega), show (2 * k + r) / 2 = k by omega,
    show (2 * k + r) % 2 = r by omega, NeumannStep.cyc_mid s 0 k (by omega) (by omega), Nat.sub_zero]

include hs hw hwt hwtl hwtb hyw hyl hyb hz hzl in
/-- One window-radius-zero step with zero start words: each output word is
minus the truncated product of the weight with the input word. -/
theorem oneStep_signed (k : ℕ) (hk : k < s) (r : ℕ) (hr : r < 2) :
    signed ((oneStep wt zeros s p w y).getD (2 * k + r) []) =
      -((signed (wt.getD k []) * signed (y.getD (2 * k + r) [])).tdiv (2 ^ p)) := by
  have hext := NeumannWords.ext_mem s 0 y hs hyl
  have hul : 2 * (s + 2 * 0 + 1) ≤ (ext s 0 y).length := by rw [NeumannWords.ext_length]
  have hW : ((2 * 0 + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (w - 1) := by
    have : (2 : ℤ) ^ p < 2 ^ (w - 1) := pow_lt_pow_right₀ (by norm_num) (by omega)
    simpa using this
  have hcen := Resampling.OffDiagSum.centre_self s k hs
  have hk1 : k * (2 * 0 + 1) + 0 = k := by ring
  -- the accumulator word
  set A := (if r = 0 then accR wt (ext s 0 y) s s 0 p w w k (2 * 0 + 1)
    else accI wt (ext s 0 y) s s 0 p w w k (2 * 0 + 1)) with hA
  have hAv : signed A = (signed (wt.getD k []) * signed (y.getD (2 * k + r) [])).tdiv (2 ^ p) := by
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · simp only [hA, ite_true]
      rw [GaussianLine.accR_signed wt (ext s 0 y) s s 0 p w w (by omega) le_rfl hW hwt
        (fun x hx => hyw x (hext x hx)) hwtb (fun x hx => hyb x (hext x hx)) hwtl hul le_rfl hs k hk _ le_rfl]
      rw [show 2 * 0 + 1 = 1 by norm_num, Finset.sum_range_one]
      unfold termR
      rw [hcen, show k * 1 + 0 = k by ring, show 2 * k + 2 * 0 = 2 * k + 0 by ring,
        ext_zero_get y s k hk 0 (by omega), add_zero]
    · simp only [hA, one_ne_zero, ite_false]
      rw [GaussianLine.accI_signed wt (ext s 0 y) s s 0 p w w (by omega) le_rfl hW hwt
        (fun x hx => hyw x (hext x hx)) hwtb (fun x hx => hyb x (hext x hx)) hwtl hul le_rfl hs k hk _ le_rfl]
      rw [show 2 * 0 + 1 = 1 by norm_num, Finset.sum_range_one]
      unfold termI
      rw [hcen, show k * 1 + 0 = k by ring, show 2 * k + 2 * 0 + 1 = 2 * k + 1 by ring,
        ext_zero_get y s k hk 1 (by omega)]
  have hwk : wt.getD k [] ∈ wt := NeumannWords.getD_mem' _ _ (by rw [hwtl]; omega)
  have hyk : y.getD (2 * k + r) [] ∈ y := NeumannWords.getD_mem' _ _ (by omega)
  have hAb : |signed A| ≤ 2 ^ p := by
    rw [hAv]; exact GaussianLine.abs_tdiv_pow_le _ _ p (hwtb _ hwk) (hyb _ hyk)
  have hget : (outWords wt (ext s 0 y) s s 0 p w w s).getD (2 * k + r) [] = A := by
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · simp only [hA, ite_true, add_zero]; exact NeumannWords.outWords_even _ _ _ _ _ _ _ _ _ _ hk
    · simp only [hA, one_ne_zero, ite_false]; exact NeumannWords.outWords_odd _ _ _ _ _ _ _ _ _ _ hk
  have hzk := hz _ (NeumannWords.getD_mem' zeros (2 * k + r) (by omega))
  have hAl : A.length = w := by
    rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl
    · simp only [hA, ite_true]; exact GaussianLine.accR_length _ _ _ _ _ _ _ _ _ le_rfl _
    · simp only [hA, one_ne_zero, ite_false]; exact GaussianLine.accI_length _ _ _ _ _ _ _ _ _ le_rfl _
  have hpow : (2 : ℤ) ^ p ≤ 2 ^ (p + 1) := pow_le_pow_right₀ (by norm_num) (by omega)
  have e := NeumannWords.sub_entry A (zeros.getD (2 * k + r) []) p w (by rw [hzk]; simp) (by rw [hAl]) hw
    (hAb.trans hpow) (by rw [hzk, GaussianLine.signed_zero_word, zero_sub, abs_neg]; exact hAb)
  unfold oneStep
  rw [NeumannWords.nextWords_getD _ _ _ _ (by omega), hget, e.1, hzk, GaussianLine.signed_zero_word, zero_sub, hAv]

end OneStep

section Vectors

theorem flatMap_pair_getD (L : List ℕ) (f g : ℕ → List Bool) (i r : ℕ) (hi : i < L.length) (hr : r < 2) :
    (L.flatMap fun j => [f j, g j]).getD (2 * i + r) [] = if r = 0 then f L[i] else g L[i] := by
  induction L generalizing i with
  | nil => simp at hi
  | cons x L ih =>
    rw [List.flatMap_cons]
    rcases i with _ | i
    · rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> simp
    · rw [show 2 * (i + 1) + r = (2 * i + r) + 2 by ring, List.getD_append_right _ _ _ _ (by simp)]
      simp only [List.length_cons, List.length_nil, show 2 * i + r + 2 - (0 + 1 + 1) = 2 * i + r by omega]
      rw [ih i (by simp at hi; omega)]
      simp

theorem vsel_get (win : List (List Bool)) (s t j r : ℕ) [NeZero s] (hj : j < s) (hr : r < 2) :
    (vsel win s t).getD (2 * j + r) [] = win.getD (2 * rowIndexNat s t (j : ZMod s) + r) [] := by
  unfold vsel
  rw [flatMap_pair_getD _ _ _ _ _ (by simpa using hj) hr, List.getElem_range]
  rcases (by omega : r = 0 ∨ r = 1) with rfl | rfl <;> simp

variable {s t : ℕ} [NeZero s] [NeZero t]

omit [NeZero t] in
/-- The selected words represent `C w`. -/
theorem sel_vec (p : ℕ) (hst : s < t) (win : List (List Bool)) :
    vec s p (vsel win s t) = NLogN.rowSelect s t (vec t p win) := by
  funext ℓ
  have hℓ := ZMod.val_lt ℓ
  simp only [vec, NLogN.rowSelect, NLogN.rowIndex_val (s := s) (t := t) hst]
  rw [show 2 * ℓ.val = 2 * ℓ.val + 0 by ring, vsel_get win s t _ 0 hℓ (by omega), vsel_get win s t _ 1 hℓ (by omega),
    ZMod.natCast_zmod_val, add_zero]

end Vectors

section Steps

variable {s : ℕ} [NeZero s] (zeros Y : List (List Bool)) (p w : ℕ)
  (hs : 0 < s) (hw : p + 3 ≤ w) (hyw : ∀ x ∈ Y, x.length = w) (hyl : Y.length = 2 * s)
  (hyb : ∀ x ∈ Y, |signed x| ≤ 2 ^ p) (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s)

include hs hw hyw hyl hyb hz hzl in
/-- A step with weights `-2^(p-1)` is the rounded halving. -/
theorem half_vec (wtH : List (List Bool)) (hp : 1 ≤ p) (hwt : ∀ x ∈ wtH, x.length = w)
    (hwtl : wtH.length = s * (2 * 0 + 1)) (hwH : ∀ x ∈ wtH, signed x = -2 ^ (p - 1)) :
    vec s p (oneStep wtH zeros s p w Y) = rdV p ((1 / 2 : ℂ) • vec s p Y) := by
  have hwtb : ∀ x ∈ wtH, |signed x| ≤ 2 ^ p := by
    intro x hx; rw [hwH x hx, abs_neg, abs_of_pos (by positivity)]
    exact pow_le_pow_right₀ (by norm_num) (by omega)
  have hpp : (2 : ℤ) ^ p = 2 ^ (p - 1) * 2 := by rw [← pow_succ]; congr 1; omega
  have key : ∀ y : ℤ, -((-(2 : ℤ) ^ (p - 1) * y).tdiv (2 ^ p)) = y.tdiv (2 ^ 1) := by
    intro y
    rw [neg_mul, Int.neg_tdiv, neg_neg, hpp, Int.mul_tdiv_mul_of_pos _ _ (by positivity), pow_one]
  have hr : ∀ y : ℤ, rho0 (2 ^ p * (1 / 2 * ((y : ℝ) / 2 ^ p))) = y.tdiv (2 ^ 1) := by
    intro y
    rw [← WindowSum.rho0_div_pow]
    congr 1
    field_simp
  funext ℓ
  have hk := ZMod.val_lt ℓ
  have hwk : wtH.getD ℓ.val [] ∈ wtH := NeumannWords.getD_mem' _ _ (by rw [hwtl]; omega)
  have e0 := oneStep_signed wtH zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 0 (by omega)
  have e1 := oneStep_signed wtH zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 1 (by omega)
  rw [add_zero, hwH _ hwk, key] at e0
  rw [hwH _ hwk, key] at e1
  apply Complex.ext
  · simp only [vec, rdV, NLogN.rhoC, Pi.smul_apply, smul_eq_mul]
    rw [e0, show ((1 / 2 : ℂ) * ⟨(signed (Y.getD (2 * ℓ.val) []) : ℝ) / 2 ^ p,
        (signed (Y.getD (2 * ℓ.val + 1) []) : ℝ) / 2 ^ p⟩).re =
        1 / 2 * ((signed (Y.getD (2 * ℓ.val) []) : ℝ) / 2 ^ p) by simp, hr]
  · simp only [vec, rdV, NLogN.rhoC, Pi.smul_apply, smul_eq_mul]
    rw [e1, show ((1 / 2 : ℂ) * ⟨(signed (Y.getD (2 * ℓ.val) []) : ℝ) / 2 ^ p,
        (signed (Y.getD (2 * ℓ.val + 1) []) : ℝ) / 2 ^ p⟩).im =
        1 / 2 * ((signed (Y.getD (2 * ℓ.val + 1) []) : ℝ) / 2 ^ p) by simp, hr]

include hs hw hyw hyl hyb hz hzl in
/-- A step with weights `-ρ(2^p d')` is `D̃'`. -/
theorem diag_vec {t : ℕ} (α : ℝ) (wtD : List (List Bool)) (hwt : ∀ x ∈ wtD, x.length = w)
    (hwtl : wtD.length = s * (2 * 0 + 1)) (hwtb : ∀ x ∈ wtD, |signed x| ≤ 2 ^ p)
    (hwD : ∀ k < s, signed (wtD.getD k []) = -rho0 (2 ^ p * NLogN.dPrime s t α (k : ZMod s))) :
    vec s p (oneStep wtD zeros s p w Y) = NLogN.diagDNum p s t α (vec s p Y) := by
  funext ℓ
  have hk := ZMod.val_lt ℓ
  set ar : ℤ → ℤ := fun j => signed (Y.getD (2 * (j % s).toNat) [])
  set ai : ℤ → ℤ := fun j => signed (Y.getD (2 * (j % s).toNat + 1) [])
  have hu : ∀ j : ℤ, vec s p Y (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩ := by
    intro j; simp only [vec, NeumannWords.val_intCast_toNat s j hs, ar, ai]
  have hℓ : ℓ = ((ℓ.val : ℤ) : ZMod s) := by simp
  have har : ar ℓ.val = signed (Y.getD (2 * ℓ.val) []) := by
    show signed (Y.getD (2 * (((ℓ.val : ℤ) % s).toNat)) []) = _
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hai : ai ℓ.val = signed (Y.getD (2 * ℓ.val + 1) []) := by
    show signed (Y.getD (2 * (((ℓ.val : ℤ) % s).toNat) + 1) []) = _
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hD : NLogN.diagDNum p s t α (vec s p Y) ℓ =
      NLogN.rhoC p (NLogN.rhoC p (NLogN.dPrime s t α ℓ : ℂ) * vec s p Y ((ℓ.val : ℤ) : ZMod s)) := by
    conv_rhs => rw [← hℓ]
    rfl
  rw [hD, OffDiagSum.round_term_parts p (vec s p Y) ar ai hu, har, hai]
  have e0 := oneStep_signed wtD zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 0 (by omega)
  have e1 := oneStep_signed wtD zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 1 (by omega)
  rw [add_zero, hwD _ hk, neg_mul, Int.neg_tdiv, neg_neg, ZMod.natCast_zmod_val] at e0
  rw [hwD _ hk, neg_mul, Int.neg_tdiv, neg_neg, ZMod.natCast_zmod_val] at e1
  apply Complex.ext
  · simp only [vec]; rw [e0]
  · simp only [vec]; rw [e1]

end Steps

section Final

open IntegerMultBounds.NLogN (resampJNumH resampB₀NumH sqrtWindow normExp hornerNeumannR_err_unit
  opNorm_offDiagCLM_le_unit offDiagNum_err_unit_sqrt room_of_le sqrtWindow_bound sqrtWindow_le norm_rdV_sub_le
  norm_rdV_le offDiagNum offDiagTermNum)

theorem vsel_mem (win : List (List Bool)) (s t : ℕ) [NeZero s] (hst : s < t) (hwin : win.length = 2 * t) :
    ∀ x ∈ vsel win s t, x ∈ win := by
  intro x hx
  simp only [vsel, List.mem_flatMap, List.mem_range, List.mem_cons, List.not_mem_nil, or_false] at hx
  obtain ⟨j, hj, rfl | rfl⟩ := hx
  all_goals
    have := NLogN.rowIndexNat_lt (s := s) (t := t) hst (j : ZMod s)
    exact NeumannWords.getD_mem' _ _ (by omega)

theorem words_bound (Y : List (List Bool)) (s p : ℕ) [NeZero s] (hyl : Y.length = 2 * s)
    (h : ‖vec s p Y‖ ≤ 1) : ∀ x ∈ Y, |signed x| ≤ 2 ^ p := by
  intro x hx
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hx
  have := NeumannWords.num_bound s p Y h i (by omega)
  rwa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi, Option.getD_some] at this

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- The words written by the `B̃₀` machine are the numerators of the clamp-free
`B̃₀` of the manuscript applied to the input vector. -/
theorem b0_value {α : ℝ} (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    {p w W : ℕ} (hp : 13 ≤ p) (hw : p + 3 ≤ w) (hwW : w ≤ W)
    (hW : ((2 * sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (win wtE wtH wtD zeros : List (List Bool))
    (hwin : win.length = 2 * t) (hwinw : ∀ x ∈ win, x.length = w) (hwinb : ∀ x ∈ win, |signed x| ≤ 2 ^ p)
    (hwv : ‖vec t p win‖ ≤ 1)
    (hwtH : ∀ x ∈ wtH, x.length = w) (hwtHl : wtH.length = s * (2 * 0 + 1))
    (hwH : ∀ x ∈ wtH, signed x = -2 ^ (p - 1))
    (hwt' : ∀ k j, k < s → j < 2 * sqrtWindow p + 1 →
      signed (wtE.getD (k * (2 * sqrtWindow p + 1) + j) []) =
        if -(sqrtWindow p : ℤ) + j = 0 then 0
        else rho0 (2 ^ p * Real.exp (normExp s t α (k : ZMod s).val (-(sqrtWindow p : ℤ) + j))))
    (hwtE : ∀ x ∈ wtE, x.length = w) (hwtEb : ∀ x ∈ wtE, |signed x| ≤ 2 ^ p)
    (hwtEl : wtE.length = s * (2 * sqrtWindow p + 1))
    (hwtD : ∀ x ∈ wtD, x.length = w) (hwtDl : wtD.length = s * (2 * 0 + 1))
    (hwtDb : ∀ x ∈ wtD, |signed x| ≤ 2 ^ p)
    (hwD : ∀ k < s, signed (wtD.getD k []) = -rho0 (2 ^ p * NLogN.dPrime s t α (k : ZMod s)))
    (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s) :
    vec s p (oneStep wtD zeros s p w
        (iter wtE (oneStep wtH zeros s p w (vsel win s t)) s (sqrtWindow p) p w W p)) =
      resampB₀NumH p (sqrtWindow p) s t α (vec t p win) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set v := NLogN.rowSelect s t (vec t p win) with hvdef
  have hsel : vec s p (vsel win s t) = v := sel_vec p hst win
  have hvw := B0Words.vsel_width s t hst win w hwin hwinw
  have hvl := B0Words.vsel_length s t win
  have hvb : ∀ x ∈ vsel win s t, |signed x| ≤ 2 ^ p := fun x hx => hwinb x (vsel_mem win s t hst hwin x hx)
  have hhalf : vec s p (oneStep wtH zeros s p w (vsel win s t)) = rdV p ((1 / 2 : ℂ) • v) := by
    rw [half_vec zeros (vsel win s t) p w hs hw hvw hvl hvb hz hzl wtH (by omega) hwtH hwtHl hwH, hsel]
  have hv : ‖v‖ ≤ 1 := (NLogN.norm_rowSelect_le _).trans hwv
  set V0 := oneStep wtH zeros s p w (vsel win s t)
  have hV0w := NeumannStep.nextWords_shape zeros (outWords wtH (ext s 0 (vsel win s t)) s s 0 p w w s) w
    (fun x hx => by rw [hz x hx]; simp)
  have hV0l : V0.length = 2 * s := by simp only [V0, oneStep, NeumannWords.nextWords_length, hzl]
  have hJ := NeumannWords.resampJNumH_eq_iter hst hα hθ hp wtE V0 hwt' hw hwW hW hwtE hwtEb hwtEl hV0l hV0w v hv hhalf
  -- the iterate stays in the unit disk
  have hhalfb : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 → 2 ^ p * ‖offDiagNum (sqrtWindow p) (offDiagTermNum p s t α) y -
      NLogN.offDiagCLM s t α y‖ ≤ 6 * (2 * (sqrtWindow p : ℝ)) + 6 :=
    fun y hy => offDiagNum_err_unit_sqrt hst hα hθ (sqrtWindow_bound p) y hy
  have hroom : 25 * (6 * (2 * (sqrtWindow p : ℝ)) + 6) ≤ 2 ^ p := room_of_le (sqrtWindow_le p (by omega)) hp
  have hv0b : ‖rdV p ((1 / 2 : ℂ) • v)‖ ≤ 1 / 2 := (norm_rdV_le p _).trans hhalfb
  have hball : ‖resampJNumH p (sqrtWindow p) s t α v‖ ≤ 1 :=
    (hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b p).1
  have hJb : ‖vec s p (iter wtE V0 s (sqrtWindow p) p w W p)‖ ≤ 1 := by
    rw [← hJ]; exact hball
  obtain ⟨hitl, hitw⟩ := NeumannStep.iter_shape wtE V0 s (sqrtWindow p) p w W hV0w p
  rw [hV0l] at hitl
  have hitb := words_bound _ s p hitl hJb
  have hD := diag_vec zeros (iter wtE V0 s (sqrtWindow p) p w W p) p w hs hw hitw hitl hitb hz hzl α wtD
    hwtD hwtDl hwtDb hwD
  rw [hD, ← hJ]
  rfl

end Final

section Tabled

open IntegerMultBounds.NLogN (resampJNumH resampB₀NumH sqrtWindow normExp hornerNeumannR_err_unit
  opNorm_offDiagCLM_le_unit room_of_le sqrtWindow_bound sqrtWindow_le norm_rdV_sub_le
  norm_rdV_le offDiagNum offDiagCLM hornerNeumannR)
open IntegerMultBounds.Resampling.TabledMaps (resampJNumW resampB₀NumW diagW offDiagW_err_sqrt tol_of_int)

variable {s t : ℕ} [NeZero s] [NeZero t]

/-- `J̃'` with an integer off-diagonal table equals the word iterates. -/
theorem resampJNumW_eq_iter {α : ℝ} (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    {p w W : ℕ} (hp : 13 ≤ p) (WE : ZMod s → ℤ → ℤ)
    (hWE : ∀ ℓ h, |(WE ℓ h : ℝ) - 2 ^ p * Real.exp (normExp s t α ℓ.val h)| ≤ 2)
    (wt v0 : List (List Bool))
    (hwt' : ∀ k j, k < s → j < 2 * sqrtWindow p + 1 →
      signed (wt.getD (k * (2 * sqrtWindow p + 1) + j) []) =
        if -(sqrtWindow p : ℤ) + j = 0 then 0 else WE (k : ZMod s) (-(sqrtWindow p : ℤ) + j))
    (hw : p + 3 ≤ w) (hwW : w ≤ W)
    (hW : ((2 * sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (hwt : ∀ x ∈ wt, x.length = w) (hwb : ∀ x ∈ wt, |signed x| ≤ 2 ^ p)
    (hwtl : wt.length = s * (2 * sqrtWindow p + 1))
    (hv0 : v0.length = 2 * s) (hv0w : ∀ x ∈ v0, x.length = w)
    (v : ZMod s → ℂ) (hv : ‖v‖ ≤ 1) (hv0v : vec s p v0 = rdV p ((1 / 2 : ℂ) • v)) :
    resampJNumW p (sqrtWindow p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) v =
      vec s p (iter wt v0 s (sqrtWindow p) p w W p) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  have hp' : (0 : ℝ) < 2 ^ p := by positivity
  set ef : ZMod s → ℤ → ℝ := fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p with hef
  have hhalf : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hv0b : ‖vec s p v0‖ ≤ 1 / 2 := by rw [hv0v]; exact (norm_rdV_le p _).trans hhalf
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 → 2 ^ p * ‖offDiagNum (sqrtWindow p) (OffDiagSum.offTermW p ef) y -
      offDiagCLM s t α y‖ ≤ 6 * (2 * (sqrtWindow p : ℝ)) + 6 :=
    fun y hy => offDiagW_err_sqrt hst hα hθ (sqrtWindow_bound p) ef (fun ℓ h => tol_of_int p _ _ (hWE ℓ h)) y hy
  have hroom : 25 * (6 * (2 * (sqrtWindow p : ℝ)) + 6) ≤ 2 ^ p := room_of_le (sqrtWindow_le p (by omega)) hp
  have hball : ∀ K, ‖hornerNeumannR (rdV p) (offDiagNum (sqrtWindow p) (OffDiagSum.offTermW p ef))
      (vec s p v0) K‖ ≤ 1 := fun K =>
    (hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b K).1
  have hwt'' : ∀ k j, k < s → j < 2 * sqrtWindow p + 1 →
      signed (wt.getD (k * (2 * sqrtWindow p + 1) + j) []) =
        if -(sqrtWindow p : ℤ) + j = 0 then 0 else rho0 (2 ^ p * ef (k : ZMod s) (-(sqrtWindow p : ℤ) + j)) := by
    intro k j hk hj
    rw [hwt' k j hk hj, hef]
    simp only
    rw [mul_div_cancel₀ _ hp'.ne', NeumannWords.rho0_int]
  have h := (NeumannWords.iter_spec wt v0 s (sqrtWindow p) p w W ef hwt'' hw hwW hW hwt hwb hwtl hv0 hv0w hs
    hball p).2.2
  unfold resampJNumW
  rw [← hv0v]
  exact h

/-- A window-radius-zero step with an integer table is `D̃'` with that table. -/
theorem diagW_vec (zeros Y : List (List Bool)) (p w : ℕ) (hs : 0 < s) (hw : p + 3 ≤ w)
    (hyw : ∀ x ∈ Y, x.length = w) (hyl : Y.length = 2 * s) (hyb : ∀ x ∈ Y, |signed x| ≤ 2 ^ p)
    (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s)
    (WD : ZMod s → ℤ) (wtD : List (List Bool)) (hwt : ∀ x ∈ wtD, x.length = w)
    (hwtl : wtD.length = s * (2 * 0 + 1)) (hwtb : ∀ x ∈ wtD, |signed x| ≤ 2 ^ p)
    (hwD : ∀ k < s, signed (wtD.getD k []) = -WD (k : ZMod s)) :
    vec s p (oneStep wtD zeros s p w Y) = diagW p (fun ℓ => (WD ℓ : ℝ) / 2 ^ p) (vec s p Y) := by
  have hp' : (0 : ℝ) < 2 ^ p := by positivity
  funext ℓ
  have hk := ZMod.val_lt ℓ
  set ar : ℤ → ℤ := fun j => signed (Y.getD (2 * (j % s).toNat) [])
  set ai : ℤ → ℤ := fun j => signed (Y.getD (2 * (j % s).toNat + 1) [])
  have hu : ∀ j : ℤ, vec s p Y (j : ZMod s) = ⟨(ar j : ℝ) / 2 ^ p, (ai j : ℝ) / 2 ^ p⟩ := by
    intro j; simp only [vec, NeumannWords.val_intCast_toNat s j hs, ar, ai]
  have hℓ : ℓ = ((ℓ.val : ℤ) : ZMod s) := by simp
  have har : ar ℓ.val = signed (Y.getD (2 * ℓ.val) []) := by
    show signed (Y.getD (2 * (((ℓ.val : ℤ) % s).toNat)) []) = _
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hai : ai ℓ.val = signed (Y.getD (2 * ℓ.val + 1) []) := by
    show signed (Y.getD (2 * (((ℓ.val : ℤ) % s).toNat) + 1) []) = _
    rw [Int.emod_eq_of_lt (by omega) (by omega), Int.toNat_natCast]
  have hD : diagW p (fun ℓ => (WD ℓ : ℝ) / 2 ^ p) (vec s p Y) ℓ =
      rhoC p (rhoC p (((WD ℓ : ℝ) / 2 ^ p : ℝ) : ℂ) * vec s p Y ((ℓ.val : ℤ) : ZMod s)) := by
    conv_rhs => rw [← hℓ]
    rfl
  rw [hD, OffDiagSum.round_term_parts p (vec s p Y) ar ai hu, har, hai, mul_div_cancel₀ _ hp'.ne',
    NeumannWords.rho0_int]
  have e0 := oneStep_signed wtD zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 0 (by omega)
  have e1 := oneStep_signed wtD zeros Y s p w hs hw hwt hwtl hwtb hyw hyl hyb hz hzl ℓ.val hk 1 (by omega)
  rw [add_zero, hwD _ hk, neg_mul, Int.neg_tdiv, neg_neg, ZMod.natCast_zmod_val] at e0
  rw [hwD _ hk, neg_mul, Int.neg_tdiv, neg_neg, ZMod.natCast_zmod_val] at e1
  apply Complex.ext
  · simp only [vec]; rw [e0]
  · simp only [vec]; rw [e1]

/-- The words written by the `B̃₀` machine from integer weight tables are the
numerators of `B̃₀` with those tables. -/
theorem b0_value_W {α : ℝ} (hst : s < t) (hα : 0 < α) (hθ : 1 ≤ α ^ 2 * ((t : ℝ) / s - 1))
    {p w W : ℕ} (hp : 13 ≤ p) (hw : p + 3 ≤ w) (hwW : w ≤ W)
    (hW : ((2 * sqrtWindow p + 1 : ℕ) : ℤ) * 2 ^ p < 2 ^ (W - 1))
    (WE : ZMod s → ℤ → ℤ) (WD : ZMod s → ℤ)
    (hWE : ∀ ℓ h, |(WE ℓ h : ℝ) - 2 ^ p * Real.exp (normExp s t α ℓ.val h)| ≤ 2)
    (win wtE wtH wtD zeros : List (List Bool))
    (hwin : win.length = 2 * t) (hwinw : ∀ x ∈ win, x.length = w) (hwinb : ∀ x ∈ win, |signed x| ≤ 2 ^ p)
    (hwv : ‖vec t p win‖ ≤ 1)
    (hwtH : ∀ x ∈ wtH, x.length = w) (hwtHl : wtH.length = s * (2 * 0 + 1))
    (hwH : ∀ x ∈ wtH, signed x = -2 ^ (p - 1))
    (hwt' : ∀ k j, k < s → j < 2 * sqrtWindow p + 1 →
      signed (wtE.getD (k * (2 * sqrtWindow p + 1) + j) []) =
        if -(sqrtWindow p : ℤ) + j = 0 then 0 else WE (k : ZMod s) (-(sqrtWindow p : ℤ) + j))
    (hwtE : ∀ x ∈ wtE, x.length = w) (hwtEb : ∀ x ∈ wtE, |signed x| ≤ 2 ^ p)
    (hwtEl : wtE.length = s * (2 * sqrtWindow p + 1))
    (hwtD : ∀ x ∈ wtD, x.length = w) (hwtDl : wtD.length = s * (2 * 0 + 1))
    (hwtDb : ∀ x ∈ wtD, |signed x| ≤ 2 ^ p)
    (hwD : ∀ k < s, signed (wtD.getD k []) = -WD (k : ZMod s))
    (hz : ∀ x ∈ zeros, x = List.replicate w false) (hzl : zeros.length = 2 * s) :
    vec s p (oneStep wtD zeros s p w
        (iter wtE (oneStep wtH zeros s p w (vsel win s t)) s (sqrtWindow p) p w W p)) =
      resampB₀NumW p (sqrtWindow p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) (fun ℓ => (WD ℓ : ℝ) / 2 ^ p)
        (vec t p win) := by
  have hs : 0 < s := Nat.pos_of_ne_zero (NeZero.ne s)
  set v := NLogN.rowSelect s t (vec t p win) with hvdef
  have hsel : vec s p (vsel win s t) = v := sel_vec p hst win
  have hvw := B0Words.vsel_width s t hst win w hwin hwinw
  have hvl := B0Words.vsel_length s t win
  have hvb : ∀ x ∈ vsel win s t, |signed x| ≤ 2 ^ p := fun x hx => hwinb x (vsel_mem win s t hst hwin x hx)
  have hhalf : vec s p (oneStep wtH zeros s p w (vsel win s t)) = rdV p ((1 / 2 : ℂ) • v) := by
    rw [half_vec zeros (vsel win s t) p w hs hw hvw hvl hvb hz hzl wtH (by omega) hwtH hwtHl hwH, hsel]
  have hv : ‖v‖ ≤ 1 := (NLogN.norm_rowSelect_le _).trans hwv
  set V0 := oneStep wtH zeros s p w (vsel win s t)
  have hV0w := NeumannStep.nextWords_shape zeros (outWords wtH (ext s 0 (vsel win s t)) s s 0 p w w s) w
    (fun x hx => by rw [hz x hx]; simp)
  have hV0l : V0.length = 2 * s := by simp only [V0, oneStep, NeumannWords.nextWords_length, hzl]
  have hJ := resampJNumW_eq_iter hst hα hθ hp WE hWE wtE V0 hwt' hw hwW hW hwtE hwtEb hwtEl hV0l hV0w v hv hhalf
  have hhalfb : ‖(1 / 2 : ℂ) • v‖ ≤ 1 / 2 := by
    rw [norm_smul, norm_div, norm_one, RCLike.norm_two]; linarith
  have hE := opNorm_offDiagCLM_le_unit hst hα hθ
  have hE' : ∀ y : ZMod s → ℂ, ‖y‖ ≤ 1 → 2 ^ p * ‖offDiagNum (sqrtWindow p)
      (OffDiagSum.offTermW p fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) y - offDiagCLM s t α y‖ ≤
        6 * (2 * (sqrtWindow p : ℝ)) + 6 :=
    fun y hy => offDiagW_err_sqrt hst hα hθ (sqrtWindow_bound p) _ (fun ℓ h => tol_of_int p _ _ (hWE ℓ h)) y hy
  have hroom : 25 * (6 * (2 * (sqrtWindow p : ℝ)) + 6) ≤ 2 ^ p := room_of_le (sqrtWindow_le p (by omega)) hp
  have hv0b : ‖rdV p ((1 / 2 : ℂ) • v)‖ ≤ 1 / 2 := (norm_rdV_le p _).trans hhalfb
  have hball : ‖resampJNumW p (sqrtWindow p) (fun ℓ h => (WE ℓ h : ℝ) / 2 ^ p) v‖ ≤ 1 :=
    (hornerNeumannR_err_unit hE hE' hroom (norm_rdV_sub_le p) (norm_rdV_le p) hv0b p).1
  have hJb : ‖vec s p (iter wtE V0 s (sqrtWindow p) p w W p)‖ ≤ 1 := by rw [← hJ]; exact hball
  obtain ⟨hitl, hitw⟩ := NeumannStep.iter_shape wtE V0 s (sqrtWindow p) p w W hV0w p
  rw [hV0l] at hitl
  have hitb := words_bound _ s p hitl hJb
  have hD := diagW_vec zeros (iter wtE V0 s (sqrtWindow p) p w W p) p w hs hw hitw hitl hitb hz hzl WD wtD
    hwtD hwtDl hwtDb hwD
  rw [hD, ← hJ]
  rfl

end Tabled

end IntegerMultBounds.Resampling.B0Value
