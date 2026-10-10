import IntegerMultBounds.Schoenhage.RingProduct

/-! What the ring product's output words mean. Each packed residue is the
evaluation of the signed coefficients at `2^W` modulo `2^N + 1`, so the
combined residues are the evaluations of the real and imaginary parts of the
negacyclic product; when those parts are below `2^(W-1)` in absolute value,
the unpacked words are exactly the parts truncated toward zero by `s` bits,
as `w`-bit words (`outs_eq`). -/

namespace IntegerMultBounds.Schoenhage

/-- The signed real (`odd = false`) or imaginary coefficients. -/
def coeffs (odd : Bool) (ps : List (List Bool × List Bool)) : List ℤ := ps.map fun p => sv (pick odd p)

/-- The exact real and imaginary parts of the normalized product, before truncation. -/
def reCoeffs (r : ℕ) (fs gs : List (List Bool × List Bool)) : List ℤ :=
  List.zipWith (· - ·) (ncMul r (coeffs false fs) (coeffs false gs)) (ncMul r (coeffs true fs) (coeffs true gs))

def imCoeffs (r : ℕ) (fs gs : List (List Bool × List Bool)) : List ℤ :=
  List.zipWith (· + ·) (ncMul r (coeffs false fs) (coeffs true gs)) (ncMul r (coeffs true fs) (coeffs false gs))

/-- The output pairs: each part truncated toward zero by `s` bits, as a `w`-bit word. -/
def ringOut (r s w : ℕ) (fs gs : List (List Bool × List Bool)) : List (List Bool × List Bool) :=
  List.zip ((reCoeffs r fs gs).map fun x => tw w (trunc0 s x)) ((imCoeffs r fs gs).map fun x => tw w (trunc0 s x))

theorem length_coeffs (odd : Bool) (ps : List (List Bool × List Bool)) : (coeffs odd ps).length = ps.length := by
  simp [coeffs]

theorem Fm_cast {Wd r N : ℕ} (hN : N = Wd * r) : ((Fm N : ℕ) : ℤ) = (2 ^ Wd : ℤ) ^ r + 1 := by
  subst hN; simp [Fm, pow_mul]

theorem resid_modEq {Wd r w N : ℕ} (odd : Bool) (ps : List (List Bool × List Bool)) (hl : ps.length = r)
    (hw : 1 ≤ w) (hwf : ∀ p ∈ ps, p.1.length = w ∧ p.2.length = w)
    (hO : wsum Wd (List.replicate r (2 ^ (w - 1))) < 2 ^ N + 1) :
    (resid Wd r w N odd ps : ℤ) ≡ ev (2 ^ Wd) (coeffs odd ps) [ZMOD (Fm N : ℤ)] := by
  have hd : (digits odd ps).length = r := by simp [digits, hl]
  have e := encode_res Wd N (2 ^ (w - 1)) (digits odd ps) (by rw [hd]; exact hO)
  rw [hd] at e
  have hm : ((digits odd ps).map fun d : ℕ => (d : ℤ) - ((2 ^ (w - 1) : ℕ) : ℤ)) = coeffs odd ps := by
    simp only [digits, coeffs, List.map_map]
    apply List.map_congr_left
    intro p hp
    have := hwf p hp
    have hne : pick odd p ≠ [] := by
      intro q; cases odd <;> simp [pick] at q <;> simp [q] at this <;> omega
    have hlen : (pick odd p).length = w := by cases odd <;> simp [pick, this.1, this.2]
    simp only [Function.comp_apply]
    rw [bval_flipLast hne, hlen]; push_cast; ring
  rw [hm] at e
  exact e

theorem mul_modEq {Wd r N : ℕ} (hN : N = Wd * r) {a b : ℕ} {u v : List ℤ} (hu : u.length = r) (hv : v.length = r)
    (ha : (a : ℤ) ≡ ev (2 ^ Wd) u [ZMOD (Fm N : ℤ)]) (hb : (b : ℤ) ≡ ev (2 ^ Wd) v [ZMOD (Fm N : ℤ)]) :
    ((a * b % Fm N : ℕ) : ℤ) ≡ ev (2 ^ Wd) (ncMul r u v) [ZMOD (Fm N : ℤ)] := by
  rw [Int.natCast_mod]
  refine (Int.mod_modEq _ _).trans ?_
  push_cast
  refine (ha.mul hb).trans ?_
  have := ev_ncMul (2 ^ Wd) r u v hu hv
  rw [← Fm_cast hN] at this
  exact this

theorem sub_modEq {N x y : ℕ} (hy : y < Fm N) {p q : ℤ} (hx : (x : ℤ) ≡ p [ZMOD (Fm N : ℤ)])
    (hq : (y : ℤ) ≡ q [ZMOD (Fm N : ℤ)]) : (((x + Fm N - y) % Fm N : ℕ) : ℤ) ≡ p - q [ZMOD (Fm N : ℤ)] := by
  rw [Int.natCast_mod]
  refine (Int.mod_modEq _ _).trans ?_
  rw [Nat.cast_sub (by omega)]
  push_cast
  have h0 : ((Fm N : ℕ) : ℤ) ≡ 0 [ZMOD (Fm N : ℤ)] := by simp [Int.ModEq]
  simpa using (hx.add h0).sub hq

theorem add_modEq {N x y : ℕ} {p q : ℤ} (hx : (x : ℤ) ≡ p [ZMOD (Fm N : ℤ)])
    (hq : (y : ℤ) ≡ q [ZMOD (Fm N : ℤ)]) : (((x + y) % Fm N : ℕ) : ℤ) ≡ p + q [ZMOD (Fm N : ℤ)] := by
  rw [Int.natCast_mod]
  refine (Int.mod_modEq _ _).trans ?_
  push_cast
  exact hx.add hq

theorem zipWith_ncMul (f : ℤ → ℤ → ℤ) (r : ℕ) (u v u' v' : List ℤ) :
    List.zipWith f (ncMul r u v) (ncMul r u' v') = (List.range r).map fun k => f (ncCoef r u v k) (ncCoef r u' v' k) := by
  simp only [ncMul, List.zipWith_map, List.zipWith_self]

/-- Every part is below half the digit range. -/
theorem part_bound {r Wd : ℕ} {Bd : ℤ} (hBd : 2 * r * (Bd * Bd) < 2 ^ (Wd - 1)) {a c : ℤ}
    (ha : |a| ≤ r * (Bd * Bd)) (hc : |c| ≤ r * (Bd * Bd)) (f : ℤ) (hf : f = a - c ∨ f = a + c) :
    -2 ^ (Wd - 1) ≤ f ∧ f < 2 ^ (Wd - 1) := by
  have h1 := abs_le.mp ha; have h3 := abs_le.mp hc
  rcases hf with rfl | rfl <;> constructor <;> nlinarith

theorem outs_parts {Wd r s w N : ℕ} (hW : 1 ≤ Wd) (hr : 1 ≤ r) (hN : N = Wd * r) (hw : 1 ≤ w)
    (hws : w + s ≤ Wd + 1) {h : List ℤ} (hl : h.length = r) (hh : ∀ x ∈ h, -2 ^ (Wd - 1) ≤ x ∧ x < 2 ^ (Wd - 1))
    {V : ℕ} (hV : (V : ℤ) ≡ ev (2 ^ Wd) h [ZMOD (Fm N : ℤ)]) :
    outs Wd r s w N V = h.map fun x => tw w (trunc0 s x) := by
  unfold outs
  rw [decode_pieces hW hr hN hl hh hV, List.map_map]
  apply List.map_congr_left
  intro x hx
  have hlt := digits_lt hW hh _ (List.mem_map_of_mem hx)
  simp only [Function.comp_apply]
  rw [outWord_eq hW hlt hw hws]
  congr 2
  have := hh x hx
  rw [Int.toNat_of_nonneg (by linarith)]; ring

theorem outs_eq {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} {τ : Fin 𝕌 → WTape}
    (h : RingSetup Wd r w s N fs gs τ) (Bd : ℤ) (hB0 : 0 ≤ Bd)
    (hf : ∀ odd, ∀ x ∈ coeffs odd fs, |x| ≤ Bd) (hg : ∀ odd, ∀ x ∈ coeffs odd gs, |x| ≤ Bd)
    (hBd : 2 * r * (Bd * Bd) < 2 ^ (Wd - 1)) :
    List.zip (outs Wd r s w N (reRes Wd r w N fs gs)) (outs Wd r s w N (imRes Wd r w N fs gs)) =
      ringOut r s w fs gs := by
  have hW : 1 ≤ Wd := by have := h.hWd; omega
  have hO : wsum Wd (List.replicate r (2 ^ (w - 1))) < 2 ^ N + 1 := by have := h.Oin_lt; omega
  have rf := fun odd => resid_modEq (Wd := Wd) (N := N) odd fs h.lf h.hw h.wf hO
  have rg := fun odd => resid_modEq (Wd := Wd) (N := N) odd gs h.lg h.hw h.wg hO
  have lf := fun odd => (length_coeffs odd fs).trans h.lf
  have lg := fun odd => (length_coeffs odd gs).trans h.lg
  have hRe : (reRes Wd r w N fs gs : ℤ) ≡ ev (2 ^ Wd) (reCoeffs r fs gs) [ZMOD (Fm N : ℤ)] := by
    unfold reRes reCoeffs
    rw [ev_sub _ _ _ (by simp)]
    exact sub_modEq (Nat.mod_lt _ (by simp [Fm])) (mul_modEq h.hN (lf false) (lg false) (rf false) (rg false))
      (mul_modEq h.hN (lf true) (lg true) (rf true) (rg true))
  have hIm : (imRes Wd r w N fs gs : ℤ) ≡ ev (2 ^ Wd) (imCoeffs r fs gs) [ZMOD (Fm N : ℤ)] := by
    unfold imRes imCoeffs
    rw [ev_add _ _ _ (by simp)]
    exact add_modEq (mul_modEq h.hN (lf false) (lg true) (rf false) (rg true))
      (mul_modEq h.hN (lf true) (lg false) (rf true) (rg false))
  have nb := fun (o₁ o₂ : Bool) (k : ℕ) =>
    ncCoef_abs r (coeffs o₁ fs) (coeffs o₂ gs) Bd Bd (hf o₁) (hg o₂) hB0 hB0 k
  have hReB : ∀ x ∈ reCoeffs r fs gs, -2 ^ (Wd - 1) ≤ x ∧ x < 2 ^ (Wd - 1) := by
    intro x hx
    unfold reCoeffs at hx
    rw [zipWith_ncMul, List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact part_bound hBd (nb false false k) (nb true true k) _ (Or.inl rfl)
  have hImB : ∀ x ∈ imCoeffs r fs gs, -2 ^ (Wd - 1) ≤ x ∧ x < 2 ^ (Wd - 1) := by
    intro x hx
    unfold imCoeffs at hx
    rw [zipWith_ncMul, List.mem_map] at hx
    obtain ⟨k, -, rfl⟩ := hx
    exact part_bound hBd (nb false true k) (nb true false k) _ (Or.inr rfl)
  unfold ringOut
  rw [outs_parts hW h.hr h.hN h.hw h.hws (by simp [reCoeffs]) hReB hRe,
    outs_parts hW h.hr h.hN h.hw h.hws (by simp [imCoeffs]) hImB hIm]

end IntegerMultBounds.Schoenhage
