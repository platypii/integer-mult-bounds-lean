module

public import IntegerMultBounds.MathlibTM2.Cost.PolynomialVolume

import IntegerMultBounds.MathlibTM2.Cost.MatchLayout
public import IntegerMultBounds.MathlibTM2.Fast.MainEmbed
public import IntegerMultBounds.MathlibTM2.Fast.SynLaySpec
public import IntegerMultBounds.MathlibTM2.Fast.DistWidth
import IntegerMultBounds.MathlibTM2.Cost.MatchBase
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-!
# Cost matching: the layout programs of the synthetic transforms

The layout programs `slyFwd`, `slyOpp` (`Fast/SynLayFwd.lean`, `Fast/SynLayOpp.lean`) cost
`slyFwdCost`, `slyOppCost` at the pipeline parameters: the axes `es = List.ofFn (cvAx (t n))`
(`|es| = d - 1`, `Σ es = log₂ T - ℓ`), records of `B = r · dsW n` symbols (`r = 2^ℓ`
coefficients of `dsW n ≤ 3p` symbols), the writer word width `W = slyW N B ℓ (d - 1) ≤ 26 b² r`,
any axis word `E` and wires `v₀`. `ml_lay_cost_le_gen`: their sum is at most a constant times
`totConv n`, eventually; `ml_lay_cost_le`: the same for the cost terms `mlCL dsW v₀`,
`mlCL' dsW v₀` of the layout bundle (word width `mlW dsW n`, axis word `mlE n`).

* **The stream volume** is `V = 2^N B = T · dsW n ≤ 3 T p` symbols; the bank registers of the
  canonical file `slyR₂` are empty, so the bank of an exchange holds the five headers only
  (`mt_lay_bank_le`, `ml_bankX_le`: at most `swapT 6 (3V + 1)` symbols).
* **The layout machine** (`ml_stage_le`, for any exchange list of the right length and any file
  family with that bank bound, so for both directions): at most `d K` single-bit moves of
  `O(V)` steps and `d q` exchanges of `O(V K^τ)` steps, `q K ≤ ℓ`, `d ℓ ≤ p`: a constant times
  `T p (d K + p K^{τ-1})`, the first two parts of `totConv`.
* **The writer** (`ml_writer_le`): a polynomial of degree `6` in arguments at most `cZ b² r`, so
  at most `555210 cZ^6 b^12 r^6 ≤ T p` eventually (`ml_poly_r_le_T`: `A b^k r^m ≤ T` eventually,
  from `d → ∞` and `b ≤ 4 (log₂ T - ℓ)`).
* **Setup, cleanup, reversal** (`ml_aux_le`): `6 · 2^N + poly(b) · r ≤ 7 T p`.
-/

@[expose] public section


namespace IntegerMultBounds.MathlibTM2.Cost

open IntegerMultBounds.MathlibTM2.Mult.Sizes Filter IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast IntegerMultBounds.MathlibTM2.Fast.TableVM IntegerMultBounds.MathlibTM2.Node
  IntegerMultBounds.MathlibTM2.LayerMachine IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Fast.ConvSt
  IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds.Networks.Shared50ModularControl (prime)

/-! ### Growth: `A b^k r^m ≤ T` -/

/-- Every `x ≤ A b^k r^m` is eventually at most `T p`. -/
theorem ml_small_le (A k m : ℕ) :
    ∀ᶠ n in atTop, ∀ x : ℕ, x ≤ A * b n ^ k * r n ^ m → (x : ℝ) ≤ (T n : ℝ) * p n := by
  filter_upwards [ml_poly_r_le_T A k m, eventually_big] with n h hb x hx
  have h1 : (x : ℝ) ≤ T n := by exact_mod_cast hx.trans h
  have h2 : (T n : ℝ) ≤ T n * p n := by
    have := mt_one_le_p hb
    have := mt_one_le_T n
    nlinarith
  linarith

/-! ### The move counts -/

/-- The counts of the layout at `ℓ n`, `K n`: at most `|es| (b + 1)` single-bit moves and
`|es| q` exchanges, with `b + 1 ≤ K`, `q K ≤ ℓ`, `q ≤ ℓ`. -/
theorem ml_counts {n : ℕ} {es : List ℕ} (H : LayHyp es (ℓ n) (K n)) (hK1 : 1 ≤ K n) (B : ℕ) :
    (layBits es (ℓ n) (K n)).length ≤ es.length * (layB (ℓ n) (K n) + 1) ∧
      (layXcs es (ℓ n) (K n) B).length ≤ es.length * layQ (ℓ n) (K n) ∧
      layB (ℓ n) (K n) + 1 ≤ K n ∧ layQ (ℓ n) (K n) * K n ≤ ℓ n ∧ layQ (ℓ n) (K n) ≤ ℓ n := by
  have hbK : layB (ℓ n) (K n) + 1 ≤ K n := H.b_lt
  have hq : layQ (ℓ n) (K n) * K n ≤ ℓ n := by
    unfold layQ
    exact (Nat.div_mul_le_self _ _).trans (Nat.sub_le _ _)
  have hqℓ : layQ (ℓ n) (K n) ≤ ℓ n := by
    have : layQ (ℓ n) (K n) ≤ layQ (ℓ n) (K n) * K n := Nat.le_mul_of_pos_right _ hK1
    omega
  obtain ⟨c1, c2⟩ := layMoves_counts (es := es) (ℓ := ℓ n) (K := K n)
  rw [layPreMoves, layPreMovesK, List.length_map, List.length_range] at c1
  refine ⟨?_, ?_, hbK, hq, hqℓ⟩
  · rw [length_layBits]; exact c1
  · rw [length_layXcs]; omega

/-! ### The writer -/

/-- **The writer at the pipeline.** With `B ≤ cw b² r`, `W ≤ cW b² r`, every argument is at
most `Z = (cW + cw + 2) b² r`, and `555210 Z^6 ≤ T p` eventually. -/
theorem ml_writer_le (cw cW : ℕ) :
    ∀ᶠ n in atTop, ∀ (es : List ℕ) (B W : ℕ), LayHyp es (ℓ n) (K n) → es.length ≤ d n →
      es.sum ≤ logT n → B ≤ cw * (b n ^ 2 * r n) → W ≤ cW * (b n ^ 2 * r n) →
      (ldgWriterCost W es.sum (ℓ n) (K n) es.length B (layB (ℓ n) (K n))
        (layBits es (ℓ n) (K n)).length (layXcs es (ℓ n) (K n) B).length
        (ldxAtoms es.sum es.length (layQ (ℓ n) (K n))) : ℝ) ≤ (T n : ℝ) * p n := by
  obtain ⟨cZ, hcZ⟩ : ∃ cZ, cZ = cW + cw + 2 := ⟨_, rfl⟩
  filter_upwards [eventually_big, gr_one_le_K, ml_small_le (555210 * cZ ^ 6) 12 6] with n h hK1
    hsmall
  intro es B W H hD hN hB hW
  have hb16 := h.sixteen_le_b
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  have hdb : d n ≤ b n := mt_d_le_b n
  have hℓb : ℓ n ≤ b n := mt_ℓ_le_b h
  have hKb : K n ≤ b n := mt_K_le_b n
  obtain ⟨hlen1, hlenX, hbK, hq, hqℓ⟩ := ml_counts H hK1 B
  apply hsmall
  obtain ⟨Q, hQ⟩ : ∃ Q, Q = b n ^ 2 * r n := ⟨_, rfl⟩
  rw [← hQ] at hB hW
  obtain ⟨Z, hZ⟩ : ∃ Z, Z = cZ * Q := ⟨_, rfl⟩
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hb2 : b n ≤ b n ^ 2 := Nat.le_self_pow two_ne_zero _
  have hbQ : b n ≤ Q := by rw [hQ]; exact hb2.trans (Nat.le_mul_of_pos_right _ hr1)
  have hbbQ : b n * b n ≤ Q := by rw [hQ, ← sq]; exact Nat.le_mul_of_pos_right _ hr1
  have hZe : Z = cW * Q + cw * Q + 2 * Q := by rw [hZ, hcZ]; ring
  have hQZ : Q ≤ Z := by rw [hZe]; omega
  have hbZ : b n ≤ Z := hbQ.trans hQZ
  have hbbZ : b n * b n ≤ Z := hbbQ.trans hQZ
  have hBZ : B ≤ Z := by rw [hZe]; omega
  have hWZ : W ≤ Z := by rw [hZe]; omega
  have hD' : es.length ≤ b n := hD.trans hdb
  have h1Z : (layBits es (ℓ n) (K n)).length ≤ Z := by
    refine hlen1.trans (le_trans ?_ hbbZ)
    exact Nat.mul_le_mul hD' (hbK.trans hKb)
  have hXZ : (layXcs es (ℓ n) (K n) B).length ≤ Z := by
    refine hlenX.trans (le_trans ?_ hbbZ)
    exact Nat.mul_le_mul hD' (hqℓ.trans hℓb)
  have hZ1 : 1 ≤ Z := by omega
  have hm := mt_lay_writer_mono (W' := Z) (N' := Z) (ℓ' := Z) (K' := Z) (D' := Z) (B' := Z)
    (b' := Z) (len1' := Z) (lenX' := Z) (KX' := ldxAtoms Z Z Z) hWZ (hNb.trans hbZ)
    (hℓb.trans hbZ) (hKb.trans hbZ) (hD'.trans hbZ) hBZ
    (show layB (ℓ n) (K n) ≤ Z by omega) h1Z hXZ
    (mt_lay_ldxAtoms_mono (hNb.trans hbZ) (hD'.trans hbZ) ((hqℓ.trans hℓb).trans hbZ))
  have hp := mt_lay_writer_poly hZ1
  have e : 555210 * Z ^ 6 = 555210 * cZ ^ 6 * b n ^ 12 * r n ^ 6 := by rw [hZ, hQ]; ring
  calc _ ≤ 555210 * Z ^ 6 := hm.trans hp
    _ = _ := e

/-! ### The bank of an exchange, the loops -/

/-- The bank registers of `ldlWX … (j + 1)` hold the five headers of exchange `j` (at most `Hm`
bits each, plus the separator) or the contents of the base file `R₁`. -/
theorem ml_bankX_le {T t₀ A : ℕ} {rg : LayReg t₀ → Fin T} {lr : LdlReg → Fin T}
    (hl : LdlRegs rg lr) {hd : Fin 5 → Fin t₀} (hi : Function.Injective hd)
    (R₁ : Fin T → List (Fin (A + 4))) (w : ℕ) (xs : List LayXcD) (j Hm : ℕ)
    (hH : ∀ k, ((xs.getD j default).hs k).length ≤ Hm) :
    ∑ i, (ldlWX rg lr hd A w R₁ xs (j + 1) (rg (.sw i))).length ≤
      ∑ i, (R₁ (rg (.sw i))).length + swapT t₀ * (Hm + 1) := by
  have hpt : ∀ i, (ldlWX rg lr hd A w R₁ xs (j + 1) (rg (.sw i))).length ≤
      (R₁ (rg (.sw i))).length + (Hm + 1) := by
    intro i
    simp only [ldlWX]
    rw [Function.update_of_ne (hl.disj _ _), ldlSetH_apply hl.rg_inj hi]
    split_ifs with hy
    · simp only [List.length_cons, List.length_map]
      have := hH hy.choose
      omega
    · omega
  calc ∑ i, (ldlWX rg lr hd A w R₁ xs (j + 1) (rg (.sw i))).length ≤
        ∑ i, ((R₁ (rg (.sw i))).length + (Hm + 1)) := Finset.sum_le_sum fun i _ => hpt i
    _ = ∑ i, (R₁ (rg (.sw i))).length + swapT t₀ * (Hm + 1) := by
        rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
          smul_eq_mul]

/-- The exchange loop on any list `xs`, with exchanges of at most `X` steps. -/
theorem ml_xcLoop_le {Ka : ℕ} (Tm t₀ n K B : ℕ) (rg : LayReg t₀ → Fin Tm)
    (Wf : ℕ → Fin Tm → List (Fin (prime + Ka + 4))) (cX X : ℕ) (xs : List LayXcD)
    (hXs : ∀ j < xs.length, layXcStep Tm t₀ n K B rg (Wf (j + 1)) (xs.getD j default) ≤ X) :
    layXcLoopCost Tm t₀ n K B rg Wf (fun _ => cX) xs ≤ xs.length * (cX + X + 5) + 4 := by
  unfold layXcLoopCost
  exact lay_loop_sum_le (fun j => cX + layXcStep Tm t₀ n K B rg (Wf (j + 1)) (xs.getD j default))
    (cX + X) xs.length (fun j hj => by have := hXs j hj; omega)

/-- The bit loop of `nb` moves. -/
theorem ml_bitLoop_le (n B cM nb : ℕ) :
    layBitCost n B (fun _ => cM) nb ≤ nb * (cM + layMvCost n B + 5) + 4 := by
  unfold layBitCost
  exact lay_loop_sum_le (fun _ => cM + layMvCost n B) (cM + layMvCost n B) nb
    (fun _ _ => le_rfl)

/-! ### Real arithmetic of the bound -/

/-- One exchange with its loader against `T p K^τ`: `V ≤ cv T p` stream symbols, a bank of at
most `sw (3V + 1)` symbols. -/
theorem ml_xr_le {Tr Pr Kτ N B V cv sw Tm s X : ℝ} (hTr : 1 ≤ Tr) (hPr : 1 ≤ Pr)
    (hK : 1 ≤ Kτ) (hN : N ≤ Pr) (hB : B ≤ V) (hV : V ≤ cv * (Tr * Pr)) (hsw : 0 ≤ sw)
    (hTm : 0 ≤ Tm) (hcv : 0 ≤ cv) (hs : 0 ≤ s)
    (hX : X ≤ 3 * s * (Tm + 12 * sw + 5) * V * Kτ +
      (6 * (sw * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * sw + 23) + 1) :
    60 * (N + B + 2) + 80 + X ≤
      (3 * s * (Tm + 12 * sw + 5) * cv + 94 * cv + 18 * sw * cv + 2 * Tm + 12 * sw + 284) *
        (Tr * Pr * Kτ) := by
  have hTP : 1 ≤ Tr * Pr := by nlinarith
  have hY1 : Tr * Pr ≤ Tr * Pr * Kτ := by nlinarith
  have hY : 1 ≤ Tr * Pr * Kτ := hTP.trans hY1
  have hN' : N ≤ Tr * Pr * Kτ := by nlinarith
  have hV' : V ≤ cv * (Tr * Pr * Kτ) := by
    have := mul_le_mul_of_nonneg_left hY1 hcv
    linarith
  have hB' : B ≤ cv * (Tr * Pr * Kτ) := hB.trans hV'
  have hVK : V * Kτ ≤ cv * (Tr * Pr * Kτ) := by
    have := mul_le_mul_of_nonneg_right hV (by linarith : (0 : ℝ) ≤ Kτ)
    linarith
  have hswV : sw * V ≤ sw * (cv * (Tr * Pr * Kτ)) := mul_le_mul_of_nonneg_left hV' hsw
  have hTm' : Tm ≤ Tm * (Tr * Pr * Kτ) := by nlinarith
  have hsw' : sw ≤ sw * (Tr * Pr * Kτ) := by nlinarith
  have hS : 0 ≤ 3 * s * (Tm + 12 * sw + 5) := by positivity
  have h3 : 3 * s * (Tm + 12 * sw + 5) * V * Kτ ≤
      3 * s * (Tm + 12 * sw + 5) * (cv * (Tr * Pr * Kτ)) := by
    have := mul_le_mul_of_nonneg_left hVK hS
    linarith
  linarith

/-- The constant of one exchange against `T p K^τ`. -/
noncomputable def mlC2 (Tm t₀ cv : ℕ) : ℝ :=
  3 * swapConst * ((Tm : ℝ) + 12 * swapT t₀ + 5) * cv + 94 * cv + 18 * swapT t₀ * cv + 2 * Tm +
    12 * swapT t₀ + 284

theorem ml_C2_nonneg (Tm t₀ cv : ℕ) : 0 ≤ mlC2 Tm t₀ cv := by
  have := mt_swapConst_nonneg
  unfold mlC2
  positivity

/-! ### The layout machine -/

/-- **The layout machine against `T p (d K + p K^{τ-1})`.** At `ℓ = ℓ n`, `K = K n`, axes of
`|es| ≤ d` and `Σ es ≤ log₂ T`, records of `B ≥ 1` symbols with `2^N B ≤ cv T p`, on any list
`xs` of at most `|es| q` well-formed exchanges, with the register files `Wf` whose banks hold at
most `swapT t₀ (3 · 2^N B + 1)` symbols: the bit loop and the exchange loop cost at most
`(18 cv + 130 + mlC2 Tm t₀ cv) · T p (d K + p K^{τ-1})`. -/
theorem ml_stage_le (Tm t₀ Ka cv : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ᶠ n in atTop, ∀ (es : List ℕ) (B : ℕ) (rg : LayReg t₀ → Fin Tm)
      (xs : List LayXcD) (Wf : ℕ → Fin Tm → List (Fin (prime + Ka + 4))),
      LayHyp es (ℓ n) (K n) → es.length ≤ d n → es.sum ≤ logT n → 1 ≤ B →
      2 ^ es.sum * B ≤ cv * (T n * p n) →
      (∀ x ∈ xs, x.OK es.sum (K n) B) → xs.length ≤ es.length * layQ (ℓ n) (K n) →
      (∀ j < xs.length, ∑ i, (Wf (j + 1) (rg (.sw i))).length ≤
        swapT t₀ * (3 * (2 ^ es.sum * B) + 1)) →
      ((layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es (ℓ n) (K n)).length +
        layXcLoopCost Tm t₀ es.sum (K n) B rg Wf (fun _ => 60 * (es.sum + B + 2) + 75) xs :
          ℕ) : ℝ) ≤
        C * ((T n : ℝ) * p n * ((d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) := by
  obtain ⟨C2, hC2def⟩ : ∃ C2, C2 = mlC2 Tm t₀ cv := ⟨_, rfl⟩
  have hC2 : 0 ≤ C2 := hC2def ▸ ml_C2_nonneg Tm t₀ cv
  refine ⟨18 * cv + 130 + C2, by positivity, ?_⟩
  filter_upwards [eventually_big, gr_one_le_K] with n h hK1
  intro es B rg xs Wf H hD hN hB1 hV hOK hxl hbank
  -- sizes
  have hb16 := h.sixteen_le_b
  have hpb : p n = 6 * b n := rfl
  have hT2 : 2 ^ es.sum ≤ T n := by
    show 2 ^ es.sum ≤ 2 ^ logT n
    exact Nat.pow_le_pow_right (by norm_num) hN
  have hTpos : 1 ≤ T n := Nat.one_le_two_pow
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  obtain ⟨hlen1, -, hbK, hq, -⟩ := ml_counts H hK1 B
  have h3dℓ : 3 * d n * ℓ n ≤ p n := h.ℓ_bounds.2
  -- one exchange
  obtain ⟨V, hVdef⟩ : ∃ V, V = 2 ^ es.sum * B := ⟨_, rfl⟩
  obtain ⟨Xr, hXr⟩ : ∃ x : ℝ, x = 3 * swapConst * ((Tm + 12 * swapT t₀ + 5 : ℕ) : ℝ) * (V : ℝ) *
      (K n : ℝ) ^ Parameters.tau +
      ((6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) :=
    ⟨_, rfl⟩
  have hXs : ∀ j < xs.length,
      layXcStep Tm t₀ es.sum (K n) B rg (Wf (j + 1)) (xs.getD j default) ≤ ⌈Xr⌉₊ := by
    intro j hj
    have hok : (xs.getD j default).OK es.sum (K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact hOK _ (List.getElem_mem hj)
    have hs := layXcStep_le Tm t₀ es.sum (K n) B rg (Wf (j + 1)) hok (by omega)
    have hbk := hbank j hj
    have hmax : max 1 (K n) = K n := max_eq_right hK1
    rw [hmax, ← hVdef] at hs
    rw [← hVdef] at hbk
    generalize (∑ i, (Wf (j + 1) (rg (.sw i))).length) = bk at hs hbk
    have hnat : 6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 ≤
        6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 := by omega
    have hnat' : ((6 * bk + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) ≤
        ((6 * (swapT t₀ * (3 * V + 1)) + 34 * V + 2 * Tm + 6 * swapT t₀ + 23 : ℕ) : ℝ) := by
      exact_mod_cast hnat
    have hle : (layXcStep Tm t₀ es.sum (K n) B rg (Wf (j + 1)) (xs.getD j default) : ℝ) ≤ Xr := by
      rw [hXr]
      linarith
    exact Nat.cast_le.1 (hle.trans (Nat.le_ceil Xr))
  have hst := ml_xcLoop_le Tm t₀ es.sum (K n) B rg Wf (60 * (es.sum + B + 2) + 75) ⌈Xr⌉₊ xs hXs
  have hbt := ml_bitLoop_le es.sum B (14 * es.sum + 12) (layBits es (ℓ n) (K n)).length
  -- the natural-number bound
  have hNp : es.sum ≤ p n := by rw [hpb]; omega
  have hA1 : (layBits es (ℓ n) (K n)).length ≤ d n * K n := hlen1.trans (Nat.mul_le_mul hD hbK)
  have hA2 : 14 * es.sum + 12 + layMvCost es.sum B + 5 ≤ (18 * cv + 121) * (T n * p n) := by
    unfold layMvCost
    have hp1 : 1 ≤ p n := by omega
    have h2N : 1 ≤ 2 ^ es.sum := Nat.one_le_two_pow
    have e1 : 2 ^ es.sum * (18 * B + 20 * es.sum + 36) =
        18 * (2 ^ es.sum * B) + 20 * (2 ^ es.sum * es.sum) + 36 * 2 ^ es.sum := by ring
    have e2 : 2 ^ es.sum * es.sum ≤ T n * p n := Nat.mul_le_mul hT2 hNp
    have e3 : 2 ^ es.sum ≤ T n * p n := hT2.trans (Nat.le_mul_of_pos_right _ hp1)
    have e4 : es.sum ≤ T n * p n := hNp.trans (Nat.le_mul_of_pos_left _ hTpos)
    have e5 : (18 * cv + 121) * (T n * p n) = 18 * (cv * (T n * p n)) + 121 * (T n * p n) := by
      ring
    rw [e1, e5]
    omega
  have hA := Nat.mul_le_mul hA1 hA2
  have hxs' : xs.length * (60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5) ≤
      es.length * layQ (ℓ n) (K n) * (60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊) := by
    have : 60 * (es.sum + B + 2) + 75 + ⌈Xr⌉₊ + 5 = 60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊ := by
      ring
    rw [this]; exact Nat.mul_le_mul_right _ hxl
  have hN1 : layBitCost es.sum B (fun _ => 14 * es.sum + 12) (layBits es (ℓ n) (K n)).length +
      layXcLoopCost Tm t₀ es.sum (K n) B rg Wf (fun _ => 60 * (es.sum + B + 2) + 75) xs ≤
      d n * K n * ((18 * cv + 121) * (T n * p n)) +
        es.length * layQ (ℓ n) (K n) * (60 * (es.sum + B + 2) + 80 + ⌈Xr⌉₊) + 8 := by
    omega
  have hR1 := (Nat.cast_le (α := ℝ)).2 hN1
  simp only [Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat] at hR1
  -- real facts
  have hTr1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hPr1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hKr1 : (1 : ℝ) ≤ K n := by exact_mod_cast hK1
  have hDr1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hKr0 : (0 : ℝ) < K n := by linarith only [hKr1]
  have hKτ : (1 : ℝ) ≤ (K n : ℝ) ^ Parameters.tau := Real.one_le_rpow hKr1 tot_tau_nonneg
  have hKτ1 : (0 : ℝ) ≤ (K n : ℝ) ^ (Parameters.tau - 1) := Real.rpow_nonneg hKr0.le _
  have hKτe : (K n : ℝ) ^ Parameters.tau = (K n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) := by
    rw [Real.rpow_sub_one hKr0.ne']
    field_simp
  have hqK : (layQ (ℓ n) (K n) : ℝ) * K n ≤ ℓ n := by exact_mod_cast hq
  have hDℓ : (es.length : ℝ) * ℓ n ≤ p n := by
    have h1 : es.length * ℓ n ≤ p n := by
      have h2 : es.length * ℓ n ≤ d n * ℓ n := Nat.mul_le_mul_right _ hD
      have h3 : 3 * d n * ℓ n = 3 * (d n * ℓ n) := by ring
      omega
    exact_mod_cast h1
  have hVr : (V : ℝ) ≤ cv * ((T n : ℝ) * p n) := by rw [hVdef]; exact_mod_cast hV
  have hBV : (B : ℝ) ≤ V := by
    rw [hVdef]
    exact_mod_cast Nat.le_mul_of_pos_left B Nat.one_le_two_pow
  have hNr : (es.sum : ℝ) ≤ p n := by exact_mod_cast hNp
  have hXr0 : 0 ≤ Xr := by
    rw [hXr]
    have := mt_swapConst_nonneg
    have : (0 : ℝ) ≤ (K n : ℝ) ^ Parameters.tau := by linarith only [hKτ]
    positivity
  have hceil : (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := (Nat.ceil_lt_add_one hXr0).le
  have hXrb : 60 * ((es.sum : ℝ) + B + 2) + 80 + (⌈Xr⌉₊ : ℝ) ≤
      C2 * ((T n : ℝ) * p n * (K n : ℝ) ^ Parameters.tau) := by
    rw [hC2def, mlC2]
    refine ml_xr_le hTr1 hPr1 hKτ hNr hBV hVr (Nat.cast_nonneg _) (Nat.cast_nonneg _)
      (Nat.cast_nonneg _) mt_swapConst_nonneg ?_
    calc (⌈Xr⌉₊ : ℝ) ≤ Xr + 1 := hceil
      _ = _ := by rw [hXr]; push_cast; ring
  have hTP0 : (0 : ℝ) ≤ (T n : ℝ) * p n := by positivity
  have hexch : (es.length : ℝ) * layQ (ℓ n) (K n) * (60 * ((es.sum : ℝ) + B + 2) + 80 + ⌈Xr⌉₊) ≤
      C2 * ((T n : ℝ) * p n) * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) := by
    refine mt_lay_exch_le (Nat.cast_nonneg _) (Nat.cast_nonneg _) hqK hDℓ hKτe hKτ1 ?_
      (mul_nonneg hC2 hTP0)
    rw [mul_assoc]
    exact hXrb
  -- assembly
  have hDK : (1 : ℝ) ≤ (d n : ℝ) * K n := by nlinarith only [hDr1, hKr1]
  have hX1 : (T n : ℝ) * p n ≤ (T n : ℝ) * p n * ((d n : ℝ) * K n) := by
    nlinarith only [hDK, hTP0]
  have hX2 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) :=
    mul_nonneg hTP0 (mul_nonneg (by linarith only [hPr1]) hKτ1)
  have hX10 : (0 : ℝ) ≤ (T n : ℝ) * p n * ((d n : ℝ) * K n) := by linarith only [hX1, hTP0]
  have hTP1 : (1 : ℝ) ≤ (T n : ℝ) * p n := by nlinarith only [hTr1, hPr1]
  have hcvY : (0 : ℝ) ≤ (cv : ℝ) *
      ((T n : ℝ) * p n * ((p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1))) :=
    mul_nonneg (Nat.cast_nonneg _) hX2
  have hC2X : (0 : ℝ) ≤ C2 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := mul_nonneg hC2 hX10
  have h8 : (8 : ℝ) ≤ 8 * ((T n : ℝ) * p n * ((d n : ℝ) * K n)) := by
    linarith only [hX1, hTP1]
  rw [Nat.cast_add]
  linarith [hR1, hexch, hX1, h8, hC2X, hcvY, hX2]

/-! ### Setup, cleanup and reversal -/

/-- **The auxiliary passes.** The setup (`slySetupCost`), the cleanup (`slyCleanCost`) and the
reversal of the streams (`slyRevStreamsCost`) at `N ≤ b`, `2^N ≤ T`, `B ≤ 18 b r`, `W ≤ 26 b² r`,
`w ≤ 18 b` and at most `b²` moves of each kind cost at most `6 T + 2821 b⁴ r ≤ 7 T p`. -/
theorem ml_aux_le :
    ∀ᶠ n in atTop, ∀ (N B W w xM xX : ℕ), N ≤ b n → 2 ^ N ≤ T n → B ≤ 72 * (b n * r n) →
      W ≤ 80 * (b n ^ 2 * r n) → w ≤ 72 * b n → xM ≤ b n ^ 2 → xX ≤ b n ^ 2 →
      ((slySetupCost W N B (2 ^ ℓ n) w + slyCleanCost xM xX N (N + B + 2) B W +
        slyRevStreamsCost xM N xX (N + B + 2) : ℕ) : ℝ) ≤ 7 * ((T n : ℝ) * p n) := by
  filter_upwards [eventually_big, ml_small_le 11872 4 1] with n h hsm
  intro N B W w xM xX hN hTN hB hW hw hM hX
  have hb16 := h.sixteen_le_b
  have hQ : ((11872 * b n ^ 4 * r n ^ 1 : ℕ) : ℝ) ≤ T n * p n := hsm _ le_rfl
  push_cast at hQ
  rw [pow_one] at hQ
  have hr' : (2 : ℝ) ^ ℓ n = r n := by unfold r; push_cast; ring
  -- real facts
  have hb1 : (1 : ℝ) ≤ b n := by exact_mod_cast (show 1 ≤ b n by omega)
  have hr1 : (1 : ℝ) ≤ r n := mt_one_le_r n
  have hT1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hp1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hr0 : (0 : ℝ) ≤ r n := by linarith
  have hTp : (T n : ℝ) ≤ T n * p n := le_mul_of_one_le_right (by linarith) hp1
  have hb2 : (b n : ℝ) ≤ (b n : ℝ) ^ 2 := by
    calc (b n : ℝ) = (b n : ℝ) ^ 1 := (pow_one _).symm
      _ ≤ (b n : ℝ) ^ 2 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb3 : (b n : ℝ) ^ 2 ≤ (b n : ℝ) ^ 3 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb4 : (b n : ℝ) ^ 3 ≤ (b n : ℝ) ^ 4 := pow_le_pow_right₀ hb1 (by norm_num)
  have hb40 : (0 : ℝ) ≤ (b n : ℝ) ^ 4 := by positivity
  have hb4r : (b n : ℝ) ^ 4 ≤ (b n : ℝ) ^ 4 * r n := le_mul_of_one_le_right hb40 hr1
  have hb1Q : (b n : ℝ) ≤ (b n : ℝ) ^ 4 * r n := by linarith
  have hb2Q : (b n : ℝ) ^ 2 ≤ (b n : ℝ) ^ 4 * r n := by linarith
  have hb3Q : (b n : ℝ) ^ 3 ≤ (b n : ℝ) ^ 4 * r n := by linarith
  have h1Q : (1 : ℝ) ≤ (b n : ℝ) ^ 4 * r n := by linarith
  have hbr : (b n : ℝ) * r n ≤ (b n : ℝ) ^ 4 * r n :=
    mul_le_mul_of_nonneg_right (by linarith) hr0
  have hb2r : (b n : ℝ) ^ 2 * r n ≤ (b n : ℝ) ^ 4 * r n :=
    mul_le_mul_of_nonneg_right (by linarith) hr0
  have hb3r : (b n : ℝ) ^ 3 * r n ≤ (b n : ℝ) ^ 4 * r n :=
    mul_le_mul_of_nonneg_right hb4 hr0
  have hrQ : (r n : ℝ) ≤ (b n : ℝ) ^ 4 * r n := le_mul_of_one_le_left hr0 (by linarith)
  -- the hypotheses in `ℝ`
  have hN' : (N : ℝ) ≤ b n := by exact_mod_cast hN
  have hTN' : (2 : ℝ) ^ N ≤ T n := by exact_mod_cast hTN
  have hB' : (B : ℝ) ≤ 72 * (b n * r n) := by exact_mod_cast hB
  have hW' : (W : ℝ) ≤ 80 * ((b n : ℝ) ^ 2 * r n) := by exact_mod_cast hW
  have hw' : (w : ℝ) ≤ 72 * b n := by exact_mod_cast hw
  have hM' : (xM : ℝ) ≤ (b n : ℝ) ^ 2 := by exact_mod_cast hM
  have hX' : (xX : ℝ) ≤ (b n : ℝ) ^ 2 := by exact_mod_cast hX
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hB0 : (0 : ℝ) ≤ B := Nat.cast_nonneg _
  have hM0 : (0 : ℝ) ≤ xM := Nat.cast_nonneg _
  have hX0 : (0 : ℝ) ≤ xX := Nat.cast_nonneg _
  -- products
  have hrw : (r n : ℝ) * w ≤ 72 * (b n * r n) := by
    have := mul_le_mul_of_nonneg_left hw' hr0
    linarith
  have hMN : (xM : ℝ) * N ≤ (b n : ℝ) ^ 3 := by
    calc (xM : ℝ) * N ≤ (b n : ℝ) ^ 2 * b n := mul_le_mul hM' hN' hN0 (by positivity)
      _ = (b n : ℝ) ^ 3 := by ring
  have hXwX : (xX : ℝ) * (N + B + 2) ≤ (b n : ℝ) ^ 3 + 72 * ((b n : ℝ) ^ 3 * r n) +
      2 * (b n : ℝ) ^ 2 := by
    have h1 : (N : ℝ) + B + 2 ≤ b n + 72 * (b n * r n) + 2 := by linarith
    calc (xX : ℝ) * (N + B + 2) ≤ (b n : ℝ) ^ 2 * (b n + 72 * (b n * r n) + 2) :=
          mul_le_mul hX' h1 (by positivity) (by positivity)
      _ = _ := by ring
  -- the three passes
  have hS : ((slySetupCost W N B (2 ^ ℓ n) w : ℕ) : ℝ) ≤
      4 * T n + 1080 * ((b n : ℝ) ^ 4 * r n) + 25 := by
    unfold slySetupCost synMulRCost
    push_cast
    rw [hr']
    linarith
  have hC : ((slyCleanCost xM xX N (N + B + 2) B W : ℕ) : ℝ) ≤
      2 * T n + 1664 * ((b n : ℝ) ^ 4 * r n) + 72 := by
    unfold slyCleanCost
    push_cast
    linarith
  have hR : ((slyRevStreamsCost xM N xX (N + B + 2) : ℕ) : ℝ) ≤
      8540 * ((b n : ℝ) ^ 4 * r n) + 50 := by
    unfold slyRevStreamsCost slyRevStreamCost
    push_cast
    linarith
  simp only [Nat.cast_add]
  linarith

/-! ### The pipeline instance -/

/-- The bank registers of `slyRw'` are those of the base file. -/
theorem ml_slyRw'_sw {Ka : ℕ} (R : Fin (nT SXReg) → List (Fin (prime + Ka + 4))) (es : List ℕ)
    (ℓ K B : ℕ) (i : Fin (swapT 6)) :
    slyRw' R es ℓ K B (slyRg (.sw i)) = R (slyRg (.sw i)) := by
  rw [slyRw'_eq, Function.update_of_ne (sly_regs.l.disj _ _),
    Function.update_of_ne (sly_regs.l.disj _ _),
    ldgPost_rg sly_regs _ _ _ _ _ _ (by simp) (by simp)]

/-- The bank registers of the canonical file `slyR₂` are empty. -/
theorem ml_slyR₂_sw {Ka : ℕ} (W E N B : ℕ) (v₀ : SynW → List (Fin (prime + Ka + 4)))
    (i : Fin (swapT 6)) : slyR₂ Ka W E N B v₀ (slyRg (.sw i)) = [] :=
  synG_synIdle_sw _ _ _ _

/-- **The layout programs of the synthetic transforms against `totConv`.** At the pipeline
parameters (axes `cvAx (t n)`, coefficient width `dsW n`, records of `2^ℓ dsW n` symbols, the
writer word width `slyW N B ℓ (d - 1)`), for any axis word `E` and any wires `v₀`, the costs of
the forward and the opposite layout programs sum to at most a constant times `totConv n`,
eventually. The costs do not depend on `E` or `v₀`: the bank registers of the canonical file
`slyR₂` are empty. -/
theorem ml_lay_cost_le_gen :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ (E : ℕ) (v₀ : SynW → List (Fin (prime + mnKa + 4))),
      ((slyFwdCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (dsW n)
          (slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * dsW n) (ℓ n) (d n - 1)) E v₀ +
        slyOppCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (dsW n)
          (slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * dsW n) (ℓ n) (d n - 1)) E v₀ : ℕ) : ℝ) ≤
        C * totConv n := by
  obtain ⟨Cs, hCs0, hst⟩ := ml_stage_le (nT SXReg) 6 mnKa 12
  refine ⟨2 * Cs + 16, ?_⟩
  filter_upwards [eventually_big, hst, ml_writer_le 72 80, ml_aux_le, gr_one_le_K] with n h hst
    hwr haux hK1
  intro E v₀
  simp only [slyFwdCost, slyOppCost, slyStageCost, slyUnstageCost]
  generalize hes : List.ofFn (cvAx (t n)) = es
  generalize hB : 2 ^ ℓ n * dsW n = B
  have H : LayHyp es (ℓ n) (K n) := hes ▸ mn_layHyp h
  have hsum : es.sum = logT n - ℓ n := hes ▸ ds_sum_cvAx h.1
  have hlen : es.length ≤ d n := by rw [← hes, List.length_ofFn]; omega
  have hℓ : ℓ n ≤ logT n := mt_ℓ_le_logT h
  have hN : es.sum ≤ logT n := by omega
  have hb16 := h.sixteen_le_b
  have hb1 : 1 ≤ b n := by omega
  have hNb : es.sum ≤ b n := hN.trans (mt_logT_le_b h)
  have hdb : d n ≤ b n := mt_d_le_b n
  have hℓb : ℓ n ≤ b n := mt_ℓ_le_b h
  have hKb : K n ≤ b n := mt_K_le_b n
  have hr1 : 1 ≤ r n := Nat.one_le_two_pow
  have hw3 : dsW n ≤ 12 * p n := by
    have := ds_dsW_le h.1; unfold p; omega
  have hw18 : dsW n ≤ 72 * b n := by unfold p at hw3; omega
  have hwpos : 1 ≤ dsW n := by have := ds_w_A n; omega
  have hB1 : 1 ≤ B := by
    rw [← hB]
    exact Nat.one_le_iff_ne_zero.2 (Nat.mul_ne_zero (by positivity) (by omega))
  have hT2 : 2 ^ es.sum ≤ T n := by
    show 2 ^ es.sum ≤ 2 ^ logT n
    exact Nat.pow_le_pow_right (by norm_num) hN
  have hV : 2 ^ es.sum * B ≤ 12 * (T n * p n) := by
    rw [← hB, ← mul_assoc, ← pow_add, hsum, Nat.sub_add_cancel hℓ]
    show 2 ^ logT n * dsW n ≤ 12 * (2 ^ logT n * p n)
    calc 2 ^ logT n * dsW n ≤ 2 ^ logT n * (12 * p n) := Nat.mul_le_mul_left _ hw3
      _ = 12 * (2 ^ logT n * p n) := by ring
  have hBb : B ≤ 72 * (b n * r n) := by
    rw [← hB]
    show r n * dsW n ≤ _
    calc r n * dsW n ≤ r n * (72 * b n) := Nat.mul_le_mul_left _ hw18
      _ = 72 * (b n * r n) := by ring
  have hbr : b n * r n ≤ b n ^ 2 * r n := by
    rw [sq]; exact Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ hb1)
  have hBb2 : B ≤ 72 * (b n ^ 2 * r n) := hBb.trans (Nat.mul_le_mul_left _ hbr)
  have hWb : slyW es.sum B (ℓ n) (d n - 1) ≤ 80 * (b n ^ 2 * r n) := by
    unfold slyW
    have h1 : es.sum * es.sum ≤ b n * b n := Nat.mul_le_mul hNb hNb
    have h2 : b n * b n ≤ b n ^ 2 * r n := by rw [sq]; exact Nat.le_mul_of_pos_right _ hr1
    have h3 : b n ≤ b n ^ 2 * r n := (Nat.le_mul_of_pos_left _ hb1).trans h2
    have h4 : b n * r n ≤ b n ^ 2 * r n := hbr
    omega
  obtain ⟨hlen1, hlenX, hbK, hq, hqℓ⟩ := ml_counts H hK1 B
  have hxM : (layBits es (ℓ n) (K n)).length ≤ b n ^ 2 := by
    rw [sq]
    exact hlen1.trans ((Nat.mul_le_mul hlen hbK).trans (Nat.mul_le_mul hdb hKb))
  have hxX : (layXcs es (ℓ n) (K n) B).length ≤ b n ^ 2 := by
    rw [sq]
    exact hlenX.trans ((Nat.mul_le_mul hlen hqℓ).trans (Nat.mul_le_mul hdb hℓb))
  -- the files
  obtain ⟨R, hR⟩ : ∃ R, R = slyR₂ mnKa (slyW es.sum B (ℓ n) (d n - 1)) E es.sum B v₀ :=
    ⟨_, rfl⟩
  rw [← hR]
  have hRsw : ∀ i, R (slyRg (.sw i)) = [] := fun i => by rw [hR]; exact ml_slyR₂_sw _ _ _ _ _ _
  have hA : 0 < B := hB1
  -- forward: the bank of exchange `j`
  have hbankF : ∀ j < (layXcs es (ℓ n) (K n) B).length,
      ∑ i, ((fun j => ldlW slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
        (ldgPost slyRg slyLr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
        (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + j)) (j + 1)
        (slyRg (.sw i))).length ≤ swapT 6 * (3 * (2 ^ es.sum * B) + 1) := by
    intro j hj
    have hok : ((layXcs es (ℓ n) (K n) B).getD j default).OK es.sum (K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact layXcs_OK B H _ (List.getElem_mem hj)
    have hbk := mt_lay_bank_le sly_regs.l sxHd_inj
      (ldgPost slyRg slyLr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) es.sum (es.sum + B + 2)
      (layBits es (ℓ n) (K n)) (layXcs es (ℓ n) (K n) B) j (3 * (2 ^ es.sum * B))
      (fun k => mt_lay_hs_le hok hA k)
    have hR0 : ∑ i, (ldgPost slyRg slyLr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)
        (slyRg (.sw i))).length = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [mt_lay_post_rg sly_regs.l R es (ℓ n) (K n) B _ (by simp) (by simp), hRsw]
      rfl
    rw [hR0, zero_add] at hbk
    exact hbk
  have hF := hst es B slyRg (layXcs es (ℓ n) (K n) B)
    (fun j => ldlW slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
      (ldgPost slyRg slyLr R es (ℓ n) (K n) B (layXcs es (ℓ n) (K n) B)) (layBits es (ℓ n) (K n))
      (layXcs es (ℓ n) (K n) B) ((layBits es (ℓ n) (K n)).length + j))
    H hlen hN hB1 hV (layXcs_OK B H) hlenX hbankF
  -- opposite: the bank of exchange `j` of the reversed list
  have hbankO : ∀ j < (layXcs es (ℓ n) (K n) B).reverse.length,
      ∑ i, (ldlWU slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2)
        (slyRw' R es (ℓ n) (K n) B) (layXcs es (ℓ n) (K n) B).reverse
        ((layBits es (ℓ n) (K n)).map Prod.swap).reverse (j + 1)
        (slyRg (.sw i))).length ≤ swapT 6 * (3 * (2 ^ es.sum * B) + 1) := by
    intro j hj
    have hok : ((layXcs es (ℓ n) (K n) B).reverse.getD j default).OK es.sum (K n) B := by
      rw [List.getD_eq_getElem _ _ hj]
      exact layXcs_OK B H _ (List.mem_reverse.1 (List.getElem_mem hj))
    rw [ldlWU_X sxHd (prime + mnKa) es.sum (es.sum + B + 2) _ _ _ (by omega)]
    have hbk := ml_bankX_le sly_regs.l sxHd_inj (slyRw' R es (ℓ n) (K n) B) (es.sum + B + 2)
      (layXcs es (ℓ n) (K n) B).reverse j (3 * (2 ^ es.sum * B)) (fun k => mt_lay_hs_le hok hA k)
    have hR0 : ∑ i, (slyRw' R es (ℓ n) (K n) B (slyRg (.sw i))).length = 0 := by
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [ml_slyRw'_sw, hRsw]
      rfl
    rw [hR0, zero_add] at hbk
    exact hbk
  have hO := hst es B slyRg (layXcs es (ℓ n) (K n) B).reverse
    (ldlWU slyRg slyLr sxHd (prime + mnKa) es.sum (es.sum + B + 2) (slyRw' R es (ℓ n) (K n) B)
      (layXcs es (ℓ n) (K n) B).reverse ((layBits es (ℓ n) (K n)).map Prod.swap).reverse)
    H hlen hN hB1 hV
    (fun x hx => layXcs_OK B H x (List.mem_reverse.1 hx))
    (by rw [List.length_reverse]; exact hlenX) hbankO
  -- the writer and the auxiliary passes
  have hWr := hwr es B _ H hlen hN hBb2 hWb
  have hAux := haux es.sum B _ (dsW n) (layBits es (ℓ n) (K n)).length
    (layXcs es (ℓ n) (K n) B).length hNb hT2 hBb hWb hw18 hxM hxX
  -- against `totConv`
  have hconv := mt_lay_le_conv h
  have hTr1 : (1 : ℝ) ≤ T n := mt_one_le_T n
  have hPr1 : (1 : ℝ) ≤ p n := mt_one_le_p h
  have hKr1 : (1 : ℝ) ≤ K n := by exact_mod_cast hK1
  have hDr1 : (1 : ℝ) ≤ d n := by exact_mod_cast h.one_le_d
  have hKτ1 : (0 : ℝ) ≤ (K n : ℝ) ^ (Parameters.tau - 1) :=
    Real.rpow_nonneg (by linarith only [hKr1]) _
  have hTP0 : (0 : ℝ) ≤ (T n : ℝ) * p n := by positivity
  have hDK : (1 : ℝ) ≤ (d n : ℝ) * K n := by nlinarith only [hDr1, hKr1]
  have hpK : (0 : ℝ) ≤ (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1) := by positivity
  have hTpX : (T n : ℝ) * p n ≤ (T n : ℝ) * p n *
      ((d n : ℝ) * K n + (p n : ℝ) * (K n : ℝ) ^ (Parameters.tau - 1)) := by
    nlinarith only [hDK, hpK, hTP0]
  have hCsX := mul_le_mul_of_nonneg_left hconv hCs0
  have hTpc : (T n : ℝ) * p n ≤ totConv n := hTpX.trans hconv
  push_cast at hF hO hAux ⊢
  linarith [hF, hO, hWr, hAux, hCsX, hTpc, hTP0]

/-! ### The cost terms of the layout bundle -/

/-- The axis word of the pipeline: bit `i` set exactly on the long axes `i ≥ numHalf n`. -/
def mlE (n : ℕ) : ℕ := (2 ^ (d n - 1) - 1) / 2 ^ numHalf n * 2 ^ numHalf n

/-- The writer's word width at `n`: `slyW N B ℓ (d - 1)`, `N = Σ aᵢ`, `B = 2^ℓ w`. -/
def mlW (w : ℕ → ℕ) (n : ℕ) : ℕ :=
  slyW (List.ofFn (cvAx (t n))).sum (2 ^ ℓ n * w n) (ℓ n) (d n - 1)

/-- The layout cost of the forward transform at `n`. -/
noncomputable def mlCL (w : ℕ → ℕ) (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))) (n : ℕ) :
    ℕ :=
  slyFwdCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (w n) (mlW w n) (mlE n) (v₀ n)

/-- The layout cost of the opposite transform at `n`. -/
noncomputable def mlCL' (w : ℕ → ℕ) (v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4))) (n : ℕ) :
    ℕ :=
  slyOppCost mnKa (List.ofFn (cvAx (t n))) (ℓ n) (K n) (ℓ n) (w n) (mlW w n) (mlE n) (v₀ n)

/-- **The layout costs of the bundle against `totConv`**: `ml_lay_cost_le_gen` at `E = mlE n`,
coefficient width `dsW n`. -/
theorem ml_lay_cost_le :
    ∃ C : ℝ, ∀ᶠ n in atTop, ∀ v₀ : ℕ → SynW → List (Fin (prime + mnKa + 4)),
      ((mlCL dsW v₀ n + mlCL' dsW v₀ n : ℕ) : ℝ) ≤ C * totConv n := by
  obtain ⟨C, hC⟩ := ml_lay_cost_le_gen
  refine ⟨C, ?_⟩
  filter_upwards [hC] with n hn
  intro v₀
  exact hn (mlE n) (v₀ n)

end IntegerMultBounds.MathlibTM2.Cost
