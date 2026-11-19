module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.Params
public import IntegerMultBounds.MathlibTM2.M8.Global.Branching97
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-!
# The stage-2 high body at its rows

At the PR97 exponent `τ₁ = 1 - 3734039/10¹²` the exponents of the core hold with atom width
exponent `θ = 1/1000` (`exponents`). At every width `e` past `Params.threshold b`, with the joined
digits `r b e` and the padded rows `padded b e`, the high body transposes the array within a constant
times `V e^τ₂` (`runs`): the join and separation cost `(r b e + 1) V ≤ A √e V`, the padding at
most doubles the volume, and the core costs its bound at width `e - r b e ≤ e`.
-/

@[expose] public section

namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCost

noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open RecursiveRowPadding (withRows)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open Stage2Width (tau2)
open RevMachine
open FamilyRoot (FamilySpec)
open HighBody (Exponents tau₂ JoinCounters Fits Ready privateBanks)
open Params (r padded view threshold)

/-- The atom width exponent `θ = 1 / K`. -/
abbrev K : ℕ := 1000

/-- **The exponents at the PR97 exponent.** -/
theorem exponents [M8.Machine.Net] (h : M8.Machine.BudgetBound.tau = M8.Global.Branching97.tau) :
    Exponents K := by
  have hs : Cost.tauS = 1 - 12402 / 10 ^ 8 := by
    simp only [Cost.tauS, Stage2Moments.savingB]; push_cast; ring
  have ht : M8.Machine.BudgetBound.tau = 1 - 3734039 / 10 ^ 12 := by
    rw [h]; simp only [M8.Global.Branching97.tau, M8.Global.Branching97.saving]
  refine ⟨by norm_num, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hs, ht]; norm_num
  · rw [ht]; norm_num
  · rw [ht]; norm_num
  · simp only [tau₂, tau2, hs, ht]; norm_num
  · simp only [tau₂, tau2, hs, ht]; norm_num

/-- The cost of the high body as a multiple of `V e^τ₂`. -/
theorem cost_le {τ A A' C' : ℝ} (hτ : 1 / 2 ≤ τ) (hA : 0 ≤ A) {e r : ℕ} (hr : r + 2 ≤ e)
    {V U : ℝ} (hV : 1 ≤ V) (hU : 0 ≤ U) (hUV : U ≤ 2 * V) {c : ℝ}
    (hrs : ((r + 1 : ℕ) : ℝ) ≤ A * (e : ℝ) ^ (1 / 2 : ℝ))
    (hc : c ≤ A' * (r + 1) * V + 826 * U + 5 + C' * U * ((e - r : ℕ) : ℝ) ^ τ) (hA' : 0 ≤ A') :
    c ≤ (A' * A + 1657 + 2 * |C'|) * V * (e : ℝ) ^ τ := by
  have he : (1 : ℝ) ≤ e := by exact_mod_cast (show 1 ≤ e by omega)
  have hE : 1 ≤ (e : ℝ) ^ τ := Real.one_le_rpow he (by linarith)
  have hsq : (e : ℝ) ^ (1 / 2 : ℝ) ≤ (e : ℝ) ^ τ := Real.rpow_le_rpow_of_exponent_le he hτ
  have her : ((e - r : ℕ) : ℝ) ^ τ ≤ (e : ℝ) ^ τ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast Nat.sub_le e r) (by linarith)
  have her0 : 0 ≤ ((e - r : ℕ) : ℝ) ^ τ := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have h1 : A' * (r + 1) * V ≤ A' * A * V * (e : ℝ) ^ τ := by
    have : ((r : ℝ) + 1) ≤ A * (e : ℝ) ^ τ := by
      have := hrs; push_cast at this; nlinarith
    have hV0 : 0 ≤ V := by linarith
    have := mul_le_mul_of_nonneg_left this (mul_nonneg hA' hV0)
    nlinarith
  have h2 : C' * U * ((e - r : ℕ) : ℝ) ^ τ ≤ 2 * |C'| * V * (e : ℝ) ^ τ := by
    have hab : C' * U * ((e - r : ℕ) : ℝ) ^ τ ≤ |C'| * U * ((e - r : ℕ) : ℝ) ^ τ := by
      have := le_abs_self C'
      have : 0 ≤ U * ((e - r : ℕ) : ℝ) ^ τ := mul_nonneg hU her0
      nlinarith
    have hU' : |C'| * U * ((e - r : ℕ) : ℝ) ^ τ ≤ |C'| * (2 * V) * (e : ℝ) ^ τ := by
      have h0 := abs_nonneg C'
      have : U * ((e - r : ℕ) : ℝ) ^ τ ≤ (2 * V) * (e : ℝ) ^ τ :=
        mul_le_mul hUV her her0 (by linarith)
      nlinarith
    nlinarith
  have h3 : 826 * U + 5 ≤ 1657 * V * (e : ℝ) ^ τ := by nlinarith
  nlinarith

/-- **Below the threshold**: a stage-1 cost at the larger exponent `τ₁` is a constant times the
stage-2 bound at `τ₂ ≤ τ₁`, since the width is bounded. -/
theorem small_le {τ₁ τ₂ C₀ : ℝ} (hτ : τ₂ ≤ τ₁) (hC₀ : 0 ≤ C₀) {E e : ℕ} (he : e < E)
    {V c : ℝ} (hV : 0 ≤ V) (hc : c ≤ C₀ * V * ((max 1 e : ℕ) : ℝ) ^ τ₁) :
    c ≤ C₀ * (E : ℝ) ^ (τ₁ - τ₂) * V * ((max 1 e : ℕ) : ℝ) ^ τ₂ := by
  have hm : (1 : ℝ) ≤ ((max 1 e : ℕ) : ℝ) := by exact_mod_cast le_max_left 1 e
  have hmE : ((max 1 e : ℕ) : ℝ) ≤ E := by exact_mod_cast max_le (by omega) he.le
  have hsplit : ((max 1 e : ℕ) : ℝ) ^ τ₁ = ((max 1 e : ℕ) : ℝ) ^ (τ₁ - τ₂) * ((max 1 e : ℕ) : ℝ) ^ τ₂ := by
    rw [← Real.rpow_add (by linarith)]; ring_nf
  have hle : ((max 1 e : ℕ) : ℝ) ^ (τ₁ - τ₂) ≤ (E : ℝ) ^ (τ₁ - τ₂) :=
    Real.rpow_le_rpow (by linarith) hmE (by linarith)
  have hpos : 0 ≤ ((max 1 e : ℕ) : ℝ) ^ τ₂ := Real.rpow_nonneg (by linarith) _
  rw [hsplit] at hc
  have : C₀ * V * (((max 1 e : ℕ) : ℝ) ^ (τ₁ - τ₂) * ((max 1 e : ℕ) : ℝ) ^ τ₂) ≤
      C₀ * V * ((E : ℝ) ^ (τ₁ - τ₂) * ((max 1 e : ℕ) : ℝ) ^ τ₂) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hle hpos) (mul_nonneg hC₀ hV)
  nlinarith

variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- **The stage-2 high body at its rows.** -/
theorem runs (hspec : FamilySpec capacity) (hτ : Exponents K) {b : ℕ} (hb : 2 ≤ b) :
    ∃ C : ℝ, ∀ P e G B : ℕ, threshold b ≤ e → 0 < P → 0 < G → 0 < B →
      ∀ (hs : Fin 6 → List Bool) (rs ss op oe : List Bool),
      RecursiveDimensionBank.Headers (originalDescriptor P e G B) hs → JoinCounters P e (r b e) G B rs ss op oe →
      ∀ ph : Fin 4 → List Bool,
      M8.Machine.ArbitraryWidthPaddedPiecePadding.Headers (joinedDescriptor prime P e (r b e) G B) (padded b e) ph →
      ∀ (f₀ : ℤ → Fin (prime+4)) (p₀ : ℤ) (node₀ scalar₀ : Tapes 1 prime) (st₀ : Tapes 2 prime),
      M8.Machine.CallReady.Ready f₀ p₀ node₀ scalar₀ st₀ →
      ∀ (f : ℤ → Fin (prime+4)) (p : ℤ) (node : Tapes 1 prime) (st : Tapes 2 prime), Ready f p node st →
      ∀ {t : ℕ} (caller : Tapes t prime) (focus : Fin t)
        (x : Fin (volume prime (originalDescriptor P e G B)) → ZMod 2),
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ K ∧
        HoareTime (HighBody.program capacity focus)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st caller)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c := by
  obtain ⟨C', hC'⟩ := HighBody.runs capacity hspec hτ
  set A' : ℝ := ((M8.Machine.ArbitraryWidthHighExchangeJoin.coefficient +
    M8.Machine.RadixHighBlockSeparateRun.coefficient prime : ℕ) : ℝ)
  set A : ℝ := ((3 * (Params.c b * Params.W) + 1 : ℕ) : ℝ)
  refine ⟨A' * A + 1657 + 2 * |C'|, fun P e G B he hP hG hB hs rs ss op oe hv hj ph hph f₀ p₀ node₀ scalar₀ st₀
    ready₀ f p node st hready t caller focus x hf hh => ?_⟩
  have hr := Params.fit_of_threshold hb he
  obtain ⟨c, hc, hrun⟩ := hC' P e (r b e) G B (by omega) hP hG hB hs rs ss op oe hv hj (padded b e) ph
    (Params.rows_le b e) hph (Params.fits hb hP hG hB hr) f₀ p₀ node₀ scalar₀ st₀ ready₀ f p node st hready
    caller focus x hf hh
  refine ⟨c, ?_, hrun⟩
  have hp : (originalDescriptor P e G B).Positive :=
    ⟨hP, (by change 0 < 1; decide), (by change 0 < 1; decide), hG, hB⟩
  have hV : (1 : ℝ) ≤ volume prime (originalDescriptor P e G B) := by
    exact_mod_cast RecursiveAffinePrepare.volume_positive Params.prime_two _ hp
  have hU : (volume prime (view b P e G B) : ℝ) ≤ 2 * volume prime (originalDescriptor P e G B) := by
    exact_mod_cast Params.volume_le (by omega)
  exact cost_le hτ.two
    (Nat.cast_nonneg _) hr hV (Nat.cast_nonneg _) hU (Params.r_succ_le hb (by omega)) hc (Nat.cast_nonneg _)

end
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCost
