module

public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCost
public import IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighBodyWithin
public import IntegerMultBounds.MathlibTM2.M8.Global.Branching97
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity

/-! The selected row padding instantiates the bounded high body. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCostWithin
noncomputable section
open IntegerMultBounds.Machine
open Networks.Shared50ModularControl (prime)
open RecursiveInterchangeLayout (Descriptor volume)
open ArbitraryWidthHighLayout
open SharedPlacementAlphabet (setTape)
open M8.Machine.ArbitraryWidthHighExchangeShared (sourceWord)
open RevMachine
open HighBody (Exponents tau₂ JoinCounters Fits Ready privateBanks)
open Params (r padded view threshold)
open HighCost (K cost_le)
variable [M8.Machine.Net] {k : ℕ} (capacity : Fintype.card (Graph.PC (RevHalf.pcs rev97m).length) ≤ 2^k)

/-- **The stage-2 high body at its rows.** -/
theorem runs (cutoff : ℕ)
    (hcut : ∀ n, cutoff ≤ n → 1 ≤ M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n ∧
      M8.Machine.ArbitraryWidthHighPrepare.highDepth prime n < n) (hτ : Exponents K) {b : ℕ} (hb : 2 ≤ b) :
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
      caller.tape focus = sourceWord x → caller.head focus = 0 → ∀ lo hi : ℤ,
      (∀ j, lo+(HighBodyWithin.coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤
        (privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st caller).head j ∧
        (privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st caller).head j+
          (HighBodyWithin.coefficient k cutoff*volume prime (originalDescriptor P e G B) : ℕ) ≤ hi) → ∃ c : ℕ,
        (c : ℝ) ≤ C * volume prime (originalDescriptor P e G B) * (e : ℝ) ^ tau₂ K ∧
        HoareWithin (HighBody.program capacity focus)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st caller)
          (· = privateBanks capacity K hs rs ss op oe f₀ p₀ node₀ scalar₀ st₀ ph (view b P e G B) f p node st
            (setTape caller focus (sourceWord (Shared50RecursiveNodeRows.transpose (one_dvd _) x)) 0)) c (fun z => ∀ j, lo ≤ z.head j ∧ z.head j ≤ hi) := by
  obtain ⟨C', hC'⟩ := HighBodyWithin.runs capacity cutoff hcut hτ
  set A' : ℝ := ((M8.Machine.ArbitraryWidthHighExchangeJoin.coefficient +
    M8.Machine.RadixHighBlockSeparateRun.coefficient prime : ℕ) : ℝ)
  set A : ℝ := ((3 * (Params.c b * Params.W) + 1 : ℕ) : ℝ)
  refine ⟨A' * A + 1657 + 2 * |C'|, fun P e G B he hP hG hB hs rs ss op oe hv hj ph hph f₀ p₀ node₀ scalar₀ st₀
    ready₀ f p node st hready t caller focus x hf hh lo hi hm => ?_⟩
  have hr := Params.fit_of_threshold hb he
  obtain ⟨c, hc, hrun⟩ := hC' P e (r b e) G B (by omega) hP hG hB hs rs ss op oe hv hj (padded b e) ph
    (Params.rows_le b e) hph (Params.fits hb hP hG hB hr) (Params.volume_le (by omega)) f₀ p₀ node₀ scalar₀ st₀ ready₀ f p node st hready
    caller focus x hf hh lo hi hm
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
end IntegerMultBounds.MathlibTM2.M8.Stage2Machine.HighCostWithin
