module

import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsTime
public import IntegerMultBounds.MathlibTM2.Fast.Glue
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainTimeGlue
public import IntegerMultBounds.MathlibTM2.Fast.CompactMainRunsCost
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
import Mathlib.Data.Nat.Factorial.DoubleFactorial
import Mathlib.Analysis.SpecialFunctions.Bernstein
import Mathlib.Algebra.Order.Ring.Star

/-! Final finite-machine packaging for the compact branch. The actual execution
and complete transform-cost hypotheses remain explicit until main assembly closes. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Fast.Main
open IntegerMultBounds IntegerMultBounds.MathlibTM2 Filter Asymptotics
open IntegerMultBounds.MathlibTM2.Cost IntegerMultBounds.MathlibTM2.Host
open IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
open IntegerMultBounds.MathlibTM2.LayerMachine
open IntegerMultBounds.Networks.Shared50ModularControl (prime)
noncomputable section

/-- An eventual exact main execution bound and complete transform-cost estimate
produce one fixed finite machine at the explicit dyadic saving. -/
theorem compactMulInTime_of_main_exec
    {P U : Type} [Fintype P] [Fintype U] {H Q A : ℕ}
    (body : P → Pr P H Q A U) (pm : P) (v₀ : HS H Q A U)
    {K : ℕ} {Lb : LProc → MnPr (prime + K)} {w : ℕ → ℕ}
    {σ : ℕ → LReg SXReg → List (Fin (prime + K + 4))} (D : MnDist K Lb w σ)
    (cF cO : ℕ → ℕ) (c extra : ℕ) {Cs : ℝ}
    (hCs : ∀ᶠ n in atTop, ((cF n + cO n : ℕ) : ℝ) ≤ Cs * CompactTotal.conv n)
    (hexec : ∀ᶠ n in atTop, ∀ x y, (pairEnc (x, y)).length = n →
      HostMulWithin body pm v₀
        (compactMainTime D (fun n => compactMainRuns D cF cO n + extra) H c) x y) :
    MulInTime (4223103985 / 2 ^ 46 : ℝ) := by
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hexec
  have hfast : ∀ x y, n₀ ≤ (pairEnc (x, y)).length →
      HostMulWithin body pm v₀
        (compactMainTime D (fun n => compactMainRuns D cF cO n + extra) H c) x y := by
    intro x y hn
    exact hn₀ _ hn x y rfl
  exact mulInTime_of_dispatch body pm v₀ _ n₀ hfast
    (compactMain_runs_time_isBigO D cF cO H c extra hCs)

end
end IntegerMultBounds.MathlibTM2.Fast.Main
