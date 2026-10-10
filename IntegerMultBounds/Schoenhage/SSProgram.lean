import IntegerMultBounds.Schoenhage.SSCost

/-! The Schönhage–Strassen multiplier as a literal multitape program: the
compiled word program on 64 tapes, with a `HoareTime` contract on encoded
tapes. -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The compiled multiplier. -/
noncomputable def ssProgram : Program 𝕋 (compile (a := 0) (by decide) ssMain).1 0 :=
  (compile (a := 0) (by decide) ssMain).2

/-- Exact products below `2^m` in `O(m log m log log m)` transitions of a literal 64-tape machine. -/
theorem ssProgram_hoare {m a b : ℕ} (hm : 1 ≤ m) (ha : a < 2 ^ m) (hb : b < 2 ^ m) (σ : Fin 𝕋 → WTape)
    (hS : SSStart (topN m) a b σ) :
    HoareTime ssProgram (· = enc σ) (fun T => ∃ σ', T = enc σ' ∧ (σ' tIn).right = [rwd (topN m) (a * b)])
      (costC cA cB cC0 * (4 * m + 1) * (bitlen (4 * m) + 1) * (3 * bitlen (bitlen (4 * m)) + 1) +
        2400 * m + 50000) := by
  obtain ⟨σ', k, hx, hq, hk⟩ := runs_ssExact hm ha hb σ hS
  exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun T h => ⟨σ', h, hq⟩) hk

end IntegerMultBounds.Schoenhage
