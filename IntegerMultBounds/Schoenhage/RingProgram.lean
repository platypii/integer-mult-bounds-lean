import IntegerMultBounds.Schoenhage.RingSpec

/-! The packed ring product as a literal 84-tape program with a `HoareTime`
contract stating the truncated negacyclic Gaussian product (`ringProgram_spec`),
and its step bound `O(N log N log log N)` in the packed size
`N = W r` (`ringCost_le`). -/

namespace IntegerMultBounds.Schoenhage

open Machine Strm Tp Schedule

/-- The compiled ring product. -/
noncomputable def ringProgram : Program 𝕌 (compile (a := 0) (by decide) ringProd).1 0 :=
  (compile (a := 0) (by decide) ringProd).2

theorem ringProgram_hoare {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} {τ : Fin 𝕌 → WTape}
    (h : RingSetup Wd r w s N fs gs τ) :
    HoareTime ringProgram (· = enc τ) (· = enc (Function.update τ rO
      ⟨[], flat (List.zip (outs Wd r s w N (reRes Wd r w N fs gs)) (outs Wd r s w N (imRes Wd r w N fs gs)))⟩))
      (ringCost Wd r w s N) := by
  obtain ⟨τ', k, hx, hq, hk⟩ := runs_ringProd h
  subst hq
  exact (compile_correct (by decide) hx).consequence (fun _ h => h) (fun _ h => h) hk

/-- The step bound in the packed size alone. -/
theorem ringCost_le {Wd r w s N : ℕ} (hr : 1 ≤ r) (hWd : w + 1 ≤ Wd) (hws : w + s ≤ Wd + 1) (hN : N = Wd * r) :
    ringCost Wd r w s N ≤
      4 * costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) + 11000 * N + 250000 := by
  have hc := cost_le cA cB cC0 N
  have h1 : r * (Wd + w + s + 10) ≤ 3 * N + 10 * N := by
    have : r * (Wd + w + s + 10) ≤ r * (3 * Wd) + r * 10 := by
      rw [← Nat.mul_add]; exact Nat.mul_le_mul_left r (by omega)
    have hW : 1 ≤ Wd := by omega
    have e : r * (3 * Wd) = 3 * N := by rw [hN]; ring
    have f : r * 10 ≤ 10 * N := by rw [hN]; nlinarith
    omega
  unfold ringCost
  have e : 400 * r * (Wd + w + s + 10) = 400 * (r * (Wd + w + s + 10)) := by ring
  rw [e]
  nlinarith

/-- The ring product's contract: the output tape holds, for each coefficient, the real and
imaginary parts of the negacyclic product truncated toward zero by `s` bits, as `w`-bit words. -/
theorem ringProgram_spec {Wd r w s N : ℕ} {fs gs : List (List Bool × List Bool)} {τ : Fin 𝕌 → WTape}
    (h : RingSetup Wd r w s N fs gs τ) (Bd : ℤ) (hB0 : 0 ≤ Bd)
    (hf : ∀ odd, ∀ x ∈ coeffs odd fs, |x| ≤ Bd) (hg : ∀ odd, ∀ x ∈ coeffs odd gs, |x| ≤ Bd)
    (hBd : 2 * r * (Bd * Bd) < 2 ^ (Wd - 1)) :
    HoareTime ringProgram (· = enc τ) (· = enc (Function.update τ rO ⟨[], flat (ringOut r s w fs gs)⟩))
      (4 * costC cA cB cC0 * (N + 1) * (bitlen N + 1) * (bitlen (bitlen N ^ 3) + 1) + 11000 * N + 250000) := by
  have e := outs_eq h Bd hB0 hf hg hBd
  rw [← e]
  exact (ringProgram_hoare h).consequence (fun _ h => h) (fun _ h => h)
    (ringCost_le h.hr h.hWd h.hws h.hN)

end IntegerMultBounds.Schoenhage
