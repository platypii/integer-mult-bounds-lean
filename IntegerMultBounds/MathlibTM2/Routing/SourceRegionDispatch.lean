module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Classify a physical Y coordinate against two live region boundaries.
Comparisons preserve every tape; a fixed branch program handles each region. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def sourceRegionIndex (q low high : ℕ) : Fin 3 :=
  if q < low then 0 else if q < high then 1 else 2

def sourceRegionDispatchProgram (rg : Fin 7 → Fin T) (branch : Fin 3 → Pr P T Q A U) : Pr P T Q A U :=
  .seq (blt (rg 0) (rg 1) (rg 3) (rg 4) (rg 5) (rg 6))
    (.cond (fun v => symBit (v.scan (rg 6))) (branch 0)
      (.seq (blt (rg 0) (rg 2) (rg 3) (rg 4) (rg 5) (rg 6))
        (.cond (fun v => symBit (v.scan (rg 6))) (branch 1) (branch 2))))

theorem sourceRegionDispatch_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (branch : Fin 3 → Pr P T Q A U)
    (L q low high C : ℕ) (hq : q < 2 ^ L) (hlow : low < 2 ^ L) (hhigh : high < 2 ^ L)
    (v : HS T Q A U) (S S' : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hlowInput : S.R (rg 1) = binSyms L low)
    (hhighInput : S.R (rg 2) = binSyms L high)
    (hblank : ∀ j : Fin 7, j = 3 ∨ j = 4 ∨ j = 5 → S.R (rg j) = [])
    (hbranch : ∀ u : HS T Q A U, ∃ (u' : HS T Q A U) (steps : ℕ), u'.user = u.user ∧ steps ≤ C ∧
      Exec body (branch (sourceRegionIndex q low high)) (mk u S) steps (mk u' S')) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 16 * L + 18 + C ∧
      Exec body (sourceRegionDispatchProgram rg branch) (mk v S) steps (mk v' S') := by
  obtain ⟨v₁, hu₁, hs₁, _, hx₁⟩ := blt_exec body
    (a := rg 0) (b := rg 1) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq hlow v S hqInput hlowInput (hblank 3 (by simp)) (hblank 4 (by simp)) (hblank 5 (by simp))
  by_cases hlo : q < low
  · obtain ⟨v₂, m₂, hu₂, hm₂, hx₂⟩ := hbranch v₁
    simp only [sourceRegionIndex, ite_eq_left hlo] at hx₂
    refine ⟨v₂, (8 * L + 8) + (m₂ + 1), hu₂.trans hu₁, by omega, ?_⟩
    exact Exec.seq hx₁ (Exec.cond_true (by simp [mk_var, hs₁, hlo]) hx₂)
  · obtain ⟨v₂, hu₂, hs₂, _, hx₂⟩ := blt_exec body
      (a := rg 0) (b := rg 2) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
      (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
      hq hhigh v₁ S hqInput hhighInput (hblank 3 (by simp)) (hblank 4 (by simp)) (hblank 5 (by simp))
    obtain ⟨v₃, m₃, hu₃, hm₃, hx₃⟩ := hbranch v₂
    by_cases hhi : q < high
    · simp only [sourceRegionIndex, ite_eq_right hlo, ite_eq_left hhi] at hx₃
      refine ⟨v₃, (8 * L + 8) + (((8 * L + 8) + (m₃ + 1)) + 1), hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
      exact Exec.seq hx₁ (Exec.cond_false (by simp [mk_var, hs₁, hlo])
        (Exec.seq hx₂ (Exec.cond_true (by simp [mk_var, hs₂, hhi]) hx₃)))
    · simp only [sourceRegionIndex, ite_eq_right hlo, ite_eq_right hhi] at hx₃
      refine ⟨v₃, (8 * L + 8) + (((8 * L + 8) + (m₃ + 1)) + 1), hu₃.trans (hu₂.trans hu₁), by omega, ?_⟩
      exact Exec.seq hx₁ (Exec.cond_false (by simp [mk_var, hs₁, hlo])
        (Exec.seq hx₂ (Exec.cond_false (by simp [mk_var, hs₂, hhi]) hx₃)))

end IntegerMultBounds.MathlibTM2.Routing
