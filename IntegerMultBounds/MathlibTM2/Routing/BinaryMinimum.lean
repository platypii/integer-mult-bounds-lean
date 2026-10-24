module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Update an orbit minimum from a live binary coordinate, preserving that
coordinate and all comparison/copy scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryMinimumProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (blt (rg 0) (rg 1) (rg 2) (rg 3) (rg 4) (rg 5))
    (.cond (fun v => symBit (v.scan (rg 5)))
      (.seq (bclear (rg 1)) (bcopy (rg 0) (rg 1) (rg 2) (rg 3))) (.act .done))

theorem binaryMinimum_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L x y : ℕ)
    (hx : x < 2 ^ L) (hy : y < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (hquery : S.R (rg 0) = binSyms L x) (hbest : S.R (rg 1) = binSyms L y)
    (hblank : ∀ j : Fin 6, j = 2 ∨ j = 3 ∨ j = 4 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧ steps ≤ 16 * L + 17 ∧
      Exec body (binaryMinimumProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 1) (binSyms L (min x y)) }) := by
  obtain ⟨v₁, hu₁, hscan, _, he₁⟩ := blt_exec (body := body)
    (a := rg 0) (b := rg 1) (tx := rg 2) (ty := rg 3) (tz := rg 4) (cy := rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hx hy v S hquery hbest (hblank 2 (by simp)) (hblank 3 (by simp)) (hblank 4 (by simp))
  by_cases h : x < y
  · obtain ⟨v₂, hu₂, _, he₂⟩ := bclear_exec (body := body) (rg 1) v₁ S
    rw [hbest, length_binSyms] at he₂
    let C : Stacks T A := { S with R := Function.update S.R (rg 1) [] }
    obtain ⟨v₃, hu₃, he₃⟩ := bcopy_exec (body := body)
      (a := rg 0) (c := rg 1) (t₁ := rg 2) (t₂ := rg 3)
      (by simp [List.nodup_cons, hrg.eq_iff]) v₂ C
      (by simp [C, hrg.eq_iff, hblank 2 (by simp)])
      (by simp [C, hrg.eq_iff, hblank 3 (by simp)])
    have hq : C.R (rg 0) = binSyms L x := by simp [C, hrg.eq_iff, hquery]
    rw [hq, length_binSyms] at he₃
    have hfinal : ({ C with R := Function.update C.R (rg 1) (binSyms L x ++ C.R (rg 1)) } : Stacks T A) =
        { S with R := Function.update S.R (rg 1) (binSyms L (min x y)) } := by
      simp [C, Nat.min_eq_left (Nat.le_of_lt h)]
    rw [hfinal] at he₃
    exact ⟨v₃, (8 * L + 8) + ((2 * L + 2) + (6 * L + 6) + 1),
      hu₃.trans (hu₂.trans hu₁), by omega,
      Exec.seq he₁ (Exec.cond_true (by simp [mk_var, hscan, h]) (Exec.seq he₂ he₃))⟩
  · have hstate : ({ S with R := Function.update S.R (rg 1) (binSyms L (min x y)) } : Stacks T A) = S := by
      rw [Nat.min_eq_right (Nat.le_of_not_gt h), ← hbest, Function.update_eq_self]
    refine ⟨v₁, (8 * L + 8) + (1 + 1), hu₁, by omega, ?_⟩
    rw [hstate]
    exact Exec.seq he₁ (Exec.cond_false (by simp [mk_var, hscan, h]) (Exec.act (body := body) .done (mk v₁ S)))

end IntegerMultBounds.MathlibTM2.Routing
