module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Subtract live binary operands with natural-number saturation at zero.
This includes empty descriptor rows; both source words and all scratch restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySaturatingSubProgram (rg : Fin 7 → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg 0) (rg 1) (rg 2) (rg 3) (rg 4) (rg 5) (rg 6))
    (.cond (fun v => symBit (v.scan (rg 6)))
      (.seq (bclear (rg 2)) (bzero (rg 0) (rg 2) (rg 3))) (.act .done))

theorem binarySaturatingSub_exec (body : P → Pr P T Q A U)
    (rg : Fin 7 → Fin T) (hrg : Function.Injective rg) (L x y : ℕ)
    (hx : x < 2 ^ L) (hy : y < 2 ^ L) (v : HS T Q A U) (S : Stacks T A)
    (ha : S.R (rg 0) = binSyms L x) (hb : S.R (rg 1) = binSyms L y)
    (hblank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 14 * L + 15 ∧
      Exec body (binarySaturatingSubProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (x - y)) }) := by
  obtain ⟨v₁, hu₁, hborrow, _, hex₁⟩ := bsub_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 3) (ty := rg 4) (tz := rg 5) (cy := rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hx hy v S ha hb
    (hblank 3 (by decide) (by decide) (by decide))
    (hblank 4 (by decide) (by decide) (by decide)) (hblank 5 (by decide) (by decide) (by decide))
  rw [hblank 2 (by decide) (by decide) (by decide), List.append_nil] at hex₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L ((x + 2 ^ L - y) % 2 ^ L)) }
  by_cases hxy : x < y
  · obtain ⟨v₂, hu₂, _, hex₂⟩ := bclear_exec body (rg 2) v₁ C
    let D : Stacks T A := { C with R := Function.update C.R (rg 2) [] }
    obtain ⟨v₃, hu₃, hex₃⟩ := bzero_exec (body := body) (wR := rg 0) (c := rg 2) (t := rg 3)
      (by simp [List.nodup_cons, hrg.eq_iff]) v₂ D
      (by simp [D, C, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)])
    have hcLen : (C.R (rg 2)).length = L := by simp [C, length_binSyms]
    have hdSrc : D.R (rg 0) = binSyms L x := by simp [D, C, hrg.eq_iff, ha]
    have hdDst : D.R (rg 2) = [] := by simp [D]
    rw [hcLen] at hex₂
    rw [hdSrc, length_binSyms, hdDst, List.append_nil] at hex₃
    have hf : ({ D with R := Function.update D.R (rg 2) (binSyms L 0) } : Stacks T A) =
        { S with R := Function.update S.R (rg 2) (binSyms L (x - y)) } := by
      simp [D, C, Nat.sub_eq_zero_of_le (Nat.le_of_lt hxy)]
    rw [hf] at hex₃
    exact ⟨v₃, (8 * L + 8) + (((2 * L + 2) + (4 * L + 4)) + 1),
      hu₃.trans (hu₂.trans hu₁), by omega,
      Exec.seq hex₁ (Exec.cond_true (by simp [mk_var, hborrow, hxy]) (Exec.seq hex₂ hex₃))⟩
  · have hsub : (x + 2 ^ L - y) % 2 ^ L = x - y := by
      rw [show x + 2 ^ L - y = (x - y) + 2 ^ L by omega, Nat.add_mod_right,
        Nat.mod_eq_of_lt ((Nat.sub_le _ _).trans_lt hx)]
    rw [hsub] at hex₁
    exact ⟨v₁, (8 * L + 8) + (1 + 1), hu₁, by omega,
      Exec.seq hex₁ (Exec.cond_false (by simp [mk_var, hborrow, hxy]) (Exec.act (body := body) .done _))⟩

end IntegerMultBounds.MathlibTM2.Routing
