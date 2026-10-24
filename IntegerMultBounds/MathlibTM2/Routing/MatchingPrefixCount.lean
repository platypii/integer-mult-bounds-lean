module

public import IntegerMultBounds.MathlibTM2.Host.BinArithMul

/-! Generate the profile prefix byte count from binary row count, stride and
entry width. The intermediate slot count is erased; all compact inputs survive. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def matchingPrefixCountProgram (rg : Fin 11 → Fin T) : Pr P T Q A U :=
  .seq (bmul (rg 0) (rg 1) (rg 3) (rg 5) (rg 6) (rg 7) (rg 8) (rg 9) (rg 10))
    (.seq (bmul (rg 3) (rg 2) (rg 4) (rg 5) (rg 6) (rg 7) (rg 8) (rg 9) (rg 10)) (bclear (rg 3)))

def matchingPrefixCountCost (Ln Lk Le : ℕ) : ℕ :=
  (Ln * (12 * (Ln + Lk) + 20) + 16 * (Ln + Lk) + 24) +
    ((Ln + Lk) * (12 * (Ln + Lk + Le) + 20) + 16 * (Ln + Lk + Le) + 24) +
      2 * (Ln + Lk) + 2

theorem matchingPrefixCount_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (Ln Lk Le n K entryWidth : ℕ)
    (hn : n < 2 ^ Ln) (hk : K < 2 ^ Lk) (he : entryWidth < 2 ^ Le)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (rg 0) = binSyms Ln n) (hstride : S.R (rg 1) = binSyms Lk K)
    (hentry : S.R (rg 2) = binSyms Le entryWidth)
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ matchingPrefixCountCost Ln Lk Le ∧
      Exec body (matchingPrefixCountProgram rg) (mk v S) m
        (mk v' { S with R := (Function.update S.R (rg 4)
          (binSyms (Ln + Lk + Le) ((n * K) * entryWidth))) }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := bmul_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 3) (s := rg 5) (t := rg 6)
    (tx := rg 7) (ty := rg 8) (tz := rg 9) (cy := rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hn hk v S
    hrows hstride (hblank 3 (by decide) (by decide) (by decide) (by decide))
    (hblank 5 (by decide) (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide) (by decide))
    (hblank 7 (by decide) (by decide) (by decide) (by decide))
    (hblank 8 (by decide) (by decide) (by decide) (by decide))
    (hblank 9 (by decide) (by decide) (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 3) (binSyms (Ln + Lk) (n * K)) }
  have hproduct : n * K < 2 ^ (Ln + Lk) := by
    rw [pow_add]
    exact Nat.mul_lt_mul_of_lt_of_lt hn hk
  have keep (j : Fin 11) (hj : j ≠ 3) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := bmul_exec (body := body)
    (a := rg 3) (b := rg 2) (c := rg 4) (s := rg 5) (t := rg 6)
    (tx := rg 7) (ty := rg 8) (tz := rg 9) (cy := rg 10)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) hproduct he v₁ C
    (by simp [C]) ((keep 2 (by decide)).trans hentry)
    ((keep 4 (by decide)).trans (hblank 4 (by decide) (by decide) (by decide) (by decide)))
    ((keep 5 (by decide)).trans (hblank 5 (by decide) (by decide) (by decide) (by decide)))
    ((keep 6 (by decide)).trans (hblank 6 (by decide) (by decide) (by decide) (by decide)))
    ((keep 7 (by decide)).trans (hblank 7 (by decide) (by decide) (by decide) (by decide)))
    ((keep 8 (by decide)).trans (hblank 8 (by decide) (by decide) (by decide) (by decide)))
    ((keep 9 (by decide)).trans (hblank 9 (by decide) (by decide) (by decide) (by decide)))
  let D : Stacks T A := { C with R := Function.update C.R (rg 4) (binSyms (Ln + Lk + Le) ((n * K) * entryWidth)) }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 3) v₂ D
  have hlen : (D.R (rg 3)).length = Ln + Lk := by simp [D, C, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 3) [] } : Stacks T A) =
      { S with R := (Function.update S.R (rg 4) (binSyms (Ln + Lk + Le) ((n * K) * entryWidth))) } := by
    congr 1
    funext x
    by_cases hx : x = rg 3
    · subst x; simp [hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide) (by decide)]
    · by_cases hy : x = rg 4 <;> simp [D, C, hx, hy, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  refine ⟨v₃, m₁ + (m₂ + (2 * (Ln + Lk) + 2)), hu₃.trans (hu₂.trans hu₁), ?_, Exec.seq he₁ (Exec.seq he₂ he₃)⟩
  unfold matchingPrefixCountCost
  omega

end IntegerMultBounds.MathlibTM2.Routing
