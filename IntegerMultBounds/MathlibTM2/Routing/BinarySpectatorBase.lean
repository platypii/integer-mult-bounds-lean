module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Compute the spectator-region base y + 2*c from live row counts. Both
operands and every borrowed arithmetic tape are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySpectatorBaseProgram (rg : Fin 8 → Fin T) : Pr P T Q A U :=
  .seq (badd (rg 0) (rg 1) (rg 2) (rg 4) (rg 5) (rg 6) (rg 7))
    (.seq (badd (rg 2) (rg 1) (rg 3) (rg 4) (rg 5) (rg 6) (rg 7)) (bclear (rg 2)))

theorem binarySpectatorBase_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg)
    (L y c : ℕ) (hfit : y + 2 * c < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hy : S.R (rg 0) = binSyms L y) (hc : S.R (rg 1) = binSyms L c)
    (hblank : ∀ j : Fin 8, j ≠ 0 → j ≠ 1 → j ≠ 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (binarySpectatorBaseProgram rg) (mk v S) (18 * L + 18)
        (mk v' { S with R := Function.update S.R (rg 3) (binSyms L (y + 2 * c)) }) := by
  obtain ⟨v₁, hu₁, _, _, hx₁⟩ := badd_exec body
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 4) (ty := rg 5) (tz := rg 6) (cy := rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : y < 2 ^ L) (by omega : c < 2 ^ L) v S hy hc
    (hblank 4 (by decide) (by decide) (by decide))
    (hblank 5 (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide))
  rw [Nat.mod_eq_of_lt (by omega : y + c < 2 ^ L), hblank 2 (by decide) (by decide) (by decide), List.append_nil] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (y + c)) }
  obtain ⟨v₂, hu₂, _, _, hx₂⟩ := badd_exec body
    (a := rg 2) (b := rg 1) (c := rg 3) (tx := rg 4) (ty := rg 5) (tz := rg 6) (cy := rg 7)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : y + c < 2 ^ L) (by omega : c < 2 ^ L) v₁ G
    (by simp [G]) (by simp [G, hrg.eq_iff, hc])
    (by simp [G, hrg.eq_iff, hblank 4 (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hblank 6 (by decide) (by decide) (by decide)])
  have heq : y + c + c = y + 2 * c := by omega
  have hd : G.R (rg 3) = [] := by simp [G, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide)]
  rw [heq, Nat.mod_eq_of_lt hfit, hd, List.append_nil] at hx₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 3) (binSyms L (y + 2 * c)) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 2) v₂ H
  have ht : H.R (rg 2) = binSyms L (y + c) := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 2) [] = Function.update S.R (rg 3) (binSyms L (y + 2 * c)) := by
    funext j
    by_cases h2 : j = rg 2
    · subst j; simp [hrg.eq_iff, hblank 2 (by decide) (by decide) (by decide)]
    · by_cases h3 : j = rg 3
      · subst j; simp [H, G, hrg.eq_iff]
      · simp [H, G, h2, h3]
  rw [hf, ht, length_binSyms] at hx₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁),
    Exec.cast (Exec.seq hx₁ (Exec.seq hx₂ hx₃)) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
