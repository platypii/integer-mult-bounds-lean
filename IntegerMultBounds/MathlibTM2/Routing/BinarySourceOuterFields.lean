module

public import IntegerMultBounds.MathlibTM2.Host.BinArithZip

/-! Low and high source regions use index zero and the coordinate minus their
region base. Both operands and arithmetic scratch are restored. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySourceOuterFieldsProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (bsub (rg 0) (rg 1) (rg 2) (rg 5) (rg 6) (rg 7) (rg 8))
    (bzero (rg 4) (rg 3) (rg 5))

theorem binarySourceOuterFields_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg)
    (L Li q base : ℕ) (hq : q < 2 ^ L) (hbase : base ≤ q)
    (v : HS T Q A U) (S : Stacks T A)
    (hqInput : S.R (rg 0) = binSyms L q) (hbaseInput : S.R (rg 1) = binSyms L base)
    (hwidthInput : (S.R (rg 4)).length = Li)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 4 → j ≠ 8 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U), v'.user = v.user ∧
      Exec body (binarySourceOuterFieldsProgram rg) (mk v S) (8 * L + 4 * Li + 12)
        (mk v' { S with R := Function.update (Function.update S.R (rg 2) (binSyms L (q - base))) (rg 3) (binSyms Li 0) }) := by
  obtain ⟨v₁, hu₁, _, _, hx₁⟩ := bsub_exec body
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    hq (by omega : base < 2 ^ L) v S hqInput hbaseInput
    (hblank 5 (by decide) (by decide) (by decide) (by decide))
    (hblank 6 (by decide) (by decide) (by decide) (by decide))
    (hblank 7 (by decide) (by decide) (by decide) (by decide))
  have hm : (q + 2 ^ L - base) % 2 ^ L = q - base := by
    rw [show q + 2 ^ L - base = (q - base) + 2 ^ L by omega, Nat.add_mod_right]
    exact Nat.mod_eq_of_lt (by omega)
  rw [hm, hblank 2 (by decide) (by decide) (by decide) (by decide), List.append_nil] at hx₁
  let G : Stacks T A := { S with R := Function.update S.R (rg 2) (binSyms L (q - base)) }
  obtain ⟨v₂, hu₂, hx₂⟩ := bzero_exec body (wR := rg 4) (c := rg 3) (t := rg 5)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₁ G
    (by simp [G, hrg.eq_iff, hblank 5 (by decide) (by decide) (by decide) (by decide)])
  have hw : (G.R (rg 4)).length = Li := by simp [G, hrg.eq_iff, hwidthInput]
  have hi : G.R (rg 3) = [] := by simp [G, hrg.eq_iff, hblank 3 (by decide) (by decide) (by decide) (by decide)]
  rw [hw, hi, List.append_nil] at hx₂
  exact ⟨v₂, hu₂.trans hu₁, Exec.cast (Exec.seq hx₁ hx₂) (by omega) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
