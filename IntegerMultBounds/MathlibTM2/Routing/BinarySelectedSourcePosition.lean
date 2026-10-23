module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryAffinePosition

/-! Compute a selected source address from index, stride, region base and local
offset. All operands and arithmetic scratch are restored; only the address grows. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binarySelectedSourcePositionProgram (rg : Fin 13 → Fin T) : Pr P T Q A U :=
  .seq (binaryAffinePositionProgram (rg 0) (rg 1) (rg 6) (rg 2) (rg 4)
      (rg 7) (rg 8) (rg 9) (rg 10) (rg 11) (rg 12))
    (.seq (badd (rg 4) (rg 3) (rg 5) (rg 9) (rg 10) (rg 11) (rg 12)) (bclear (rg 4)))

theorem binarySelectedSourcePosition_exec (body : P → Pr P T Q A U)
    (rg : Fin 13 → Fin T) (hrg : Function.Injective rg)
    (Li Lk i k b r : ℕ) (hi : i < 2 ^ Li) (hk : k < 2 ^ Lk)
    (hfit : i * k + b + r < 2 ^ (Li + Lk))
    (v : HS T Q A U) (S : Stacks T A)
    (hindex : S.R (rg 0) = binSyms Li i) (hstride : S.R (rg 1) = binSyms Lk k)
    (hbase : S.R (rg 2) = binSyms (Li + Lk) b) (hlocal : S.R (rg 3) = binSyms (Li + Lk) r)
    (hblank : ∀ j : Fin 13, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 3 → j ≠ 5 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (steps : ℕ), v'.user = v.user ∧
      steps ≤ Li * (12 * (Li + Lk) + 20) + 36 * (Li + Lk) + 44 ∧
      Exec body (binarySelectedSourcePositionProgram rg) (mk v S) steps
        (mk v' { S with R := Function.update S.R (rg 5) (binSyms (Li + Lk) (i * k + b + r) ++ S.R (rg 5)) }) := by
  have hb (j : Fin 13) (h0 : j ≠ 0) (h1 : j ≠ 1) (h2 : j ≠ 2) (h3 : j ≠ 3) (h5 : j ≠ 5) :=
    hblank j h0 h1 h2 h3 h5
  obtain ⟨v₁, m₁, hu₁, hm₁, hx₁⟩ := binaryAffinePosition_exec body
    (rg 0) (rg 1) (rg 6) (rg 2) (rg 4) (rg 7) (rg 8) (rg 9) (rg 10) (rg 11) (rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide)) (hrg.ne (by decide))
    Li Lk i k b hi hk (by omega) v S hindex hstride hbase
    (hb 6 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 4 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 7 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 8 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 9 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 10 (by decide) (by decide) (by decide) (by decide) (by decide))
    (hb 11 (by decide) (by decide) (by decide) (by decide) (by decide))
  let G : Stacks T A := { S with R := Function.update S.R (rg 4) (binSyms (Li + Lk) (i * k + b)) }
  obtain ⟨v₂, hu₂, _, _, hx₂⟩ := badd_exec body
    (a := rg 4) (b := rg 3) (c := rg 5) (tx := rg 9) (ty := rg 10) (tz := rg 11) (cy := rg 12)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : i * k + b < 2 ^ (Li + Lk)) (by omega : r < 2 ^ (Li + Lk)) v₁ G
    (by simp [G]) (by simp [G, hrg.eq_iff, hlocal])
    (by simp [G, hrg.eq_iff, hb 9 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 10 (by decide) (by decide) (by decide) (by decide) (by decide)])
    (by simp [G, hrg.eq_iff, hb 11 (by decide) (by decide) (by decide) (by decide) (by decide)])
  rw [Nat.mod_eq_of_lt hfit] at hx₂
  let H : Stacks T A := { G with R := Function.update G.R (rg 5) (binSyms (Li + Lk) (i * k + b + r) ++ G.R (rg 5)) }
  obtain ⟨v₃, hu₃, _, hx₃⟩ := bclear_exec body (rg 4) v₂ H
  have hp : H.R (rg 4) = binSyms (Li + Lk) (i * k + b) := by simp [H, G, hrg.eq_iff]
  have hf : Function.update H.R (rg 4) [] = Function.update S.R (rg 5)
      (binSyms (Li + Lk) (i * k + b + r) ++ S.R (rg 5)) := by
    funext j
    by_cases hj : j = rg 4
    · subst j; simp [hrg.eq_iff, hb 4 (by decide) (by decide) (by decide) (by decide) (by decide)]
    · by_cases hd : j = rg 5
      · subst j; simp [H, G, hrg.eq_iff]
      · simp [H, G, Function.update_apply, hj, hd]
  rw [hf, hp, length_binSyms] at hx₃
  exact ⟨v₃, m₁ + ((8 * (Li + Lk) + 8) + (2 * (Li + Lk) + 2)),
    hu₃.trans (hu₂.trans hu₁), by omega, Exec.seq hx₁ (Exec.seq hx₂ hx₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
