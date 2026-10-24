module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryFixedScale

/-! Generate the fixed-width reservoir multiples from a single binary width. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def reservoirScalarMultiplesProgram (rg : Fin 9 → Fin T) : Pr P T Q A U :=
  .seq (binaryDoubleCopyProgram (rg 0) (rg 1) (rg 5) (rg 6))
    (.seq (badd (rg 0) (rg 1) (rg 2) (rg 5) (rg 6) (rg 7) (rg 8))
      (binaryDoubleCopyProgram (rg 2) (rg 3) (rg 5) (rg 6)))

theorem reservoirScalarMultiples_exec (body : P → Pr P T Q A U)
    (rg : Fin 9 → Fin T) (hrg : Function.Injective rg) (L H : ℕ) (hfit : 6 * H < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L H)
    (hblank : ∀ j : Fin 9, j ≠ 0 → j ≠ 8 → S.R (rg j) = []) :
    ∃ v', v'.user = v.user ∧
      Exec body (reservoirScalarMultiplesProgram rg) (mk v S) (28 * L + 36)
        (mk v' { S with R := (Function.update (Function.update (Function.update S.R
          (rg 1) (binSyms L (2 * H))) (rg 2) (binSyms L (3 * H))) (rg 3) (binSyms L (6 * H))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := binaryDoubleCopy_exec body (rg 0) (rg 1) (rg 5) (rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) L H v S hsrc
    (hblank 1 (by decide) (by decide)) (hblank 5 (by decide) (by decide)) (hblank 6 (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (binSyms L (2 * H)) }
  obtain ⟨v₂, hu₂, _, _, he₂⟩ := badd_exec (body := body)
    (a := rg 0) (b := rg 1) (c := rg 2) (tx := rg 5) (ty := rg 6) (tz := rg 7) (cy := rg 8)
    (by simp [List.nodup_cons, hrg.eq_iff]) (hrg.ne (by decide)) (hrg.ne (by decide))
    (by omega : H < 2 ^ L) (by omega : 2 * H < 2 ^ L) v₁ C
    (by simp [C, hrg.eq_iff, hsrc]) (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 6 (by decide) (by decide)])
    (by simp [C, hrg.eq_iff, hblank 7 (by decide) (by decide)])
  have hsum : H + 2 * H = 3 * H := by omega
  have htriple : 3 * H < 2 ^ L := by omega
  have hc2 : C.R (rg 2) = [] := by simp [C, hrg.eq_iff, hblank 2 (by decide) (by decide)]
  rw [hsum, Nat.mod_eq_of_lt htriple, hc2, List.append_nil] at he₂
  let D : Stacks T A := { C with R := Function.update C.R (rg 2) (binSyms L (3 * H)) }
  obtain ⟨v₃, hu₃, he₃⟩ := binaryDoubleCopy_exec body (rg 2) (rg 3) (rg 5) (rg 6)
    (by simp [List.nodup_cons, hrg.eq_iff]) L (3 * H) v₂ D (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 5 (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 6 (by decide) (by decide)])
  have hscale : 2 * (3 * H) = 6 * H := by omega
  rw [hscale] at he₃
  exact ⟨v₃, hu₃.trans (hu₂.trans hu₁), (Exec.seq he₁ (Exec.seq he₂ he₃)).cast (by ring) rfl⟩

end IntegerMultBounds.MathlibTM2.Routing
