module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLogData
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec
public import IntegerMultBounds.MathlibTM2.Routing.PaddedCopy

/-! Compute `clog 2 (n+2)` from a preserved padded binary dimension. Increment
in one extra bit, normalize, count the canonical bits, then erase that temporary. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryCeilLogProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (paddedCopy (rg 0) (rg 1) (rg 3) (rg 4))
    (.seq (countIter (rg 1) (rg 3) (rg 5))
      (.seq (binaryCanonicalProgram (rg 1) (rg 3))
        (.seq (toBinary (rg 1) (rg 0) (rg 2) (rg 3) (rg 4) (rg 5)) (bclear (rg 1)))))

theorem binaryCeilLog_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 34 * L + 48 ∧
      Exec body (binaryCeilLogProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (Nat.clog 2 (n + 2))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := paddedCopy_exec body (src := rg 0) (dst := rg 1) (tmp := rg 3) (ctmp := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) L n hn v S hsrc
    (hblank 1 (by decide) (by decide)) (hblank 3 (by decide) (by decide)) (hblank 4 (by decide) (by decide))
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (binSyms (L + 1) n) }
  obtain ⟨v₂, hu₂, he₂⟩ := countIter_exec body (c := rg 1) (tmp := rg 3) (W := L + 1) (j := n)
    (hrg.ne (by decide)) (rg 5) v₁ C (by simp [C])
    (by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
  let D : Stacks T A := { C with R := Function.update C.R (rg 1) (binSyms (L + 1) (n + 1)) }
  have hnext : n + 1 < 2 ^ (L + 1) := by
    rw [pow_succ]
    have := Nat.two_pow_pos L
    omega
  obtain ⟨bs, v₃, hc, hv, hl, hu₃, he₃⟩ := binaryCanonical_exec body (rg 1) (rg 3) (hrg.ne (by decide))
    (L + 1) (n + 1) hnext v₂ D (by simp [D])
    (by simp [D, C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
  have hlength : bs.length = Nat.clog 2 (n + 2) := by
    rw [canonicalBinary_length_clog bs hc, hv]
  let E : Stacks T A := { D with R := Function.update D.R (rg 1) (bs.map bitSymbol) }
  obtain ⟨v₄, m₄, hu₄, hm₄, he₄⟩ := toBinary_exec (body := body)
    (u := rg 1) (wR := rg 0) (c := rg 2) (t := rg 3) (tmp := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) (rg 5) v₃ E
    (by simp [E, D, C, hrg.eq_iff, hblank 2 (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [E, D, C, hrg.eq_iff, hblank 4 (by decide) (by decide)])
  have he0 : (E.R (rg 0)).length = L := by simp [E, D, C, hrg.eq_iff, hsrc, length_binSyms]
  have he1 : (E.R (rg 1)).length = bs.length := by simp [E]
  rw [he0, he1] at hm₄ he₄
  let F : Stacks T A := { E with R := Function.update E.R (rg 2) (binSyms L bs.length) }
  obtain ⟨v₅, hu₅, _, he₅⟩ := bclear_exec (body := body) (rg 1) v₄ F
  have hflen : (F.R (rg 1)).length = bs.length := by simp [F, E, hrg.eq_iff]
  have hfinal : ({ F with R := Function.update F.R (rg 1) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L (Nat.clog 2 (n + 2))) } := by
    congr 1
    funext x
    by_cases h1 : x = rg 1
    · subst x; simp [hrg.eq_iff, hblank 1 (by decide) (by decide)]
    · by_cases h2 : x = rg 2 <;> simp [F, E, D, C, h1, h2, hrg.eq_iff, hlength]
  rw [hflen, hfinal] at he₅
  refine ⟨v₅, (1 + (6 * L + 6)) + ((4 * (L + 1) + 5) + ((4 * (L + 1) + 6) + (m₄ + (2 * bs.length + 2)))),
    hu₅.trans (hu₄.trans (hu₃.trans (hu₂.trans hu₁))), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ (Exec.seq he₄ he₅)))⟩
  nlinarith only [hm₄, Nat.mul_le_mul_right (4 * L + 12) hl]

end IntegerMultBounds.MathlibTM2.Routing
