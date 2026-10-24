module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryCeilLogData
public import IntegerMultBounds.MathlibTM2.Routing.BinaryCanonicalExec
public import IntegerMultBounds.MathlibTM2.Host.BinArith

/-! Compute the exact canonical scalar width `clog 2 (n+1)` from a preserved
binary operand, including zero. Only the width output changes. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def binaryScalarWidthProgram (rg : Fin 6 → Fin T) : Pr P T Q A U :=
  .seq (bcopy (rg 0) (rg 1) (rg 3) (rg 4))
    (.seq (binaryCanonicalProgram (rg 1) (rg 3))
      (.seq (toBinary (rg 1) (rg 0) (rg 2) (rg 3) (rg 4) (rg 5)) (bclear (rg 1))))

theorem binaryScalarWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 6 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) (hn : n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 4 * L * L + 26 * L + 22 ∧
      Exec body (binaryScalarWidthProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 2) (binSyms L (Nat.clog 2 (n + 1))) }) := by
  obtain ⟨v₁, hu₁, he₁⟩ := bcopy_exec (body := body) (a := rg 0) (c := rg 1) (t₁ := rg 3) (t₂ := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) v S (hblank 3 (by decide) (by decide)) (hblank 4 (by decide) (by decide))
  rw [hsrc, hblank 1 (by decide) (by decide), List.append_nil, length_binSyms] at he₁
  let C : Stacks T A := { S with R := Function.update S.R (rg 1) (binSyms L n) }
  obtain ⟨bs, v₂, hc, hv, hl, hu₂, he₂⟩ := binaryCanonical_exec body (rg 1) (rg 3) (hrg.ne (by decide))
    L n hn v₁ C (by simp [C]) (by simp [C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
  have hlength : bs.length = Nat.clog 2 (n + 1) := by rw [canonicalBinary_length_clog bs hc, hv]
  let D : Stacks T A := { C with R := Function.update C.R (rg 1) (bs.map bitSymbol) }
  obtain ⟨v₃, m₃, hu₃, hm₃, he₃⟩ := toBinary_exec (body := body)
    (u := rg 1) (wR := rg 0) (c := rg 2) (t := rg 3) (tmp := rg 4)
    (by simp [List.nodup_cons, hrg.eq_iff]) (rg 5) v₂ D
    (by simp [D, C, hrg.eq_iff, hblank 2 (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 3 (by decide) (by decide)])
    (by simp [D, C, hrg.eq_iff, hblank 4 (by decide) (by decide)])
  have hd0 : (D.R (rg 0)).length = L := by simp [D, C, hrg.eq_iff, hsrc, length_binSyms]
  have hd1 : (D.R (rg 1)).length = bs.length := by simp [D]
  rw [hd0, hd1] at hm₃ he₃
  let E : Stacks T A := { D with R := Function.update D.R (rg 2) (binSyms L bs.length) }
  obtain ⟨v₄, hu₄, _, he₄⟩ := bclear_exec (body := body) (rg 1) v₃ E
  have hlen : (E.R (rg 1)).length = bs.length := by simp [E, D, hrg.eq_iff]
  have hfinal : ({ E with R := Function.update E.R (rg 1) [] } : Stacks T A) =
      { S with R := Function.update S.R (rg 2) (binSyms L (Nat.clog 2 (n + 1))) } := by
    congr 1
    funext x
    by_cases h1 : x = rg 1
    · subst x; simp [hrg.eq_iff, hblank 1 (by decide) (by decide)]
    · by_cases h2 : x = rg 2 <;> simp [E, D, C, h1, h2, hrg.eq_iff, hlength]
  rw [hlen, hfinal] at he₄
  refine ⟨v₄, (6 * L + 6) + ((4 * L + 6) + (m₃ + (2 * bs.length + 2))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), ?_, Exec.seq he₁ (Exec.seq he₂ (Exec.seq he₃ he₄))⟩
  nlinarith only [hm₃, Nat.mul_le_mul_right (4 * L + 12) hl]

end IntegerMultBounds.MathlibTM2.Routing
