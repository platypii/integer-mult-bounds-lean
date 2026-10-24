module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryWordWidth
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometryGenerate

/-! Common routing geometry from only three binary value inputs. The binary
word width is counted from the dimension tape and erased after use. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerGeometryWidthSlot : Fin 6 → Fin 17 := ![0,3,15,4,5,9]
theorem routerGeometryWidthSlot_injective : Function.Injective routerGeometryWidthSlot := by decide +kernel

def routerGeometryCompactProgram (rg : Fin 17 → Fin T) : Pr P T Q A U :=
  .seq (binaryWordWidthProgram (rg ∘ routerGeometryWidthSlot))
    (.seq (routerGeometryGenerateProgram rg) (bclear (rg 15)))

theorem routerGeometryCompact_exec (body : P → Pr P T Q A U)
    (rg : Fin 17 → Fin T) (hrg : Function.Injective rg) (L n K G : ℕ)
    (hn : n < 2 ^ L) (hK : 0 < K) (hKn : K ≤ n) (hdivisor : K + 3 * G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hstride : S.R (rg 1) = binSyms L K)
    (hgap : S.R (rg 2) = binSyms L G)
    (hblank : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 44 * L * L + 212 * L + 154 ∧
      Exec body (routerGeometryCompactProgram rg) (mk v S) m
        (mk v' { S with R := routerGeometryBank S.R rg L n K G }) := by
  have hwidthBlank : ∀ j : Fin 6, j ≠ 0 → j ≠ 5 → S.R ((rg ∘ routerGeometryWidthSlot) j) = [] := by
    intro j hj0 hj5
    fin_cases j <;> simp only [Function.comp_apply, routerGeometryWidthSlot, Fin.isValue] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := binaryWordWidth_exec body (rg ∘ routerGeometryWidthSlot)
    (hrg.comp routerGeometryWidthSlot_injective) L v S (by simp [routerGeometryWidthSlot, hdimension, length_binSyms]) hwidthBlank
  let C : Stacks T A := { S with R := Function.update S.R (rg 15) (binSyms L L) }
  have keep (j : Fin 17) (hj : j ≠ 15) : C.R (rg j) = S.R (rg j) := Function.update_of_ne (hrg.ne hj) _ _
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := routerGeometryGenerate_exec body rg hrg L L n K G
    (Nat.lt_two_pow_self (n := L)) hn hK hKn hdivisor v₁ C
    ((keep 0 (by decide)).trans hdimension) ((keep 1 (by decide)).trans hstride)
    ((keep 2 (by decide)).trans hgap) (by simp [C])
    (fun j hj0 hj1 hj2 hj9 hj15 => (keep j hj15).trans (hblank j hj0 hj1 hj2 hj9))
  let D : Stacks T A := { C with R := routerGeometryBank C.R rg L n K G }
  obtain ⟨v₃, hu₃, _, he₃⟩ := bclear_exec (body := body) (rg 15) v₂ D
  have hlen : (D.R (rg 15)).length = L := by simp [D, C, routerGeometryBank, hrg.eq_iff, length_binSyms]
  have hfinal : ({ D with R := Function.update D.R (rg 15) [] } : Stacks T A) =
      { S with R := routerGeometryBank S.R rg L n K G } := by
    congr 1
    funext x
    by_cases h15 : x = rg 15
    · subst x; simp [routerGeometryBank, hrg.eq_iff, hblank 15 (by decide) (by decide) (by decide) (by decide)]
    · by_cases h11 : x = rg 11 <;> by_cases h14 : x = rg 14 <;> by_cases h16 : x = rg 16 <;>
        simp [D, C, routerGeometryBank, h15, h11, h14, h16, hrg.eq_iff]
  rw [hlen, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (2 * L + 2)), hu₃.trans (hu₂.trans hu₁), by nlinarith only [hm₁, hm₂],
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
