module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryProductLowCopy
public import IntegerMultBounds.MathlibTM2.Routing.RouterGeometry

/-! Multiply the generated digit count by the gap and export the fixed-width
borrowed span. The wide multiplication result is erased. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def routerBorrowedWidthProgram (rg : Fin 11 → Fin T) : Pr P T Q A U :=
  binaryProductLowCopyProgram rg

theorem routerBorrowedWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 11 → Fin T) (hrg : Function.Injective rg) (M L n K G : ℕ)
    (hL : L < 2 ^ M) (hdigits : routerDigits n K G < 2 ^ L) (hG : G < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hcount : S.R (rg 0) = binSyms L (routerDigits n K G)) (hgap : S.R (rg 1) = binSyms L G)
    (hwidth : S.R (rg 2) = binSyms M L)
    (hblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 10 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ L * (24 * L + 20) + 50 * L + 44 + M * (4 * L + 11) ∧
      Exec body (routerBorrowedWidthProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 8) (binSyms L (routerBorrowed n K G)) }) := by
  simpa only [routerBorrowedWidthProgram, routerBorrowed] using
    binaryProductLowCopy_exec body rg hrg M L (routerDigits n K G) G hL hdigits hG v S
      hcount hgap hwidth hblank

end IntegerMultBounds.MathlibTM2.Routing
