module

public import IntegerMultBounds.MathlibTM2.Routing.BinaryPrefixExtract

/-! Copy a fixed-width low part using a compact binary width operand. This
reuses the executed prefix extractor; the wide source and all scratch restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

theorem binaryLowCopy_exec (body : P → Pr P T Q A U)
    (rg : Fin 8 → Fin T) (hrg : Function.Injective rg) (M L e x : ℕ) (hL : L < 2 ^ M)
    (v : HS T Q A U) (S : Stacks T A)
    (hwidth : S.R (rg 0) = binSyms M L) (hinput : S.R (rg 5) = binSyms (L + e) x)
    (hblank : ∀ j : Fin 8, j = 1 ∨ j = 2 ∨ j = 3 ∨ j = 4 ∨ j = 7 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ binaryPrefixExtractCost M L ∧
      Exec body (binaryPrefixExtractProgram rg) (mk v S) m
        (mk v' { S with R := Function.update S.R (rg 6) (binSyms L x ++ S.R (rg 6)) }) := by
  obtain ⟨v', m, hu, hm, he⟩ := binaryPrefixExtract_exec body rg hrg M
    (binSyms L x) (binSyms e (x / 2 ^ L)) (by simpa only [length_binSyms] using hL) v S
    (by simpa only [length_binSyms] using hwidth)
    (by rw [hinput, binSyms_append]) hblank
  rw [length_binSyms] at hm
  exact ⟨v', m, hu, hm, he⟩

end IntegerMultBounds.MathlibTM2.Routing
