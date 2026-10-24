module

public import IntegerMultBounds.MathlibTM2.Routing.DescriptorLastRows
public import IntegerMultBounds.MathlibTM2.Routing.DescriptorSourceWidths
public import IntegerMultBounds.MathlibTM2.Routing.RepairDescriptorScalarPalette

/-! Complete the eleven-value shared descriptor palette. Five live geometric
operands are preserved; six derived values are generated with shared scratch. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def descriptorScalarLastSlot : Fin 9 → Fin 17 := ![5,6,11,7,8,12,13,14,16]
def descriptorScalarSourceSlot : Fin 10 → Fin 17 := ![6,5,11,12,9,10,13,14,15,16]
theorem descriptorScalarLastSlot_injective : Function.Injective descriptorScalarLastSlot := by decide +kernel
theorem descriptorScalarSourceSlot_injective : Function.Injective descriptorScalarSourceSlot := by decide +kernel

def descriptorScalarGenerateProgram (rg : Fin 17 → Fin T) : Pr P T Q A U :=
  .seq (descriptorLastRowsProgram (rg ∘ descriptorScalarLastSlot))
    (.seq (descriptorSourceWidthsProgram (rg ∘ descriptorScalarSourceSlot))
      (.seq (binarySuccessorProgram (rg 2) (rg 3) (rg 11) (rg 12) (rg 16))
        (bzero (rg 5) (rg 4) (rg 11))))

def descriptorScalarBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 17 → Fin T) (L : ℕ) (p : Par) :=
  Function.update (Function.update (Function.update (Function.update (Function.update (Function.update R
    (rg 7) (binSyms L (p.wy - 1))) (rg 8) (binSyms L (p.wc - 1)))
    (rg 9) (binSyms L (2 * p.wc + 1))) (rg 10) (binSyms L (p.wy + 2 * p.wc + 1)))
    (rg 3) (binSyms L (p.ρ + 1))) (rg 4) (binSyms L 0)

theorem descriptorScalarGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 17 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (p : Par)
    (hfit : p.wy + 2 * p.wc + 1 < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A)
    (hrows : S.R (rg 5) = binSyms L p.wy) (hborrowed : S.R (rg 6) = binSyms L p.wc)
    (hresidue : S.R (rg 2) = binSyms L p.ρ)
    (hblank : ∀ j : Fin 17, j ≠ 0 → j ≠ 1 → j ≠ 2 → j ≠ 5 → j ≠ 6 → j ≠ 16 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 94 * L + 104 ∧
      Exec body (descriptorScalarGenerateProgram rg) (mk v S) m
        (mk v' { S with R := descriptorScalarBank S.R rg L p }) := by
  have blank (j : Fin 17) (hj : j ∈ ([3,4,7,8,9,10,11,12,13,14,15] : List (Fin 17))) : S.R (rg j) = [] := by
    apply hblank
    all_goals intro h; subst j; simp at hj
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := descriptorLastRows_exec body (rg ∘ descriptorScalarLastSlot)
    (hrg.comp descriptorScalarLastSlot_injective) L p.wy p.wc (by omega) (by omega) (by omega)
    v S hrows hborrowed
    (by intro j h0 h1 h8; fin_cases j <;> simp [descriptorScalarLastSlot, blank] at h0 h1 h8 ⊢)
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 7)
    (binSyms L (p.wy - 1))) (rg 8) (binSyms L (p.wc - 1))) }
  obtain ⟨v₂, hu₂, hex₂⟩ := descriptorSourceWidths_exec body (rg ∘ descriptorScalarSourceSlot)
    (hrg.comp descriptorScalarSourceSlot_injective) L p.wy p.wc hfit v₁ C
    (by simpa [C, descriptorScalarSourceSlot, hrg.eq_iff] using hborrowed)
    (by simpa [C, descriptorScalarSourceSlot, hrg.eq_iff] using hrows)
    (by intro j h0 h1 h9; fin_cases j <;> simp [descriptorScalarSourceSlot, C, hrg.eq_iff, blank] at h0 h1 h9 ⊢)
  let D : Stacks T A := { C with R := (Function.update (Function.update C.R (rg 9)
    (binSyms L (2 * p.wc + 1))) (rg 10) (binSyms L (p.wy + 2 * p.wc + 1))) }
  obtain ⟨v₃, hu₃, hex₃⟩ := binarySuccessor_exec body (rg 2) (rg 3) (rg 11) (rg 12) (rg 16)
    (by simp [List.nodup_cons, hrg.eq_iff]) L p.ρ v₂ D
    (by simp [D, C, hrg.eq_iff, hresidue])
    (by simp [D, C, hrg.eq_iff, blank]) (by simp [D, C, hrg.eq_iff, blank]) (by simp [D, C, hrg.eq_iff, blank])
  let E : Stacks T A := { D with R := Function.update D.R (rg 3) (binSyms L (p.ρ + 1)) }
  obtain ⟨v₄, hu₄, hex₄⟩ := bzero_exec (body := body) (wR := rg 5) (c := rg 4) (t := rg 11)
    (by simp [List.nodup_cons, hrg.eq_iff]) v₃ E (by simp [E, D, C, hrg.eq_iff, blank])
  have he5 : E.R (rg 5) = binSyms L p.wy := by simp [E, D, C, hrg.eq_iff, hrows]
  have he4 : E.R (rg 4) = [] := by simp [E, D, C, hrg.eq_iff, blank]
  rw [he5, length_binSyms, he4, List.append_nil] at hex₄
  refine ⟨v₄, m₁ + ((42 * L + 48) + ((10 * L + 11) + (4 * L + 4))),
    hu₄.trans (hu₃.trans (hu₂.trans hu₁)), by omega, ?_⟩
  exact (Exec.seq hex₁ (Exec.seq hex₂ (Exec.seq hex₃ hex₄))).cast rfl rfl

def descriptorScalarPaletteSlot : Fin 11 → Fin 17 := Fin.castLE (by decide)

theorem descriptorScalarBank_palette (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 17 → Fin T) (hrg : Function.Injective rg) (L : ℕ) (p : Par)
    (hinput : ∀ j : Fin 11, j ∈ ([0,1,2,5,6] : List (Fin 11)) →
      R (rg (descriptorScalarPaletteSlot j)) = binSyms L (repairDescriptorScalarPalette p j))
    (j : Fin 11) :
    descriptorScalarBank R rg L p (rg (descriptorScalarPaletteSlot j)) =
      binSyms L (repairDescriptorScalarPalette p j) := by
  have h0 := hinput 0 (by decide)
  have h1 := hinput 1 (by decide)
  have h2 := hinput 2 (by decide)
  have h5 := hinput 5 (by decide)
  have h6 := hinput 6 (by decide)
  simp [descriptorScalarPaletteSlot, repairDescriptorScalarPalette] at h0 h1 h2 h5 h6
  fin_cases j <;> simp [descriptorScalarBank, descriptorScalarPaletteSlot,
    repairDescriptorScalarPalette, hrg.eq_iff, h0, h1, h2, h5, h6]

end IntegerMultBounds.MathlibTM2.Routing
