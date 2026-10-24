module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorScalarLayout

/-! Generate common canonical geometry, exact encoding widths and target width.
This shared prefix supplies descriptor and auxiliary operand generation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T Q A : ℕ} {P U : Type}

def canonicalScalarInputProgram (rg : Fin 46 → Fin T) : Pr P T Q A U :=
  .seq (canonicalProfileSetupProgram (rg ∘ canonicalDescriptorGeometrySlot))
    (routerTargetWidthGenerateProgram (rg ∘ canonicalDescriptorTargetSlot))

theorem canonicalScalarInput_exec (body : P → Pr P T Q A U)
    (rg : Fin 46 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (r : Fin (canonicalRouterStride n)) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r.val)
    (hblank : ∀ j : Fin 46, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 96*L*L+592*L+560 ∧
      Exec body (canonicalScalarInputProgram rg) (mk v S) m
        (mk v' { S with R := canonicalDescriptorScalarInputBank S.R rg L n r.val }) := by
  have hg := hrg.comp canonicalDescriptorGeometrySlot_injective
  have hgeometryBlank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 →
      S.R ((rg ∘ canonicalDescriptorGeometrySlot) j) = [] := by
    intro j h0 h9 h18
    apply hblank
    · exact fun h => h0 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
    · exact fun h => h9 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
    · exact fun h => h18 (Fin.ext (congrArg (fun k : Fin 46 => k.val) h))
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalProfileSetup_exec body (rg ∘ canonicalDescriptorGeometrySlot)
    hg L n r.val hn hlarge hdivisor r.isLt v S hdimension hresidue hgeometryBlank
  let C : Stacks T A := { S with R := canonicalProfileSetupBank S.R (rg ∘ canonicalDescriptorGeometrySlot) L n r.val }
  have keep (j : Fin 46) (hj : j ∉ canonicalProfileTargets canonicalDescriptorGeometrySlot) :
      C.R (rg j) = S.R (rg j) := by
    apply canonicalProfileSetupBank_keep
    simpa [canonicalProfileTargets, hrg.eq_iff] using hj
  have borrowed : C.R (rg 16) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [C, canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
      canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, canonicalProfileWidthSlot,
      canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot,
      canonicalDescriptorGeometrySlot, canonicalRouterStride, hrg.eq_iff]
  have targetBlank : ∀ j : Fin 9, j ≠ 0 → j ≠ 1 → j ≠ 8 →
      C.R ((rg ∘ canonicalDescriptorTargetSlot) j) = [] := by
    intro j h0 h1 h8
    have sep : canonicalDescriptorTargetSlot j ∉ canonicalProfileTargets canonicalDescriptorGeometrySlot ∧
        canonicalDescriptorTargetSlot j ≠ 0 ∧ canonicalDescriptorTargetSlot j ≠ 9 ∧ canonicalDescriptorTargetSlot j ≠ 18 := by
      fin_cases j <;> simp_all [canonicalDescriptorTargetSlot, canonicalProfileTargets, canonicalDescriptorGeometrySlot]
    exact (keep _ sep.1).trans (hblank _ sep.2.1 sep.2.2.1 sep.2.2.2)
  have hdecomp := routerGeometry_decomposition n (canonicalRouterStride n) (canonicalRouterGap n) hlarge
  obtain ⟨v₂, hu₂, hex₂⟩ := routerTargetWidthGenerate_exec body (rg ∘ canonicalDescriptorTargetSlot)
    (hrg.comp canonicalDescriptorTargetSlot_injective) L n (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    hn (by omega) v₁ C ((keep 0 (by decide)).trans hdimension) borrowed targetBlank
  exact ⟨v₂,m₁+(30*L+34),hu₂.trans hu₁,by nlinarith only [hm₁],Exec.seq hex₁ hex₂⟩

end IntegerMultBounds.MathlibTM2.Routing
