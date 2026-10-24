module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalResidueGeometry
public import IntegerMultBounds.MathlibTM2.Routing.CanonicalDescriptorWidthsGenerate

/-! Canonical geometry and exact descriptor widths share dimension and carry
inputs. The combined setup starts with only dimension and residue populated. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalProfileGeometrySlot : Fin 20 → Fin 28 := Fin.castLE (by decide)
def canonicalProfileWidthSlot : Fin 11 → Fin 28 := ![0,16,20,21,22,23,24,9,25,26,27]
theorem canonicalProfileGeometrySlot_injective : Function.Injective canonicalProfileGeometrySlot := by decide +kernel
theorem canonicalProfileWidthSlot_injective : Function.Injective canonicalProfileWidthSlot := by decide +kernel

def canonicalProfileSetupProgram (rg : Fin 28 → Fin T) : Pr P T Q A U :=
  .seq (canonicalResidueGeometryProgram (rg ∘ canonicalProfileGeometrySlot))
    (canonicalDescriptorWidthsProgram (rg ∘ canonicalProfileWidthSlot))

def canonicalProfileSetupBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T)
    (L n r : ℕ) : Fin T → List (Fin (A + 4)) :=
  canonicalDescriptorWidthsBank
    (canonicalResidueGeometryBank R (rg ∘ canonicalProfileGeometrySlot) L n r)
    (rg ∘ canonicalProfileWidthSlot) L n
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))

theorem canonicalProfileSetup_exec (body : P → Pr P T Q A U)
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (hr : r < canonicalRouterStride n) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r)
    (hblank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 96 * L * L + 562 * L + 526 ∧
      Exec body (canonicalProfileSetupProgram rg) (mk v S) m
        (mk v' { S with R := canonicalProfileSetupBank S.R rg L n r }) := by
  let geo := rg ∘ canonicalProfileGeometrySlot
  let widths := rg ∘ canonicalProfileWidthSlot
  have hgeo := hrg.comp canonicalProfileGeometrySlot_injective
  have hwidths := hrg.comp canonicalProfileWidthSlot_injective
  have hgeoBlank : ∀ j : Fin 20, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (geo j) = [] := by
    intro j h0 h9 h18
    apply hblank
    · exact fun h => h0 (Fin.ext (congrArg (fun k : Fin 28 => k.val) h))
    · exact fun h => h9 (Fin.ext (congrArg (fun k : Fin 28 => k.val) h))
    · exact fun h => h18 (Fin.ext (congrArg (fun k : Fin 28 => k.val) h))
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalResidueGeometry_exec body geo hgeo L n r
    hn hlarge hdivisor hr v S hdimension hresidue hgeoBlank
  let C : Stacks T A := { S with R := canonicalResidueGeometryBank S.R geo L n r }
  have keep (j : Fin 28) (hj : j ∉ ([1,2,11,14,16,17,19] : List (Fin 28))) :
      C.R (rg j) = S.R (rg j) := by
    dsimp only [C, canonicalResidueGeometryBank]
    rw [Function.update_of_ne (by simpa [geo, canonicalProfileGeometrySlot, hrg.eq_iff] using
      (show j ≠ 19 by intro h; subst j; simp at hj))]
    apply canonicalGeometryBank_keep
    have hj' : j ∉ ([1,2,11,14,16,17] : List (Fin 28)) := by
      simp only [List.mem_cons, not_or] at hj ⊢
      tauto
    simpa [canonicalGeometryTargets, geo, canonicalResidueCommonSlot,
      canonicalProfileGeometrySlot, hrg.eq_iff] using hj'
  have hc0 : C.R (widths 0) = binSyms L n := (keep 0 (by decide)).trans hdimension
  have hc1 : C.R (widths 1) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [C, widths, geo, canonicalProfileWidthSlot, canonicalProfileGeometrySlot,
      canonicalResidueGeometryBank, canonicalGeometryBank, routerReservoirGeometryBank,
      routerGeometryBank, canonicalResidueCommonSlot, routerReservoirCommonSlot, canonicalRouterStride, hrg.eq_iff]
  have hwblank : ∀ j : Fin 11, j ≠ 0 → j ≠ 1 → j ≠ 7 → C.R (widths j) = [] := by
    intro j h0 h1 h7
    have sep : canonicalProfileWidthSlot j ∉ ([1,2,11,14,16,17,19] : List (Fin 28)) ∧
        canonicalProfileWidthSlot j ≠ 0 ∧ canonicalProfileWidthSlot j ≠ 9 ∧ canonicalProfileWidthSlot j ≠ 18 := by
      fin_cases j <;> simp_all [canonicalProfileWidthSlot]
    exact (keep _ sep.1).trans (hblank _ sep.2.1 sep.2.2.1 sep.2.2.2)
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := canonicalDescriptorWidths_canonical_exec body widths hwidths
    L n hn hlarge v₁ C hc0 hc1 hwblank
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by nlinarith only [hm₁, hm₂], Exec.seq hex₁ hex₂⟩

/-- The generated bank supplies all five compact operands of the fixed compiler. -/
theorem canonicalProfileSetup_parameters
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T) (hrg : Function.Injective rg)
    (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hresidue : R (rg 18) = binSyms L r.val) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val
    let w := canonicalStageWidths p
    let B := canonicalProfileSetupBank R rg L n r.val
    B (rg 1) = binSyms L p.K ∧ B (rg 18) = binSyms L p.ρ ∧
      B (rg 11) = binSyms L p.n ∧ B (rg 21) = binSyms L w.strideBits ∧
      B (rg 26) = binSyms L (w.indexBits + w.strideBits) := by
  dsimp only
  obtain ⟨hi, hg, hs, hsel, hw⟩ := canonicalStageWidths_router n hlarge r
  rw [hi, hs]
  simp [canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
    canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank,
    canonicalProfileWidthSlot, canonicalProfileGeometrySlot, canonicalResidueCommonSlot,
    routerReservoirCommonSlot, routerProfileParameters, canonicalRouterStride, hrg.eq_iff,
    hresidue, Nat.two_mul, Nat.add_comm, Nat.add_left_comm]

end IntegerMultBounds.MathlibTM2.Routing
