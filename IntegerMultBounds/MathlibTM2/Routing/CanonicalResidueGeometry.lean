module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalGeometryGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RouterResidueTail

/-! Generate all canonical profile geometry from dimension and current residue.
The common geometry is reusable; only the final subtraction depends on residue. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalResidueCommonSlot : Fin 18 → Fin 20 := Fin.castLE (by decide)
def canonicalResidueTailSlot : Fin 7 → Fin 20 := ![14,18,19,3,4,5,9]
theorem canonicalResidueCommonSlot_injective : Function.Injective canonicalResidueCommonSlot := by decide +kernel
theorem canonicalResidueTailSlot_injective : Function.Injective canonicalResidueTailSlot := by decide +kernel

def canonicalResidueGeometryProgram (rg : Fin 20 → Fin T) : Pr P T Q A U :=
  .seq (canonicalGeometryGenerateProgram (rg ∘ canonicalResidueCommonSlot))
    (bsub (rg 14) (rg 18) (rg 19) (rg 3) (rg 4) (rg 5) (rg 9))

def canonicalResidueGeometryBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 20 → Fin T)
    (L n r : ℕ) : Fin T → List (Fin (A + 4)) :=
  Function.update (canonicalGeometryBank R (rg ∘ canonicalResidueCommonSlot) L n) (rg 19)
    (binSyms L (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r).m)

theorem canonicalResidueGeometry_exec (body : P → Pr P T Q A U)
    (rg : Fin 20 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (hr : r < canonicalRouterStride n) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r)
    (hblank : ∀ j : Fin 20, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 88 * L * L + 472 * L + 421 ∧
      Exec body (canonicalResidueGeometryProgram rg) (mk v S) m
        (mk v' { S with R := canonicalResidueGeometryBank S.R rg L n r }) := by
  let small := rg ∘ canonicalResidueCommonSlot
  have hs : Function.Injective small := hrg.comp canonicalResidueCommonSlot_injective
  have hcommonBlank : ∀ j : Fin 18, j ≠ 0 → j ≠ 9 → S.R (small j) = [] := by
    intro j hj0 hj9
    apply hblank
    · exact fun he => hj0 (Fin.ext (congrArg (fun a : Fin 20 => a.val) he))
    · exact fun he => hj9 (Fin.ext (congrArg (fun a : Fin 20 => a.val) he))
    · intro he
      have hv := congrArg Fin.val he
      change j.val = 18 at hv
      exact (Nat.ne_of_lt j.isLt) hv
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalGeometryGenerate_exec body small hs L n hn hlarge hdivisor
    v S hdimension hcommonBlank
  let C : Stacks T A := { S with R := canonicalGeometryBank S.R small L n }
  have keep (j : Fin 20) (hj : j ∉ ([1,2,11,14,16,17] : List (Fin 20))) : C.R (rg j) = S.R (rg j) := by
    apply canonicalGeometryBank_keep S.R small L n (rg j)
    simpa [canonicalGeometryTargets, small, canonicalResidueCommonSlot, hrg.eq_iff] using hj
  have htail : C.R (rg 14) = binSyms L (routerTail n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [C, canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank, small,
      canonicalResidueCommonSlot, routerReservoirCommonSlot, canonicalRouterStride, hrg.eq_iff]
  have hsep : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 →
      let a := canonicalResidueTailSlot j
      a ∉ ([1,2,11,14,16,17] : List (Fin 20)) ∧ a ≠ 0 ∧ a ≠ 9 ∧ a ≠ 18 := by decide +kernel
  have htailBlank : ∀ j : Fin 7, j ≠ 0 → j ≠ 1 → j ≠ 6 →
      C.R ((rg ∘ canonicalResidueTailSlot) j) = [] := by
    intro j hj0 hj1 hj6
    obtain ⟨ha,h0,h9,h18⟩ := hsep j hj0 hj1 hj6
    exact (keep _ ha).trans (hblank _ h0 h9 h18)
  obtain ⟨v₂, hu₂, he₂⟩ := routerResidueTail_exec body (rg ∘ canonicalResidueTailSlot)
    (hrg.comp canonicalResidueTailSlot_injective) L n (canonicalRouterStride n) (canonicalRouterGap n) r
    hn hlarge hr v₁ C htail ((keep 18 (by decide)).trans hresidue) htailBlank
  exact ⟨v₂, m₁ + (8 * L + 8), hu₂.trans hu₁, by omega, Exec.seq he₁ he₂⟩

/-- All five profile parameters have actual binary words in the generated bank. -/
theorem canonicalResidueGeometry_parameters
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 20 → Fin T) (hrg : Function.Injective rg)
    (L n r : ℕ) (hresidue : R (rg 18) = binSyms L r) :
    let p := routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r
    let B := canonicalResidueGeometryBank R rg L n r
    B (rg 1) = binSyms L p.K ∧ B (rg 18) = binSyms L p.ρ ∧
      B (rg 11) = binSyms L p.n ∧ B (rg 2) = binSyms L p.G ∧ B (rg 19) = binSyms L p.m := by
  simp [canonicalResidueGeometryBank, canonicalGeometryBank, routerReservoirGeometryBank,
    routerGeometryBank, canonicalResidueCommonSlot, routerReservoirCommonSlot,
    routerProfileParameters, canonicalRouterStride, hrg.eq_iff, hresidue]

end IntegerMultBounds.MathlibTM2.Routing
