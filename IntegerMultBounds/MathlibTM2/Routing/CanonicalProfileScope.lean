module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalProfileSetup

/-! Borrow the generated canonical profile operands for a framed call, then erase
all eleven generated words. Dimension, residue, carry and all spectators restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalProfileTargets (rg : Fin 28 → Fin T) : List (Fin T) :=
  [rg 1,rg 2,rg 11,rg 14,rg 16,rg 17,rg 19,rg 21,rg 25,rg 26,rg 27]

theorem canonicalProfileSetupBank_keep
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T) (L n r : ℕ)
    (x : Fin T) (hx : x ∉ canonicalProfileTargets rg) :
    canonicalProfileSetupBank R rg L n r x = R x := by
  simp only [canonicalProfileTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  simp_all [canonicalProfileSetupBank, canonicalDescriptorWidthsBank, canonicalResidueGeometryBank,
    canonicalGeometryBank, routerReservoirGeometryBank, routerGeometryBank,
    canonicalProfileWidthSlot, canonicalProfileGeometrySlot, canonicalResidueCommonSlot,
    routerReservoirCommonSlot]

theorem canonicalProfileSetupBank_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T) (L n r : ℕ)
    (hblank : ∀ x ∈ canonicalProfileTargets rg, R x = []) :
    metadataCleared (canonicalProfileSetupBank R rg L n r) (canonicalProfileTargets rg) = R := by
  funext x
  by_cases hx : x ∈ canonicalProfileTargets rg
  · rw [metadataCleared_at _ _ _ hx]
    exact (hblank x hx).symm
  · rw [metadataCleared_keep _ _ _ hx, canonicalProfileSetupBank_keep R rg L n r x hx]

theorem canonicalProfileSetupBank_cleanCost
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 28 → Fin T) (hrg : Function.Injective rg)
    (L n r : ℕ) :
    metadataCleanCost (canonicalProfileSetupBank R rg L n r) (canonicalProfileTargets rg) = 22 * L + 23 := by
  simp [canonicalProfileTargets, metadataCleanCost, canonicalProfileSetupBank,
    canonicalDescriptorWidthsBank, canonicalResidueGeometryBank, canonicalGeometryBank,
    routerReservoirGeometryBank, routerGeometryBank, canonicalProfileWidthSlot,
    canonicalProfileGeometrySlot, canonicalResidueCommonSlot, routerReservoirCommonSlot,
    hrg.eq_iff, length_binSyms]
  ring

def canonicalProfileScope (rg : Fin 28 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (canonicalProfileSetupProgram rg) (.seq call (metadataClean (canonicalProfileTargets rg)))

theorem canonicalProfileScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 28 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (hr : r < canonicalRouterStride n) (v : HS T Q A U) (S : Stacks T A)
    (hdimension : S.R (rg 0) = binSyms L n) (hresidue : S.R (rg 18) = binSyms L r)
    (hblank : ∀ j : Fin 28, j ≠ 0 → j ≠ 9 → j ≠ 18 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ∉ canonicalProfileTargets rg) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := canonicalProfileSetupBank S.R rg L n r }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 96 * L * L + 584 * L + 549 ∧
      Exec body (canonicalProfileScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, hex₁⟩ := canonicalProfileSetup_exec body rg hrg L n r hn hlarge hdivisor hr
    v S hdimension hresidue hblank
  let C : Stacks T A := { S with R := canonicalProfileSetupBank S.R rg L n r }
  obtain ⟨v₂, m₂, hu₂, hm₂, hex₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, hex₃⟩ := metadataClean_exec body (canonicalProfileTargets rg)
    (by simp [canonicalProfileTargets, List.nodup_cons, hrg.eq_iff]) v₂ D
  have hcost : metadataCleanCost D.R (canonicalProfileTargets rg) = 22 * L + 23 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro x hx
      apply Function.update_of_ne
      intro he
      exact hstr (he ▸ hx))]
    exact canonicalProfileSetupBank_cleanCost S.R rg hrg L n r
  have htargetsBlank : ∀ x ∈ canonicalProfileTargets rg, S.R x = [] := by
    intro x hx
    simp only [canonicalProfileTargets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  have hfinal : metadataCleared D.R (canonicalProfileTargets rg) = Function.update S.R str output := by
    rw [show D.R = Function.update C.R str output from rfl, metadataCleared_update _ _ _ _ hstr]
    exact congrArg (fun R => Function.update R str output)
      (canonicalProfileSetupBank_clean S.R rg L n r htargetsBlank)
  rw [hcost, hfinal] at hex₃
  exact ⟨v₃, m₁ + (m₂ + (22 * L + 23)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq hex₁ (Exec.seq hex₂ hex₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
