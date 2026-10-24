module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalStrideGenerate
public import IntegerMultBounds.MathlibTM2.Routing.RouterReservoirGeometry

/-! Generate canonical gap, stride, digits, tail, borrowed span and reservoir
width from the binary dimension alone. All remaining registers restore. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalGeometryStrideSlot : Fin 10 → Fin 18 := ![0,3,4,5,2,6,7,8,9,1]
theorem canonicalGeometryStrideSlot_injective : Function.Injective canonicalGeometryStrideSlot := by decide +kernel

def canonicalGeometryGenerateProgram (rg : Fin 18 → Fin T) : Pr P T Q A U :=
  .seq (canonicalStrideGenerateProgram (rg ∘ canonicalGeometryStrideSlot)) (routerReservoirGeometryProgram rg)

def canonicalGeometryBank (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T)
    (L n : ℕ) : Fin T → List (Fin (A + 4)) :=
  routerReservoirGeometryBank (Function.update (Function.update R (rg 2) (binSyms L (canonicalRouterGap n)))
    (rg 1) (binSyms L (canonicalRouterStride n))) rg L n (canonicalRouterGap n)

theorem canonicalGeometryGenerate_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 18, j ≠ 0 → j ≠ 9 → S.R (rg j) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 88 * L * L + 464 * L + 413 ∧
      Exec body (canonicalGeometryGenerateProgram rg) (mk v S) m
        (mk v' { S with R := canonicalGeometryBank S.R rg L n }) := by
  have hstrideBlank : ∀ j : Fin 10, j ≠ 0 → j ≠ 8 →
      S.R ((rg ∘ canonicalGeometryStrideSlot) j) = [] := by
    intro j hj0 hj8
    fin_cases j <;> simp only [Function.comp_apply, canonicalGeometryStrideSlot, Fin.isValue] <;>
      first | contradiction | (apply hblank <;> decide)
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalStrideGenerate_exec body (rg ∘ canonicalGeometryStrideSlot)
    (hrg.comp canonicalGeometryStrideSlot_injective) L n hn (by omega) v S hsrc hstrideBlank
  let C : Stacks T A := { S with R := (Function.update (Function.update S.R (rg 2)
    (binSyms L (canonicalRouterGap n))) (rg 1) (binSyms L (canonicalRouterStride n))) }
  have keep (j : Fin 18) (hj1 : j ≠ 1) (hj2 : j ≠ 2) : C.R (rg j) = S.R (rg j) := by
    simp [C, hrg.eq_iff, hj1, hj2]
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := routerReservoirGeometry_exec body rg hrg L n (canonicalRouterGap n)
    hn (canonicalRouterGap_pos n) hlarge hdivisor v₁ C
    ((keep 0 (by decide) (by decide)).trans hsrc)
    (by simp [C, canonicalRouterStride]) (by simp [C, hrg.eq_iff])
    (fun j hj0 hj1 hj2 hj9 => (keep j hj1 hj2).trans (hblank j hj0 hj9))
  exact ⟨v₂, m₁ + m₂, hu₂.trans hu₁, by nlinarith only [hm₁, hm₂], Exec.seq he₁ he₂⟩

def canonicalGeometryTargets (rg : Fin 18 → Fin T) : List (Fin T) :=
  [rg 1,rg 2,rg 11,rg 14,rg 16,rg 17]

theorem canonicalGeometryBank_keep
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (L n : ℕ)
    (x : Fin T) (hx : x ∉ canonicalGeometryTargets rg) :
    canonicalGeometryBank R rg L n x = R x := by
  simp only [canonicalGeometryTargets, List.mem_cons, List.not_mem_nil, or_false, not_or] at hx
  rw [canonicalGeometryBank, routerReservoirGeometryBank_keep _ rg L n (canonicalRouterGap n) x
    (by simp [routerReservoirGeometryTargets, hx.2.2.1, hx.2.2.2.1, hx.2.2.2.2.1, hx.2.2.2.2.2])]
  simp [hx.1, hx.2.1]

theorem canonicalGeometryBank_clean
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (L n : ℕ)
    (hblank : ∀ x ∈ canonicalGeometryTargets rg, R x = []) :
    metadataCleared (canonicalGeometryBank R rg L n) (canonicalGeometryTargets rg) = R := by
  funext x
  by_cases hx : x ∈ canonicalGeometryTargets rg
  · rw [metadataCleared_at _ _ _ hx]
    exact (hblank x hx).symm
  · rw [metadataCleared_keep _ _ _ hx, canonicalGeometryBank_keep R rg L n x hx]

theorem canonicalGeometryBank_cleanCost
    (R : Fin T → List (Fin (A + 4))) (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n : ℕ) :
    metadataCleanCost (canonicalGeometryBank R rg L n) (canonicalGeometryTargets rg) = 12 * L + 13 := by
  simp [canonicalGeometryTargets, metadataCleanCost, canonicalGeometryBank,
    routerReservoirGeometryBank, routerGeometryBank, routerReservoirCommonSlot, hrg.eq_iff, length_binSyms]
  ring

def canonicalGeometryScope (rg : Fin 18 → Fin T) (call : Pr P T Q A U) : Pr P T Q A U :=
  .seq (canonicalGeometryGenerateProgram rg) (.seq call (metadataClean (canonicalGeometryTargets rg)))

theorem canonicalGeometryScope_exec (body : P → Pr P T Q A U)
    (rg : Fin 18 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2 ^ L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3 * canonicalRouterGap n < 2 ^ L)
    (v : HS T Q A U) (S : Stacks T A) (hsrc : S.R (rg 0) = binSyms L n)
    (hblank : ∀ j : Fin 18, j ≠ 0 → j ≠ 9 → S.R (rg j) = [])
    (str : Fin T) (hstr : str ∉ canonicalGeometryTargets rg) (output : List (Fin (A + 4)))
    (call : Pr P T Q A U) (price : ℕ)
    (hcall : ∀ u : HS T Q A U,
      let C : Stacks T A := { S with R := canonicalGeometryBank S.R rg L n }
      ∃ (u' : HS T Q A U) (m : ℕ), u'.user = u.user ∧ m ≤ price ∧
        Exec body call (mk u C) m (mk u' { C with R := Function.update C.R str output })) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ price + 88 * L * L + 476 * L + 426 ∧
      Exec body (canonicalGeometryScope rg call) (mk v S) m
        (mk v' { S with R := Function.update S.R str output }) := by
  obtain ⟨v₁, m₁, hu₁, hm₁, he₁⟩ := canonicalGeometryGenerate_exec body rg hrg L n hn hlarge hdivisor v S hsrc hblank
  let C : Stacks T A := { S with R := canonicalGeometryBank S.R rg L n }
  obtain ⟨v₂, m₂, hu₂, hm₂, he₂⟩ := hcall v₁
  let D : Stacks T A := { C with R := Function.update C.R str output }
  obtain ⟨v₃, hu₃, he₃⟩ := metadataClean_exec body (canonicalGeometryTargets rg)
    (by simp [canonicalGeometryTargets, List.nodup_cons, hrg.eq_iff]) v₂ D
  have hcost : metadataCleanCost D.R (canonicalGeometryTargets rg) = 12 * L + 13 := by
    rw [metadataCleanCost_congr _ (R' := C.R) (by
      intro x hx
      apply Function.update_of_ne
      intro he
      exact hstr (he ▸ hx))]
    exact canonicalGeometryBank_cleanCost S.R rg hrg L n
  have htargetsBlank : ∀ x ∈ canonicalGeometryTargets rg, S.R x = [] := by
    intro x hx
    simp only [canonicalGeometryTargets, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl | rfl <;> apply hblank <;> decide
  have hfinal : metadataCleared D.R (canonicalGeometryTargets rg) = Function.update S.R str output := by
    rw [show D.R = Function.update C.R str output from rfl, metadataCleared_update _ _ _ _ hstr]
    rw [canonicalGeometryBank_clean S.R rg L n htargetsBlank]
  rw [hcost, hfinal] at he₃
  exact ⟨v₃, m₁ + (m₂ + (12 * L + 13)), hu₃.trans (hu₂.trans hu₁), by omega,
    Exec.seq he₁ (Exec.seq he₂ he₃)⟩

end IntegerMultBounds.MathlibTM2.Routing
