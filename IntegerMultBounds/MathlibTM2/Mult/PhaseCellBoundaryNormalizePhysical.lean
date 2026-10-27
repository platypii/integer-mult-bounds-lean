module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryNormalizeRuns
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPowerWordHeader
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellBoundaryFactorWorkspace

/-! Construct and retire the normalization scalar on the physical factor bank. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Fast
  IntegerMultBounds.MathlibTM2.Mult.BandFactor

/-- A valuation update at an injectively placed factor role is a physical tape update. -/
theorem boundaryFactorState_update {A : ℕ} (S : Stacks 224 A) (r : RsbR) (xs : List (Fin (A+4))) :
    boundaryFactorState {S with R := Function.update S.R (boundaryFactorReg r) xs} =
      Function.update (boundaryFactorState S) r xs :=
  funext (rsb_holds_upd boundaryFactorReg_injective (fun _ => rfl) r xs)

/-- The valuation and its frame determine the complete physical state after a one-port update. -/
theorem boundaryFactorFr_update {A : ℕ} {S S' : Stacks 224 A} (r : RsbR) (xs : List (Fin (A+4)))
    (hframe : RsbFr boundaryFactorReg S S')
    (hholds : RsbHolds boundaryFactorReg S' (Function.update (boundaryFactorState S) r xs)) :
    S' = {S with R := Function.update S.R (boundaryFactorReg r) xs} := by
  classical
  refine Stacks.ext hframe.1 hframe.2.1 hframe.2.2.1 ?_
  funext i
  by_cases hi : ∃ a, boundaryFactorReg a = i
  · obtain ⟨a,rfl⟩ := hi
    exact (hholds a).trans (rsb_holds_upd boundaryFactorReg_injective (fun _ => rfl) r xs a).symm
  · change S'.R i = Function.update S.R (boundaryFactorReg r) xs i
    rw [hframe.2.2.2 i (by simpa using hi)]
    rw [Function.update_of_ne (fun h => hi ⟨r,h.symm⟩)]

variable {Q A : ℕ} {P U : Type} {body : P → Pr P 224 Q A U}

noncomputable def boundaryNormalizePhysical (hQ : SS.states ≤ Q) : Pr P 224 Q A U :=
  .seq (powerWordHeader 160 223 220 221 184 0)
    (.seq (boundaryNormalizeP boundaryFactorReg boundaryFactorMulReg_injective (by decide) hQ) (uclear 220))

def boundaryNormalizePhysicalCost (q e N : ℕ) : ℕ :=
  (4*(2*q+8)+4+(8*e+9))+(boundaryNormalizeCost (2*q+8) N+(2*(2*q+8)+2))

/-- Normalize the gathered RHS, constructing its scalar from a runtime exponent header.
Only the RHS port changes; the scalar and its private scratch are retired. -/
theorem boundaryNormalizePhysical_exec (hQ : SS.states ≤ Q) (hA : 96 ≤ A)
    (q E e : ℕ) (hq : q = E+e+1) (xs : List GaussianInt)
    (hbound : ∀ z ∈ xs, |gv q z.re| ≤ (2 : ℝ)^E ∧ |gv q z.im| ≤ (2 : ℝ)^E)
    (v : HS 224 Q A U) (S : Stacks 224 A)
    (hleft : ∀ i, S.L i = []) (hmul : ∀ i : Fin 64, S.R (boundaryFactorMulReg i) = [])
    (hready : RsbReady (boundaryFactorState S) (2*q+8) q)
    (he : (S.R 223).length = e) (hsrc : S.R 206 = cstream A (2*q+8) xs)
    (h184 : S.R 184 = []) (h220 : S.R 220 = []) (h221 : S.R 221 = [])
    (hya : S.R 208 = []) (hac2 : S.R 215 = []) :
    ∃ v' n, v'.user = v.user ∧ n ≤ boundaryNormalizePhysicalCost q e xs.length ∧
      Exec body (boundaryNormalizePhysical hQ) (mk v S) n
        (mk v' {S with R := (Function.update S.R 206
          (cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))))}) := by
  obtain ⟨v₁,hu₁,he₁⟩ := powerWordHeader_exec (body := body)
    (width := 160) (exponent := 223) (dst := 220) (parked := 221) (saved := 184) (tmp := 0)
    (by decide) (2*q+8) e (by omega) v S hready.wn he h220 h221 h184 (hmul 0)
  let scalar := csyms A (2*q+8) (⟨(2 : ℤ)^e,0⟩ : GaussianInt)
  let S₁ : Stacks 224 A := {S with R := Function.update S.R 220 scalar}
  have hstate : boundaryFactorState S₁ = Function.update (boundaryFactorState S) .dtab scalar :=
    boundaryFactorState_update S .dtab scalar
  have hrun := boundary_normalize_runs (body := body) boundaryFactorReg_injective boundaryFactorReg_disjoint
    boundaryFactorMulReg_injective (by decide) hQ hA q E e hq (boundaryFactorState S₁)
    (by rw [hstate]; exact hready.update .dtab (fun _ => by simp) scalar) xs hbound
    (by rw [hstate]; exact hsrc) (by rw [hstate]; rfl)
    (by rw [hstate]; exact hya) (by rw [hstate]; exact hac2)
  obtain ⟨v₂,S₂,n₂,hu₂,hn₂,he₂,hholds,hframe⟩ := hrun v₁ S₁ ⟨hleft,by
    intro i
    have hi220 : boundaryFactorMulReg i ≠ 220 := by
      intro hi
      have hv := congrArg (fun k : Fin 224 => k.val) hi
      have hi' := i.isLt
      change i.val = 220 at hv
      omega
    simpa only [S₁,Function.update_of_ne hi220] using hmul i⟩ (fun _ => rfl)
  have hS₂ := boundaryFactorFr_update .vk _ hframe hholds
  rw [hS₂] at he₂
  let output := cstream A (2*q+8) (xs.map (normalizeBoundaryWord q e))
  let S₂' : Stacks 224 A := {S₁ with R := Function.update S₁.R 206 output}
  obtain ⟨v₃,hu₃,he₃⟩ := uclear_exec body 220 v₂ S₂'
  have hlen : (S₂'.R 220).length = 2*q+8 := by simp [S₂',S₁,scalar]
  have he₃' : Exec body (uclear 220) (mk v₂ S₂') (2*(2*q+8)+2)
      (mk v₃ {S₂' with R := Function.update S₂'.R 220 []}) := he₃.cast (by rw [hlen]) rfl
  refine ⟨v₃,(4*(2*q+8)+4+(8*e+9))+(n₂+(2*(2*q+8)+2)),hu₃.trans (hu₂.trans hu₁),
    Nat.add_le_add_left (Nat.add_le_add_right hn₂ _) _,(Exec.seq he₁ (Exec.seq he₂ he₃')).cast rfl ?_⟩
  apply congrArg (mk v₃)
  refine Stacks.ext rfl rfl rfl ?_
  funext i
  by_cases hi220 : i = 220 <;> by_cases hi206 : i = 206 <;>
    simp [S₂',S₁,scalar,output,hi220,hi206,h220]

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz
