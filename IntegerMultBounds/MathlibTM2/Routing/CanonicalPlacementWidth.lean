module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementOperands
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScalarWidth

/-! Supply the exact live target-width operand for placement coordinate resizing.
The numeric dimension and all generated coordinates remain available. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalPlacementWidthCore : Fin 33 → Fin 34 := Fin.castLE (by decide)
def canonicalPlacementWidthSlot : Fin 6 → Fin 34 := ![0,25,33,3,4,9]
theorem canonicalPlacementWidthCore_injective : Function.Injective canonicalPlacementWidthCore := by decide +kernel
theorem canonicalPlacementWidthSlot_injective : Function.Injective canonicalPlacementWidthSlot := by decide +kernel

def canonicalPlacementWidthProgram (rg : Fin 34 → Fin T) : Pr P T Q A U :=
  .seq (canonicalPlacementOperandsProgram (rg ∘ canonicalPlacementWidthCore))
    (binaryScalarWidthProgram (rg ∘ canonicalPlacementWidthSlot))

def canonicalPlacementWidthBank (R : Fin T → List (Fin (A+4)))
    (rg : Fin 34 → Fin T) (L n : ℕ) :=
  Function.update (canonicalPlacementOperandBank R (rg ∘ canonicalPlacementWidthCore) L n)
    (rg 33) (binSyms L (canonicalScalarWidth n))

theorem canonicalPlacementWidth_exec (body : P → Pr P T Q A U)
    (rg : Fin 34 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2^L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hblank : ∀ i : Fin 34, i ≠ 0 → i ≠ 9 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 92*L*L+572*L+529 ∧
      Exec body (canonicalPlacementWidthProgram rg) (mk v S) m
        (mk v' { S with R := canonicalPlacementWidthBank S.R rg L n }) := by
  let core := rg ∘ canonicalPlacementWidthCore
  have hc : Function.Injective core := hrg.comp canonicalPlacementWidthCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalPlacementOperands_exec body core hc L n hn hlarge hdivisor v S
    hdimension (by
      intro i h0 h9
      exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 34 => x.val) h)))
        (fun h => h9 (Fin.ext (congrArg (fun x : Fin 34 => x.val) h))))
  let C : Stacks T A := { S with R := canonicalPlacementOperandBank S.R core L n }
  have keep (i : Fin 34) (hi : i ∈ ([0,3,4,25,33] : List (Fin 34))) : C.R (rg i) = S.R (rg i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false] at hi
    rcases hi with rfl | rfl | rfl | rfl | rfl <;>
      simp [C,canonicalPlacementOperandBank,reservoirExchangeOperandBank,reservoirExchangeOperandJobs,
        canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
        canonicalPlacementOperandSlot,canonicalPlacementGeometrySlot,routerReservoirCommonSlot,
        core,canonicalPlacementWidthCore,Function.comp_def,hrg.eq_iff]
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := binaryScalarWidth_exec body (rg ∘ canonicalPlacementWidthSlot)
    (hrg.comp canonicalPlacementWidthSlot_injective) L n hn v₁ C
    ((keep 0 (by simp)).trans hdimension) (by
      intro i h0 h5
      fin_cases i
      · exact (h0 rfl).elim
      · exact (keep 25 (by simp)).trans (hblank 25 (by decide) (by decide))
      · exact (keep 33 (by simp)).trans (hblank 33 (by decide) (by decide))
      · exact (keep 3 (by simp)).trans (hblank 3 (by decide) (by decide))
      · exact (keep 4 (by simp)).trans (hblank 4 (by decide) (by decide))
      · exact (h5 rfl).elim)
  refine ⟨v₂,m₁+m₂,hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁,hm₂]

end IntegerMultBounds.MathlibTM2.Routing
