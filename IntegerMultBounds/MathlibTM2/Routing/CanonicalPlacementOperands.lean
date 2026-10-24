module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalGeometryGenerate
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirExchangeOperandFrames
public import IntegerMultBounds.MathlibTM2.Routing.ReservoirBudget

/-! Placement coordinates from the original binary dimension. Reuse the common
canonical geometry and the existing reservoir operand generator. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalPlacementGeometrySlot : Fin 18 → Fin 33 := Fin.castLE (by decide)
def canonicalPlacementOperandSlot : Fin 22 → Fin 33 :=
  ![0,17,16,18,19,20,21,22,23,24,3,4,5,9,25,26,27,28,29,30,31,32]
theorem canonicalPlacementGeometrySlot_injective : Function.Injective canonicalPlacementGeometrySlot := by decide +kernel
theorem canonicalPlacementOperandSlot_injective : Function.Injective canonicalPlacementOperandSlot := by decide +kernel

def canonicalPlacementOperandsProgram (rg : Fin 33 → Fin T) : Pr P T Q A U :=
  .seq (canonicalGeometryGenerateProgram (rg ∘ canonicalPlacementGeometrySlot))
    (reservoirExchangeOperandsProgram (rg ∘ canonicalPlacementOperandSlot))

def canonicalPlacementOperandBank (R : Fin T → List (Fin (A+4)))
    (rg : Fin 33 → Fin T) (L n : ℕ) :=
  reservoirExchangeOperandBank (canonicalGeometryBank R (rg ∘ canonicalPlacementGeometrySlot) L n)
    (rg ∘ canonicalPlacementOperandSlot) L n (routingReservoirWidth n (canonicalRouterGap n))
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))

def canonicalPlacementCoordinateSource (k stage axis : Fin 3) : Fin 33 :=
  canonicalPlacementOperandSlot (reservoirExchangeFrameSlot k stage (Fin.castLE (by decide) axis))

theorem BlockExchangeSpec.coordinateValue_le {n : ℕ} (spec : BlockExchangeSpec n) (axis : Fin 3) :
    (![spec.a,spec.b,spec.w] axis) ≤ n := by
  have hs := spec.separate
  have hf := spec.fits
  fin_cases axis
  · change spec.a ≤ n; omega
  · change spec.b ≤ n; omega
  · change spec.w ≤ n; omega

theorem canonicalPlacementOperandBank_coordinates (R : Fin T → List (Fin (A+4)))
    (rg : Fin 33 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k stage axis : Fin 3) :
    let H := routingReservoirWidth n (canonicalRouterGap n)
    let w := routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)
    let spec := reservoirExchangeSpecs n H (routingReservoir_fit n (canonicalRouterGap n) hlarge)
      w (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k stage
    canonicalPlacementOperandBank R rg L n (rg (canonicalPlacementCoordinateSource k stage axis)) =
      binSyms L (![spec.a,spec.b,spec.w] axis) := by
  dsimp only
  have span : canonicalGeometryBank R (rg ∘ canonicalPlacementGeometrySlot) L n
      ((rg ∘ canonicalPlacementOperandSlot) 2) =
      binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
      canonicalPlacementGeometrySlot,canonicalPlacementOperandSlot,routerReservoirCommonSlot,
      Function.comp_def,hrg.eq_iff,canonicalRouterStride]
  have he := reservoirExchangeOperandFrames_ready
    (canonicalGeometryBank R (rg ∘ canonicalPlacementGeometrySlot) L n)
    (rg ∘ canonicalPlacementOperandSlot) (hrg.comp canonicalPlacementOperandSlot_injective) L n
    (routingReservoirWidth n (canonicalRouterGap n))
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routingReservoir_fit n (canonicalRouterGap n) hlarge)
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) span k stage
  fin_cases axis
  · exact he.1
  · exact he.2.1
  · exact he.2.2

theorem canonicalPlacementOperands_exec (body : P → Pr P T Q A U)
    (rg : Fin 33 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2^L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hblank : ∀ i : Fin 33, i ≠ 0 → i ≠ 9 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧ m ≤ 88*L*L+546*L+507 ∧
      Exec body (canonicalPlacementOperandsProgram rg) (mk v S) m
        (mk v' { S with R := canonicalPlacementOperandBank S.R rg L n }) := by
  let geo := rg ∘ canonicalPlacementGeometrySlot
  have hg : Function.Injective geo := hrg.comp canonicalPlacementGeometrySlot_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalGeometryGenerate_exec body geo hg L n hn hlarge hdivisor v S
    hdimension (by
      intro i h0 h9
      exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 33 => x.val) h)))
        (fun h => h9 (Fin.ext (congrArg (fun x : Fin 33 => x.val) h))))
  let C : Stacks T A := { S with R := canonicalGeometryBank S.R geo L n }
  have keep (i : Fin 33) (hi : i ∉ ([1,2,11,14,16,17] : List (Fin 33))) : C.R (rg i) = S.R (rg i) := by
    simp only [List.mem_cons,List.not_mem_nil,or_false,not_or] at hi
    simp [C,canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
      geo,canonicalPlacementGeometrySlot,routerReservoirCommonSlot,Function.comp_def,hrg.eq_iff,
      hi.1,hi.2.1,hi.2.2.1,hi.2.2.2.1,hi.2.2.2.2.1,hi.2.2.2.2.2]
  have srcH : C.R (rg 17) = binSyms L (routingReservoirWidth n (canonicalRouterGap n)) := by
    simp [C,canonicalGeometryBank,routerReservoirGeometryBank,geo,canonicalPlacementGeometrySlot]
  have srcW : C.R (rg 16) = binSyms L (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) := by
    simp [C,canonicalGeometryBank,routerReservoirGeometryBank,routerGeometryBank,
      geo,canonicalPlacementGeometrySlot,routerReservoirCommonSlot,Function.comp_def,hrg.eq_iff,canonicalRouterStride]
  have sep : ∀ i : Fin 22, i ≠ 0 → i ≠ 1 → i ≠ 2 → i ≠ 13 → i ≠ 18 →
      canonicalPlacementOperandSlot i ∉ ([1,2,11,14,16,17] : List (Fin 33)) ∧
      canonicalPlacementOperandSlot i ≠ 0 ∧ canonicalPlacementOperandSlot i ≠ 9 := by decide +kernel
  obtain ⟨v₂,hu₂,he₂⟩ := reservoirExchangeOperands_exec body (rg ∘ canonicalPlacementOperandSlot)
    (hrg.comp canonicalPlacementOperandSlot_injective) L n
    (routingReservoirWidth n (canonicalRouterGap n))
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n)) hn
    (routingReservoir_fit n (canonicalRouterGap n) hlarge)
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) v₁ C
    ((keep 0 (by decide)).trans hdimension) srcH srcW (by
      intro i h0 h1 h2 h13 h18
      have h := sep i h0 h1 h2 h13 h18
      exact (keep _ h.1).trans (hblank _ h.2.1 h.2.2))
  refine ⟨v₂,m₁+(82*L+94),hu₂.trans hu₁,?_,Exec.seq he₁ he₂⟩
  nlinarith only [hm₁]

end IntegerMultBounds.MathlibTM2.Routing
