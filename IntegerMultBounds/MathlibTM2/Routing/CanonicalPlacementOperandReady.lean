module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementScalarGenerate
public import IntegerMultBounds.MathlibTM2.Routing.BinaryScheduleLayout

/-! Every input of the actual binary placement schedule is now generated.
The record stream is a separate caller operand and has an empty placeholder. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A t₀ : ℕ}

def placementCoordinateIndex (stage axis : Fin 3) : Fin 9 :=
  ⟨3*stage.val+axis.val,by have := stage.isLt; have := axis.isLt; omega⟩

theorem placementStage_index (stage axis : Fin 3) :
    placementStage (placementCoordinateIndex stage axis) = stage := by
  apply Fin.ext
  dsimp [placementStage,placementCoordinateIndex]
  have := axis.isLt
  omega

theorem placementAxis_index (stage axis : Fin 3) :
    placementAxis (placementCoordinateIndex stage axis) = axis := by
  apply Fin.ext
  dsimp [placementAxis,placementCoordinateIndex]
  have := axis.isLt
  omega

def canonicalPlacementOperandSource : BinaryScheduleReg t₀ 3 → Fin 53
  | .coordinate stage axis => ⟨34+(placementCoordinateIndex stage axis).val,
      by have := (placementCoordinateIndex stage axis).isLt; omega⟩
  | .width => 50
  | .rows => 52
  | .block => 51
  | _ => 43

theorem canonicalPlacementScalarBank_low (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (i : Fin 49) :
    canonicalPlacementScalarBank R rg L n B hlarge k (rg (canonicalPlacementScalarCore i)) =
      canonicalPlacementResizedBank R (rg ∘ canonicalPlacementScalarCore) L n hlarge k
        (rg (canonicalPlacementScalarCore i)) := by
  have hi := i.isLt
  have off (j : Fin 53) (hj : 49 ≤ j.val) : canonicalPlacementScalarCore i ≠ j := by
    intro h
    have hv := congrArg Fin.val h
    change i.val = j.val at hv
    omega
  simp [canonicalPlacementScalarBank,headerScalarBank,canonicalPlacementScalarSlot,hrg.eq_iff,
    off 50 (by decide),off 51 (by decide),off 52 (by decide)]

theorem canonicalPlacementScalarBank_operands (R : Fin T → List (Fin (A+4)))
    (rg : Fin 53 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (hblank : R (rg 43) = []) :
    let spec := reservoirExchangeSpecs n (routingReservoirWidth n (canonicalRouterGap n))
      (routingReservoir_fit n (canonicalRouterGap n) hlarge)
      (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
      (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k
    (fun role : BinaryScheduleReg t₀ 3 =>
      canonicalPlacementScalarBank R rg L n B hlarge k (rg (canonicalPlacementOperandSource role))) =
      binaryScheduleInputWords spec (fun _ => []) (canonicalScalarWidth n) (canonicalScalarWidth B) B [true] [] := by
  dsimp only
  have empty : canonicalPlacementScalarBank R rg L n B hlarge k (rg 43) = [] := by
    exact (canonicalPlacementScalarBank_low R rg hrg L n B hlarge k 43).trans
      ((canonicalPlacementResizedBank_copyReady R (rg ∘ canonicalPlacementScalarCore)
        (hrg.comp canonicalPlacementScalarCore_injective) L n hlarge k 43 (by simp)).trans hblank)
  funext role
  cases role with
  | coordinate stage axis =>
    let j := placementCoordinateIndex stage axis
    have he := canonicalPlacementResizedBank_coordinate R (rg ∘ canonicalPlacementScalarCore)
      (hrg.comp canonicalPlacementScalarCore_injective) L n hlarge k j
    rw [show canonicalPlacementScalarBank R rg L n B hlarge k
        (rg (canonicalPlacementOperandSource (.coordinate stage axis : BinaryScheduleReg t₀ 3))) =
        canonicalPlacementResizedBank R (rg ∘ canonicalPlacementScalarCore) L n hlarge k
          (rg ⟨34+j.val,by have := j.isLt; omega⟩) from
      canonicalPlacementScalarBank_low R rg hrg L n B hlarge k ⟨34+j.val,by have := j.isLt; omega⟩]
    simpa [canonicalPlacementCoordinateValue,j,placementStage_index,placementAxis_index,binaryScheduleInputWords,
      canonicalPlacementScalarCore]
      using he
  | width | rows | block =>
    simp [canonicalPlacementOperandSource,canonicalPlacementScalarBank,headerScalarBank,
      canonicalPlacementScalarSlot,binaryScheduleInputWords,hrg.eq_iff]
  | _ => exact empty

end IntegerMultBounds.MathlibTM2.Routing
