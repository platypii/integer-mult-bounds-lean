module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalPlacementWidth
public import IntegerMultBounds.MathlibTM2.Routing.BinaryResizeBatchScope

/-! Resize the nine reservoir coordinates to the exact canonical dimension
width. The executed job schedule depends only on the finite reservoir class. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2.Stack
open IntegerMultBounds.MathlibTM2.Host
variable {T Q A : ℕ} {P U : Type}

def canonicalPlacementResizeCore : Fin 34 → Fin 49 := Fin.castLE (by decide)
theorem canonicalPlacementResizeCore_injective : Function.Injective canonicalPlacementResizeCore := by decide +kernel
def placementStage (j : Fin 9) : Fin 3 := ⟨j.val / 3,by have := j.isLt; omega⟩
def placementAxis (j : Fin 9) : Fin 3 := ⟨j.val % 3,Nat.mod_lt _ (by decide)⟩
def canonicalPlacementResizeSlot (k : Fin 3) (j : Fin 9) : Fin 9 → Fin 49 :=
  ![33,Fin.castLE (by decide) (canonicalPlacementCoordinateSource k (placementStage j) (placementAxis j)),
    43,⟨34+j.val,by have := j.isLt; omega⟩,44,45,46,47,48]
theorem canonicalPlacementResizeSlot_injective (k : Fin 3) (j : Fin 9) :
    Function.Injective (canonicalPlacementResizeSlot k j) := by
  fin_cases k <;> fin_cases j <;> decide +kernel

def canonicalPlacementResizeProgram (rg : Fin 49 → Fin T) (k : Fin 3) : Pr P T Q A U :=
  .seq (canonicalPlacementWidthProgram (rg ∘ canonicalPlacementResizeCore))
    (binaryResizeBatchProgram (fun j => rg ∘ canonicalPlacementResizeSlot k j) (List.finRange 9))

def canonicalPlacementCoordinateValue (n : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (j : Fin 9) :=
  let spec := reservoirExchangeSpecs n (routingReservoirWidth n (canonicalRouterGap n))
    (routingReservoir_fit n (canonicalRouterGap n) hlarge)
    (routerBorrowed n (canonicalRouterStride n) (canonicalRouterGap n))
    (routerBorrowed_le_reservoir n (canonicalRouterGap n) (canonicalRouterGap_pos n)) k (placementStage j)
  ![spec.a,spec.b,spec.w] (placementAxis j)

def canonicalPlacementResizedBank (R : Fin T → List (Fin (A+4))) (rg : Fin 49 → Fin T)
    (L n : ℕ) (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) :=
  binaryResizeBatchBank (canonicalPlacementWidthBank R (rg ∘ canonicalPlacementResizeCore) L n)
    (fun j => rg ∘ canonicalPlacementResizeSlot k j) (fun _ => canonicalScalarWidth n)
    (canonicalPlacementCoordinateValue n hlarge k) (List.finRange 9)

theorem canonicalPlacementResizedBank_coordinate (R : Fin T → List (Fin (A+4)))
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (k : Fin 3) (j : Fin 9) :
    canonicalPlacementResizedBank R rg L n hlarge k (rg ⟨34+j.val,by have := j.isLt; omega⟩) =
      binSyms (canonicalScalarWidth n) (canonicalPlacementCoordinateValue n hlarge k j) := by
  apply binaryResizeBatchBank_at
  · apply List.Nodup.map
    · intro a b h
      have hv := congrArg (fun x : Fin 49 => x.val) (hrg h)
      change 34+a.val = 34+b.val at hv
      exact Fin.ext (by omega)
    · exact List.nodup_finRange 9
  · exact List.mem_finRange j

theorem canonicalPlacementResize_exec (body : P → Pr P T Q A U)
    (rg : Fin 49 → Fin T) (hrg : Function.Injective rg) (L n : ℕ)
    (hn : n < 2^L) (hlarge : canonicalRouterStride n ≤ n)
    (hdivisor : canonicalRouterStride n + 3*canonicalRouterGap n < 2^L) (k : Fin 3)
    (v : HS T Q A U) (S : Stacks T A) (hdimension : S.R (rg 0) = binSyms L n)
    (hblank : ∀ i : Fin 49, i ≠ 0 → i ≠ 9 → S.R (rg i) = []) :
    ∃ (v' : HS T Q A U) (m : ℕ), v'.user = v.user ∧
      m ≤ 92*L*L+572*L+529 + binaryResizeBatchCost (fun _ : Fin 9 => L) (fun _ => L)
        (fun _ => canonicalScalarWidth n) (List.finRange 9) ∧
      Exec body (canonicalPlacementResizeProgram rg k) (mk v S) m
        (mk v' { S with R := canonicalPlacementResizedBank S.R rg L n hlarge k }) := by
  let core := rg ∘ canonicalPlacementResizeCore
  have hc : Function.Injective core := hrg.comp canonicalPlacementResizeCore_injective
  obtain ⟨v₁,m₁,hu₁,hm₁,he₁⟩ := canonicalPlacementWidth_exec body core hc L n hn hlarge hdivisor v S
    hdimension (by
      intro i h0 h9
      exact hblank _ (fun h => h0 (Fin.ext (congrArg (fun x : Fin 49 => x.val) h)))
        (fun h => h9 (Fin.ext (congrArg (fun x : Fin 49 => x.val) h))))
  let C : Stacks T A := { S with R := canonicalPlacementWidthBank S.R core L n }
  let slots := fun j => rg ∘ canonicalPlacementResizeSlot k j
  have newBlank (i : Fin 49) (hi : 34 ≤ i.val) : C.R (rg i) = [] := by
    have off : ∀ j : Fin 34, rg i ≠ core j := by
      intro j he
      have hv := congrArg (fun x : Fin 49 => x.val) (hrg he)
      change i.val = j.val at hv
      have := j.isLt
      omega
    simp [C,canonicalPlacementWidthBank,canonicalPlacementOperandBank,
      reservoirExchangeOperandBank,reservoirExchangeOperandJobs,canonicalGeometryBank,
      routerReservoirGeometryBank,routerGeometryBank,Function.comp_def,off]
    apply hblank <;> intro he <;> subst i <;> norm_num at hi
  have hdst : ((List.finRange 9).map (fun j => slots j 3)).Nodup := by
    apply List.Nodup.map
    · intro a b h
      have hv := congrArg (fun x : Fin 49 => x.val) (hrg h)
      change 34+a.val = 34+b.val at hv
      exact Fin.ext (by omega)
    · exact List.nodup_finRange 9
  have sep : ∀ j i, i ≠ 3 → ∀ t,
      canonicalPlacementResizeSlot k j i ≠ canonicalPlacementResizeSlot k t 3 := by
    fin_cases k <;> decide +kernel
  have scratch : ∀ j i, i ≠ 0 → i ≠ 1 → i ≠ 3 → 34 ≤ (canonicalPlacementResizeSlot k j i).val := by
    fin_cases k <;> decide +kernel
  have width : canonicalScalarWidth n < 2^L := by
    have hw : canonicalScalarWidth n ≤ L := Nat.clog_le_of_le_pow (Nat.succ_le_of_lt hn)
    exact hw.trans_lt (Nat.lt_two_pow_self (n := L))
  obtain ⟨v₂,m₂,hu₂,hm₂,he₂⟩ := binaryResizeBatch_exec body slots
    (fun j => hrg.comp (canonicalPlacementResizeSlot_injective k j))
    (fun _ => L) (fun _ => L) (fun _ => canonicalScalarWidth n)
    (canonicalPlacementCoordinateValue n hlarge k) (fun _ => width)
    (fun j => (BlockExchangeSpec.coordinateValue_le _ _).trans_lt hn) (List.finRange 9) hdst
    (fun j i hi t => hrg.ne (sep j i hi t)) v₁ C
    (by intro j; exact Function.update_self _ _ _)
    (by
      intro j
      have he := canonicalPlacementOperandBank_coordinates S.R (core ∘ canonicalPlacementWidthCore)
        (hc.comp canonicalPlacementWidthCore_injective) L n hlarge k (placementStage j) (placementAxis j)
      have hs : (Fin.castLE (by decide) (canonicalPlacementCoordinateSource k (placementStage j)
          (placementAxis j)) : Fin 49) ≠ 33 := by
        intro h
        have hv := congrArg Fin.val h
        have hl := (canonicalPlacementCoordinateSource k (placementStage j) (placementAxis j)).isLt
        change (canonicalPlacementCoordinateSource k (placementStage j) (placementAxis j)).val = 33 at hv
        omega
      simpa [C,canonicalPlacementWidthBank,slots,canonicalPlacementResizeSlot,
        canonicalPlacementCoordinateValue,core,canonicalPlacementResizeCore,
        canonicalPlacementWidthCore,Function.comp_def,hrg.eq_iff,hs] using he)
    (by intro j hj; exact newBlank _ (by change 34 ≤ 34+j.val; omega))
    (by intro j i h0 h1 h3; exact newBlank _ (scratch j i h0 h1 h3))
  exact ⟨v₂,m₁+m₂,hu₂.trans hu₁,Nat.add_le_add hm₁ hm₂,Exec.seq he₁ he₂⟩

end IntegerMultBounds.MathlibTM2.Routing
