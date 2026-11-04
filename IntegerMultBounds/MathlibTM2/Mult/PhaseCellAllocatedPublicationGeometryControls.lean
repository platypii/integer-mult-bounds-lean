module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellPublicationGeometryControls
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellAllocatedPublicationDimensions

/-! Place three binary inputs and two owned controls in caller storage.
Four arithmetic scratch ports reuse the existing routing suffix. -/
@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
open IntegerMultBounds IntegerMultBounds.MathlibTM2 IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Node
noncomputable section
variable {T A : ℕ}

def publicationGeometrySources (origins : Fin 7 → Fin T) (src : Fin 10 → Fin T) : Fin 5 → Fin T :=
  ![origins 0,origins 2,origins 3,src 4,src 8]

theorem publicationGeometrySources_injective (origins : Fin 7 → Fin T) (src : Fin 10 → Fin T)
    (ho : Function.Injective origins) (hs : Function.Injective src)
    (hoff : ∀ j ∈ [(0 : Fin 7),2,3], ∀ k ∈ [(4 : Fin 10),8], origins j ≠ src k) :
    Function.Injective (publicationGeometrySources origins src) := by
  have h04 := hoff 0 (by simp) 4 (by simp)
  have h08 := hoff 0 (by simp) 8 (by simp)
  have h24 := hoff 2 (by simp) 4 (by simp)
  have h28 := hoff 2 (by simp) 8 (by simp)
  have h34 := hoff 3 (by simp) 4 (by simp)
  have h38 := hoff 3 (by simp) 8 (by simp)
  intro i j hij
  fin_cases i <;> fin_cases j <;>
    simp_all [publicationGeometrySources,ho.eq_iff,hs.eq_iff,Ne.symm]

def publicationGeometryPrivate (i : Fin 9) : Fin tapeCount := headerReg ⟨50+i.val,by have := i.isLt; omega⟩

def publicationGeometryRole (i : Fin 9) : Option (Fin 5) := if h : i.val < 5 then some ⟨i.val,h⟩ else none

def publicationGeometryPlacement (src : Fin 5 → Fin T) : Fin 9 → Fin (T+tapeCount) :=
  sharedRegisterPlacement (Fin.natAdd T ∘ publicationGeometryPrivate) (Fin.castAdd tapeCount ∘ src)
    publicationGeometryRole

theorem publicationGeometryPlacement_shared (src : Fin 5 → Fin T) (i : Fin 5) :
    publicationGeometryPlacement src (Fin.castAdd 4 i) = Fin.castAdd tapeCount (src i) := by
  simp [publicationGeometryPlacement,sharedRegisterPlacement,publicationGeometryRole]

theorem publicationGeometryPlacement_private (src : Fin 5 → Fin T) (i : Fin 9) (hi : 5 ≤ i.val) :
    publicationGeometryPlacement src i = Fin.natAdd T (publicationGeometryPrivate i) := by
  simp [publicationGeometryPlacement,sharedRegisterPlacement,publicationGeometryRole,show ¬i.val < 5 by omega]

theorem publicationGeometryPlacement_injective (src : Fin 5 → Fin T) (hs : Function.Injective src) :
    Function.Injective (publicationGeometryPlacement src) := by
  have hp : Function.Injective (Fin.natAdd T ∘ publicationGeometryPrivate) := by
    intro i j hij
    have hh := headerReg_injective ((Fin.natAdd_injective _ _) hij)
    have hv := congrArg Fin.val hh
    simp only [publicationGeometryPrivate,Function.comp_apply] at hij
    apply Fin.ext
    change 50+i.val = 50+j.val at hv
    omega
  apply sharedRegisterPlacement_injective _ hp _ ((Fin.castAdd_injective _ _).comp hs)
  · intro i j heq
    have hh := congrArg (fun k : Fin (T+tapeCount) => k.val) heq
    simp only [Function.comp_apply,Fin.val_natAdd,Fin.val_castAdd] at hh
    have := (src j).isLt
    omega
  · intro i j k hi hj
    unfold publicationGeometryRole at hi hj
    split_ifs at hi hj <;> simp_all only [Option.some.injEq]
    apply Fin.ext
    exact (congrArg Fin.val hi).trans (congrArg Fin.val hj).symm

theorem publicationGeometryPlacement_off_prefix (src : Fin 5 → Fin T) (k : Fin T)
    (hoff : ∀ j, src j ≠ k) (i : Fin 9) : publicationGeometryPlacement src i ≠ Fin.castAdd tapeCount k := by
  by_cases hi : i.val < 5
  · have heq : i = Fin.castAdd 4 (⟨i.val,hi⟩ : Fin 5) := Fin.ext rfl
    rw [heq,publicationGeometryPlacement_shared]
    exact (Fin.castAdd_injective _ _).ne (hoff _)
  · rw [publicationGeometryPlacement_private src i (by omega)]
    intro heq
    have hh := congrArg (fun j : Fin (T+tapeCount) => j.val) heq
    simp only [Fin.val_natAdd,Fin.val_castAdd] at hh
    have := k.isLt
    omega

end
end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.PackedTranspose
