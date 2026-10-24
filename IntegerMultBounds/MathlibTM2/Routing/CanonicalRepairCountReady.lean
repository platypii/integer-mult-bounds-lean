module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairCountGenerate

/-! Sources needed by the remaining repair arithmetic survive zero/count setup.
The one-bit header word supplies overflow padding without a new numeric input. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host
variable {T A : ℕ}

def canonicalRepairCountHeader : Fin 120 → Fin 125 := canonicalRepairCountCore ∘ canonicalRepairZeroCore
theorem canonicalRepairCountHeader_injective : Function.Injective canonicalRepairCountHeader :=
  canonicalRepairCountCore_injective.comp canonicalRepairZeroCore_injective

theorem canonicalRepairCountGeneratedBank_keep (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (i : Fin 125) (h121 : i ≠ 121) (h122 : i ≠ 122) (h124 : i ≠ 124) :
    canonicalRepairCountGeneratedBank R rg L n r (rg i) =
      canonicalHeaderScalarGeneratedBank R (rg ∘ canonicalRepairCountHeader) L n r (rg i) := by
  simp [canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,repairZeroBank,
    canonicalRepairCountCore,canonicalRepairZeroSlot,canonicalRepairCountHeader,
    Function.comp_def,hrg.eq_iff,h121,h122,h124]

theorem canonicalRepairCountGeneratedBank_outside (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (L n r : ℕ) (k : Fin T) (hoff : ∀ i, rg i ≠ k) :
    canonicalRepairCountGeneratedBank R rg L n r k = R k := by
  have he : canonicalRepairCountGeneratedBank R rg L n r k =
      canonicalHeaderScalarGeneratedBank R (rg ∘ canonicalRepairCountHeader) L n r k := by
    simp [canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,repairZeroBank,
      canonicalRepairCountCore,canonicalRepairZeroSlot,canonicalRepairCountHeader,
      Function.comp_def,(hoff 121).symm,(hoff 122).symm,(hoff 124).symm]
  rw [he]
  exact canonicalHeaderScalarGeneratedBank_outside R (rg ∘ canonicalRepairCountHeader) L n r k (fun i => hoff _)

theorem canonicalRepairCountGeneratedBank_dimension (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    canonicalRepairCountGeneratedBank R rg L n r (rg 0) = R (rg 0) := by
  rw [canonicalRepairCountGeneratedBank_keep R rg hrg L n r 0 (by decide) (by decide) (by decide)]
  exact canonicalHeaderScalarGeneratedBank_dimension R (rg ∘ canonicalRepairCountHeader)
    (hrg.comp canonicalRepairCountHeader_injective) L n r

theorem canonicalRepairCountGeneratedBank_payload (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    canonicalRepairCountGeneratedBank R rg L n r (rg 120) = R (rg 120) := by
  rw [canonicalRepairCountGeneratedBank_keep R rg hrg L n r 120 (by decide) (by decide) (by decide)]
  apply canonicalHeaderScalarGeneratedBank_outside
  intro j h
  have hv := congrArg (fun i : Fin 125 => i.val) (hrg h)
  change j.val = 120 at hv
  have := j.isLt
  omega

theorem canonicalRepairCountGeneratedBank_one (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ) :
    canonicalRepairCountGeneratedBank R rg L n r (rg 118) = [bitSymbol true] := by
  rw [canonicalRepairCountGeneratedBank_keep R rg hrg L n r 118 (by decide) (by decide) (by decide)]
  simp [canonicalHeaderScalarGeneratedBank,headerScalarBank,canonicalHeaderScalarSlot,
    canonicalRepairCountHeader,canonicalRepairCountCore,canonicalRepairZeroCore,Function.comp_def,hrg.eq_iff]

theorem canonicalRepairCountGeneratedBank_scratch (R : Fin T → List (Fin (A + 4)))
    (rg : Fin 125 → Fin T) (hrg : Function.Injective rg) (L n r : ℕ)
    (hblank : ∀ i : Fin 125, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → R (rg i) = [])
    (i : Fin 118) (hi : i ∈ ([39,40,41,42,43,45] : List (Fin 118))) :
    canonicalRepairCountGeneratedBank R rg L n r
      (rg ⟨i.val,by have := i.isLt; omega⟩) = [] := by
  let header := rg ∘ canonicalRepairCountHeader
  have hh : Function.Injective header := hrg.comp canonicalRepairCountHeader_injective
  have hlo : i.val < 118 := i.isLt
  have h121 : (⟨i.val,by omega⟩ : Fin 125) ≠ 121 := by
    intro h; have hv := congrArg Fin.val h; simp only at hv; omega
  have h122 : (⟨i.val,by omega⟩ : Fin 125) ≠ 122 := by
    intro h; have hv := congrArg Fin.val h; simp only at hv; omega
  have h124 : (⟨i.val,by omega⟩ : Fin 125) ≠ 124 := by
    intro h; have hv := congrArg Fin.val h; simp only at hv; omega
  rw [canonicalRepairCountGeneratedBank_keep R rg hrg L n r _ h121 h122 h124]
  change canonicalHeaderScalarGeneratedBank R header L n r (header (canonicalHeaderScalarCore i)) = []
  rw [canonicalHeaderScalarGeneratedBank_low R header hh L n r _ i.isLt]
  apply canonicalHeaderBase_blank R header hh L n r
  · intro j h0 h9 h18
    apply hblank
    · intro h; exact h0 (Fin.ext (congrArg (fun k : Fin 125 => k.val) h))
    · intro h; exact h9 (Fin.ext (congrArg (fun k : Fin 125 => k.val) h))
    · intro h; exact h18 (Fin.ext (congrArg (fun k : Fin 125 => k.val) h))
    · intro h; have hv := congrArg (fun k : Fin 125 => k.val) h
      change j.val = 120 at hv
      have := j.isLt
      omega
  · exact hi

end IntegerMultBounds.MathlibTM2.Routing
