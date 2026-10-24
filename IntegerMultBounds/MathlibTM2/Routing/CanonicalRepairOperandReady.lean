module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalRepairBlockGenerate

/-! The generated numeric bank supplies every initial repair word, including
empty controls. Shared zero words need not be duplicated before serialization. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Layer.CompactGadget
variable {T A : ℕ}
noncomputable section

def canonicalRepairBlockHeader : Fin 120 → Fin 130 :=
  canonicalRepairBlockCore ∘ canonicalRepairKeyCore ∘ canonicalRepairCountCore ∘ canonicalRepairZeroCore

theorem canonicalRepairBlockHeader_injective : Function.Injective canonicalRepairBlockHeader :=
  canonicalRepairBlockCore_injective.comp (canonicalRepairKeyCore_injective.comp
    (canonicalRepairCountCore_injective.comp canonicalRepairZeroCore_injective))

theorem canonicalRepairBlockGeneratedBank_scratch (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n r B : ℕ)
    (hblank : ∀ i : Fin 130, i ≠ 0 → i ≠ 9 → i ≠ 18 → i ≠ 120 → R (rg i) = [])
    (i : Fin 2) :
    canonicalRepairBlockGeneratedBank R rg L n r B (rg (if i = 0 then 40 else 41)) = [] := by
  let header := rg ∘ canonicalRepairBlockHeader
  have hb : ∀ j : Fin 120, j ≠ 0 → j ≠ 9 → j ≠ 18 → R (header j) = [] := by
    intro j h0 h9 h18
    apply hblank
    · intro h; exact h0 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h; exact h9 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h; exact h18 (Fin.ext (congrArg (fun k : Fin 130 => k.val) h))
    · intro h
      have hv := congrArg (fun k : Fin 130 => k.val) h
      change j.val = 120 at hv
      have := j.isLt
      omega
  have he := canonicalHeaderScalarGeneratedBank_scratch R header
    (hrg.comp canonicalRepairBlockHeader_injective) L n r hb i
  fin_cases i <;> simpa [canonicalRepairBlockGeneratedBank,canonicalRepairKeyGeneratedBank,
    canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,repairZeroBank,
    canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,canonicalRepairZeroCore,
    canonicalRepairZeroSlot,header,canonicalRepairBlockHeader,Function.comp_def,hrg.eq_iff] using he

def canonicalRepairOperandSource : RepairSetupKey → Fin 130
  | .inl (.field f) => ![121,122,121,121,128] f
  | .inl .block => 127
  | .inl .records => 124
  | .inr .payload => 126
  | .inr .keyLength => 125
  | _ => 128

theorem canonicalRepairBlockGeneratedBank_operands (R : Fin T → List (Fin (A+4)))
    (rg : Fin 130 → Fin T) (hrg : Function.Injective rg) (L n B : ℕ)
    (hlarge : canonicalRouterStride n ≤ n) (r : Fin (canonicalRouterStride n))
    (hblank : R (rg 128) = []) :
    (fun key => canonicalRepairBlockGeneratedBank R rg L n r.val B (rg (canonicalRepairOperandSource key))) =
      canonicalRepairPayload (routerProfileParameters n (canonicalRouterStride n) (canonicalRouterGap n) r.val)
        0 (canonicalScalarWidth 1) (canonicalScalarWidth (n+B+1)) (n+1)
        (canonicalScalarWidth B) (canonicalScalarWidth (n+1)) 1 B := by
  let header := rg ∘ canonicalRepairBlockCore ∘ canonicalRepairKeyCore ∘
    canonicalRepairCountCore ∘ canonicalRepairZeroCore
  have outside : ∀ j : Fin 120, header j ≠ rg 128 := by
    intro j he
    have hv := congrArg (fun x : Fin 130 => x.val) (hrg he)
    change j.val = 128 at hv
    have := j.isLt
    omega
  have empty : canonicalHeaderScalarGeneratedBank R header L n r.val (rg 128) = [] :=
    (canonicalHeaderScalarGeneratedBank_outside R header L n r.val _ outside).trans hblank
  dsimp [header,canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,
    canonicalRepairZeroCore,Function.comp_def] at empty
  funext key
  cases key with
  | inl key =>
    cases key with
    | field f =>
      fin_cases f <;> simp [canonicalRepairOperandSource,canonicalRepairBlockGeneratedBank,
        canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,
        repairZeroBank,canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,
        canonicalRepairZeroCore,canonicalRepairZeroSlot,Function.comp_def,hrg.eq_iff,
        canonicalRepairPayload,selectiveLen]; exact empty
    | block => exact canonicalRepairBlockGeneratedBank_block R rg L n B hlarge r _ _ _
    | records =>
      rw [canonicalRepair_countWord n hlarge r]
      simp [canonicalRepairOperandSource,canonicalRepairBlockGeneratedBank,
        canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,
        canonicalRepairBlockCore,canonicalRepairKeyCore,Function.comp_def,hrg.eq_iff]
    | desc i | header i j =>
      simpa [canonicalRepairOperandSource,canonicalRepairBlockGeneratedBank,
        canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,
        repairZeroBank,canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,
        canonicalRepairZeroCore,canonicalRepairZeroSlot,Function.comp_def,hrg.eq_iff,
        canonicalRepairPayload] using empty
  | inr key =>
    cases key <;> first
    | (rw [canonicalRepair_keyWord n hlarge r]; simp [canonicalRepairOperandSource,
        canonicalRepairBlockGeneratedBank,canonicalRepairKeyGeneratedBank,canonicalRepairBlockCore,
        Function.comp_def,hrg.eq_iff])
    | (simp [canonicalRepairOperandSource,canonicalRepairBlockGeneratedBank,
        canonicalRepairKeyGeneratedBank,canonicalRepairBlockCore,Function.comp_def,hrg.eq_iff,
        canonicalRepairPayload]; done)
    | (simpa [canonicalRepairOperandSource,canonicalRepairBlockGeneratedBank,
        canonicalRepairKeyGeneratedBank,canonicalRepairCountGeneratedBank,canonicalRepairZeroGeneratedBank,
        repairZeroBank,canonicalRepairBlockCore,canonicalRepairKeyCore,canonicalRepairCountCore,
        canonicalRepairZeroCore,canonicalRepairZeroSlot,Function.comp_def,hrg.eq_iff,
        canonicalRepairPayload] using empty)

end
end IntegerMultBounds.MathlibTM2.Routing
