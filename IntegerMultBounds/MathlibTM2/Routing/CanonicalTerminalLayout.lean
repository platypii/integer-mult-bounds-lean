module

public import IntegerMultBounds.MathlibTM2.Routing.CanonicalTerminalReady
public import Mathlib.Data.Fintype.EquivFin

/-! A fixed finite register bank for terminal routing. Compiler, router, shared
binary inputs and six external work tapes occupy disjoint summands. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Fast
noncomputable section

instance : Fintype ElementaryCoordinateReg := Fintype.ofList
  ([.width, .target, .source, .targetUnary, .sourceUnary, .gap, .rowExp, .renamed, .coord, .high] ++
    Finset.univ.toList.map ElementaryCoordinateReg.scratch)
  (by intro r; cases r <;> simp)

instance : Fintype ElementaryCompilerReg := Fintype.ofList
  (Finset.univ.toList.map ElementaryCompilerReg.coordinate ++ [.rows, .block, .mask, .output] ++
    Finset.univ.toList.map ElementaryCompilerReg.header)
  (by intro r; cases r <;> simp)

instance : Fintype SharedInputReg := Fintype.ofList
  ([.width, .rows, .block, .records, .field, .mask] ++ Finset.univ.toList.map SharedInputReg.scratch)
  (by intro r; cases r <;> simp)

instance {t₀ : ℕ} : Fintype (LayReg t₀) := by
  classical
  exact Fintype.ofList
    ([.str, .r0, .r1, .r2, .r3, .q0, .q1, .q2, .q3, .ctrB, .cnt, .tmp, .st, .fld, .mA, .mB,
      .cM, .tM, .cX, .tX] ++ Finset.univ.toList.map LayReg.us ++ Finset.univ.toList.map LayReg.sw)
    (by intro r; cases r <;> simp)

inductive CanonicalTerminalReg where
  | router (r : LayReg 6)
  | compiler (r : ElementaryCompilerReg)
  | input (r : SharedInputReg)
  | aux (i : Fin 6)
  deriving Fintype

abbrev canonicalTerminalT := Fintype.card CanonicalTerminalReg

def canonicalTerminalReg : CanonicalTerminalReg → Fin canonicalTerminalT := Fintype.equivFin _

@[simp] theorem canonicalTerminalReg_eq (r s : CanonicalTerminalReg) :
    canonicalTerminalReg r = canonicalTerminalReg s ↔ r = s := (Fintype.equivFin _).injective.eq_iff

def canonicalTerminalRouter (r : LayReg 6) := canonicalTerminalReg (.router r)
def canonicalTerminalCompiler (r : ElementaryCompilerReg) := canonicalTerminalReg (.compiler r)
def canonicalTerminalInput (r : SharedInputReg) := canonicalTerminalReg (.input r)
def canonicalTerminalAux (i : Fin 6) := canonicalTerminalReg (.aux i)

theorem canonicalTerminalRouter_injective : Function.Injective canonicalTerminalRouter := by
  intro r s h
  simpa only [canonicalTerminalRouter, canonicalTerminalReg_eq, CanonicalTerminalReg.router.injEq] using h

theorem canonicalTerminalCompiler_injective : Function.Injective canonicalTerminalCompiler := by
  intro r s h
  simpa only [canonicalTerminalCompiler, canonicalTerminalReg_eq, CanonicalTerminalReg.compiler.injEq] using h

theorem canonicalTerminalInput_injective : Function.Injective canonicalTerminalInput := by
  intro r s h
  simpa only [canonicalTerminalInput, canonicalTerminalReg_eq, CanonicalTerminalReg.input.injEq] using h

theorem canonicalTerminalT_fit : IntegerMultBounds.MathlibTM2.Host.swapT 6 ≤ canonicalTerminalT := by
  have hinj : Function.Injective (fun j => canonicalTerminalReg (.router (.sw j))) := by
    intro i j h
    have he := (canonicalTerminalReg_eq _ _).mp h
    cases he
    rfl
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ hinj


theorem canonicalTerminalShared_regs (wb wm B M : ℕ) (key : Fin 4) :
    [(elementarySharedJob canonicalTerminalRouter (sharedInputConfig canonicalTerminalInput) wb wm B M key).src,
      elementarySharedTarget canonicalTerminalRouter key, canonicalTerminalAux 3,
      canonicalTerminalAux 4, canonicalTerminalAux 5].Nodup := by
  fin_cases key <;>
    simp [elementarySharedJob, elementarySharedTarget, sharedInputConfig, canonicalTerminalRouter,
      canonicalTerminalInput, canonicalTerminalAux, MetadataJob.src]

theorem canonicalTerminalShared_sources (wb wm B M : ℕ) (key other : Fin 4) :
    (elementarySharedJob canonicalTerminalRouter (sharedInputConfig canonicalTerminalInput) wb wm B M key).src ≠
      elementarySharedTarget canonicalTerminalRouter other := by
  fin_cases key <;> fin_cases other <;>
    simp [elementarySharedJob, elementarySharedTarget, sharedInputConfig, canonicalTerminalRouter,
      canonicalTerminalInput, MetadataJob.src]


@[simp] theorem canonicalTerminalBank_fixed_compiler {A : ℕ} (stream coordinates : List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) (c : ElementaryCompilerReg) :
    canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits (canonicalTerminalCompiler c) =
        elementaryCompilerInputWords n L Lb B rowBits c := by
  apply canonicalTerminalBank_compiler _ _ canonicalTerminalCompiler_injective
  intro c r
  simp [canonicalTerminalCompiler, canonicalTerminalInput]

@[simp] theorem canonicalTerminalBank_fixed_input {A : ℕ} (stream coordinates : List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) (r : SharedInputReg) :
    canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits (canonicalTerminalInput r) =
        sharedInputInitialWords L n Lb B rowBits r :=
  canonicalTerminalBank_input _ _ canonicalTerminalInput_injective _ _ _ _ _ _ r

@[simp] theorem canonicalTerminalBank_fixed_router {A : ℕ} (stream coordinates : List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) (r : LayReg 6) :
    canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits (canonicalTerminalRouter r) =
        if canonicalTerminalRouter r = canonicalTerminalRouter .str then stream else [] := by
  apply canonicalTerminalRoutingBank_router
  · intro c r; simp [canonicalTerminalCompiler, canonicalTerminalRouter]
  · intro i r; simp [canonicalTerminalInput, canonicalTerminalRouter]
  · intro r; simp [canonicalTerminalAux, canonicalTerminalRouter]

@[simp] theorem canonicalTerminalBank_fixed_aux {A : ℕ} (stream coordinates : List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) (i : Fin 6) :
    canonicalTerminalRoutingBank canonicalTerminalRouter canonicalTerminalCompiler canonicalTerminalInput
      (canonicalTerminalAux 0) stream coordinates n L Lb B rowBits (canonicalTerminalAux i) =
        if i = 0 then coordinates else [] := by
  unfold canonicalTerminalRoutingBank
  rw [canonicalTerminalBank_off]
  · simp [canonicalTerminalRawBank, canonicalTerminalAux, canonicalTerminalRouter]
  · intro c; simp [canonicalTerminalCompiler, canonicalTerminalAux]
  · intro r; simp [canonicalTerminalInput, canonicalTerminalAux]

end
end IntegerMultBounds.MathlibTM2.Routing
