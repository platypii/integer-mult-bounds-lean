module

public import IntegerMultBounds.MathlibTM2.Routing.ElementaryCompileLoopData
public import IntegerMultBounds.MathlibTM2.Routing.SharedInputExec

/-! One compatible operand bank for the existing terminal compiler and shared
counter generator. Both use binary dimensions and blank private workspace. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Routing
open IntegerMultBounds.MathlibTM2.Host IntegerMultBounds.MathlibTM2.Fast
noncomputable section
variable {T A : ℕ}

def canonicalTerminalBank (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :=
  sharedInputInitialBank input (elementaryCompilerInputBank compiler outside n L Lb B rowBits)
    L n Lb B rowBits

theorem canonicalTerminalBank_compiler (compiler : ElementaryCompilerReg → Fin T)
    (input : SharedInputReg → Fin T) (hc : Function.Injective compiler)
    (hsep : ∀ c r, compiler c ≠ input r)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) (c : ElementaryCompilerReg) :
    canonicalTerminalBank compiler input outside n L Lb B rowBits (compiler c) =
      elementaryCompilerInputWords n L Lb B rowBits c := by
  unfold canonicalTerminalBank
  rw [sharedInputInitialBank_off _ _ _ _ _ _ _ _ (fun r => (hsep c r).symm)]
  exact hc.extend_apply _ _ c

theorem canonicalTerminalBank_input (compiler : ElementaryCompilerReg → Fin T)
    (input : SharedInputReg → Fin T) (hi : Function.Injective input)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) (r : SharedInputReg) :
    canonicalTerminalBank compiler input outside n L Lb B rowBits (input r) =
      sharedInputInitialWords L n Lb B rowBits r := hi.extend_apply _ _ r

theorem canonicalTerminalBank_off (compiler : ElementaryCompilerReg → Fin T)
    (input : SharedInputReg → Fin T) (outside : Fin T → List (Fin (A + 4)))
    (n L Lb B : ℕ) (rowBits : List Bool) (j : Fin T)
    (hc : ∀ c, compiler c ≠ j) (hi : ∀ r, input r ≠ j) :
    canonicalTerminalBank compiler input outside n L Lb B rowBits j = outside j := by
  unfold canonicalTerminalBank
  rw [sharedInputInitialBank_off _ _ _ _ _ _ _ _ hi,
    elementaryCompilerInputBank_off _ _ _ _ _ _ _ _ hc]

theorem canonicalTerminalBank_ready (compiler : ElementaryCompilerReg → Fin T)
    (input : SharedInputReg → Fin T) (hc : Function.Injective compiler)
    (hsep : ∀ c r, compiler c ≠ input r)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :
    ElementaryCompileReady compiler (canonicalTerminalBank compiler input outside n L Lb B rowBits)
      n L Lb B rowBits := by
  apply (elementaryCompilerInputBank_ready compiler hc outside n L Lb B rowBits).congr
  intro c _
  rw [canonicalTerminalBank_compiler compiler input hc hsep]
  exact (hc.extend_apply _ _ c).symm


/-- The actual generated counter bank remains ready for terminal compilation. -/
theorem canonicalTerminalBank_generated_ready (compiler : ElementaryCompilerReg → Fin T)
    (input : SharedInputReg → Fin T) (hc : Function.Injective compiler)
    (hsep : ∀ c r, compiler c ≠ input r)
    (outside : Fin T → List (Fin (A + 4))) (n L Lb B rows : ℕ) (rowBits : List Bool) :
    ElementaryCompileReady compiler
      (sharedInputBank (canonicalTerminalBank compiler input outside n L Lb B rowBits)
        input n rows rowBits.length) n L Lb B rowBits := by
  apply (canonicalTerminalBank_ready compiler input hc hsep outside n L Lb B rowBits).congr
  intro c _
  apply sharedInputBank_keep
  simp only [sharedInputPrivate, List.mem_cons, List.not_mem_nil, or_false, not_or]
  exact ⟨hsep c .records, hsep c .field, hsep c .mask⟩


/-- The raw terminal bank carries only the records and physical coordinate table. -/
def canonicalTerminalRawBank (str src : Fin T) (stream coordinates : List (Fin (A + 4)))
    (j : Fin T) : List (Fin (A + 4)) :=
  if j = src then coordinates else if j = str then stream else []

def canonicalTerminalRoutingBank {t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (src : Fin T) (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :=
  canonicalTerminalBank compiler input (canonicalTerminalRawBank (rg .str) src stream coordinates)
    n L Lb B rowBits

/-- Every router register except the record stream starts blank, even after
installing all compiler and counter operands. -/
theorem canonicalTerminalRoutingBank_router {t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (hcompiler : ∀ c r, compiler c ≠ rg r) (hinput : ∀ i r, input i ≠ rg r)
    (src : Fin T) (hsrc : ∀ r, src ≠ rg r)
    (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) (r : LayReg t₀) :
    canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits (rg r) =
      if rg r = rg .str then stream else [] := by
  unfold canonicalTerminalRoutingBank
  rw [canonicalTerminalBank_off _ _ _ _ _ _ _ _ _ (fun c => hcompiler c r) (fun i => hinput i r)]
  simp only [canonicalTerminalRawBank, ite_eq_right (hsrc r).symm]

theorem canonicalTerminalRoutingBank_blank {t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (hrg : Function.Injective rg)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (hcompiler : ∀ c r, compiler c ≠ rg r) (hinput : ∀ i r, input i ≠ rg r)
    (src : Fin T) (hsrc : ∀ r, src ≠ rg r)
    (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool)
    (r : LayReg t₀) (hr : r ≠ .str) :
    canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits (rg r) = [] := by
  rw [canonicalTerminalRoutingBank_router rg compiler input hcompiler hinput src hsrc]
  exact ite_eq_right (hrg.ne hr)


theorem canonicalTerminalRoutingBank_coordinates {t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (src : Fin T) (hcompiler : ∀ c, compiler c ≠ src) (hinput : ∀ i, input i ≠ src)
    (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :
    canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits src = coordinates := by
  unfold canonicalTerminalRoutingBank
  rw [canonicalTerminalBank_off _ _ _ _ _ _ _ _ _ hcompiler hinput]
  simp only [canonicalTerminalRawBank, ite_true]

theorem canonicalTerminalRoutingBank_stream {t₀ : ℕ} (rg : LayReg t₀ → Fin T)
    (compiler : ElementaryCompilerReg → Fin T) (input : SharedInputReg → Fin T)
    (hcompiler : ∀ c r, compiler c ≠ rg r) (hinput : ∀ i r, input i ≠ rg r)
    (src : Fin T) (hsrc : ∀ r, src ≠ rg r)
    (stream coordinates : List (Fin (A + 4))) (n L Lb B : ℕ) (rowBits : List Bool) :
    canonicalTerminalRoutingBank rg compiler input src stream coordinates n L Lb B rowBits (rg .str) = stream := by
  rw [canonicalTerminalRoutingBank_router rg compiler input hcompiler hinput src hsrc]
  simp only [ite_true]

end
end IntegerMultBounds.MathlibTM2.Routing
