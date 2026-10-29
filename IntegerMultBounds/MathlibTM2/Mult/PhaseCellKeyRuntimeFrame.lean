module

public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellInstallKeyRuntime
public import IntegerMultBounds.MathlibTM2.Mult.PhaseCellOuterHeaders

/-! The generated private operands disappear when their retained caller copies
are installed. This frame is independent of the key-generation computation. -/

@[expose] public section
namespace IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement

open IntegerMultBounds IntegerMultBounds.Machine IntegerMultBounds.MathlibTM2
  IntegerMultBounds.MathlibTM2.Stack IntegerMultBounds.MathlibTM2.Host
  IntegerMultBounds.MathlibTM2.Node IntegerMultBounds.MathlibTM2.Mult.ShortConv

def generatedKeyRuntimeR {A : ℕ} (R : Regs 144 A) (V w K : ℕ)
    (keys : List (Fin (A+4))) : Regs 144 A :=
  Function.update (Function.update (Function.update (Function.update R
    94 (List.replicate w tick)) 115 (List.replicate V tick)) 87 keys)
    86 (List.replicate K tick)

def initializedKeyRuntimeR {T A : ℕ} [NeZero T] (R : Regs T A) (V w K : ℕ)
    (keys : List (Fin (A+4))) : Regs T A :=
  Function.update (Function.update (Function.update (Function.update R
    125 (List.replicate V tick)) 126 (keys++R 126)) 127 (List.replicate K tick))
    130 (List.replicate w tick)

theorem installed_generatedKeyRuntimeR {A : ℕ} (R : Regs 144 A) (V w K : ℕ)
    (keys : List (Fin (A+4)))
    (hblank : ∀ k ∈ [(86 : Fin 144),87,94,115], R k = []) :
    installedKeyRuntimeR (generatedKeyRuntimeR R V w K keys) V w K keys =
      initializedKeyRuntimeR R V w K keys := by
  funext k
  by_cases h86 : k = 86
  · subst k; simp [installedKeyRuntimeR,initializedKeyRuntimeR,hblank 86 (by simp)]
  by_cases h87 : k = 87
  · subst k; simp [installedKeyRuntimeR,initializedKeyRuntimeR,hblank 87 (by simp)]
  by_cases h94 : k = 94
  · subst k; simp [installedKeyRuntimeR,initializedKeyRuntimeR,hblank 94 (by simp)]
  by_cases h115 : k = 115
  · subst k; simp [installedKeyRuntimeR,initializedKeyRuntimeR,hblank 115 (by simp)]
  simp [installedKeyRuntimeR,generatedKeyRuntimeR,initializedKeyRuntimeR,
    Function.update_apply,h86,h87,h94,h115]

theorem initializedKeyRuntimeR_private {A : ℕ} (R : Regs 144 A) (V w K : ℕ)
    (keys : List (Fin (A+4))) (k : Fin 144) (hk : k.val < 117) :
    initializedKeyRuntimeR R V w K keys k = R k := by
  have h125 : k ≠ 125 := by intro h; subst k; contradiction
  have h126 : k ≠ 126 := by intro h; subst k; contradiction
  have h127 : k ≠ 127 := by intro h; subst k; contradiction
  have h130 : k ≠ 130 := by intro h; subst k; contradiction
  simp [initializedKeyRuntimeR,h125,h126,h127,h130]

theorem initializedKeyRuntimeR_copiedGroupR {A : ℕ} (R : Regs 144 A)
    (P N q l s t u band L V w K : ℕ) (keys : List (Fin (A+4))) :
    initializedKeyRuntimeR (copiedGroupR P N q l s t u band L R) V w K keys =
      copiedGroupR P N q l s t u band L (initializedKeyRuntimeR R V w K keys) := by
  funext k
  by_cases hk : 117 ≤ k.val
  · rw [copiedGroupR_off _ _ _ _ _ _ _ _ _ _ _ hk]
    simp [initializedKeyRuntimeR,Function.update_apply,
      copiedGroupR_off P N q l s t u band L R k hk,
      copiedGroupR_off P N q l s t u band L R 126 (by decide)]
  · have hlo : k.val < 117 := by omega
    rw [initializedKeyRuntimeR_private _ _ _ _ _ _ hlo]
    apply unaryCopiesR_congr_base
    · intro r hr
      have hrlo : r.2.val < 117 := by
        simp only [groupHeaderCopies,List.mem_cons,List.not_mem_nil,or_false] at hr
        rcases hr with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide
      exact (initializedKeyRuntimeR_private R V w K keys r.2 hrlo).symm
    · exact (initializedKeyRuntimeR_private R V w K keys k hlo).symm

end IntegerMultBounds.MathlibTM2.Mult.PhaseCellToeplitz.ScalarPlacement
